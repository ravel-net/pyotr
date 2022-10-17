from copy import deepcopy
from curses.ascii import isdigit
import re
import sys
from os.path import dirname, abspath
from turtle import right
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)

from Core.Homomorphism.faure_translator.attribute import SelectedAttribute
import databaseconfig as cfg
import psycopg2 
conn = psycopg2.connect(
    host=cfg.postgres["host"], 
    database=cfg.postgres["db"], 
    user=cfg.postgres["user"], 
    password=cfg.postgres["password"])

class SQL_Parser:
    """
    
    Parameters:
    -----------
    sql: 
        SQL str. Now only supports selection.

    databases:
        all columns are default int4_faure datatype except for condition column.
        format: {"tablename": {"types": list[datatypes], "names": list[attribute_names]}} 
        require to include 'condition' column and datatype of 'condition' column
    
    """
    _ARRAY_OPERATORS = ["||", "@>", "<@"]
    _ARITHMATIC_OPERATORS = ['+', '-', '/', '*']
    _FAURE_DATATYPE = ['int4_faure', 'inet_faure']
    
    def __init__(self, sql, reasoning_engine='z3', databases={}):
        self._original_sql = sql
        self._reasoning_engine=reasoning_engine
        self.databases = {}
        for table in databases:
            table_lower = table.lower()
            self.databases[table_lower] = {'types': [], 'names': []}
            for i in range(len(databases[table]['names'])):
                self.databases[table_lower]['types'].append(databases[table]['types'][i].lower()) 
                self.databases[table_lower]['names'].append(databases[table]['names'][i].lower()) 

        self.type = None # 1: select, 2: insert, 3: delete
        self._selected_attributes = {'is_star': False, 'attributes': []}
        self.working_tables = []

        # self._constraints_in_where_clause = []
        self._position_subclause_mapping_dict = {} # for complex where clause
        # self._where_clause_with_subclause_pos = None # e.g., <0> or <3> and b = 1

        sql_lowercase = sql.strip(';').lower()
        self._all_attributes = {} # {'tablename':list[attributes], 'condition': list[attributes]}

        self.simple_attr2column_name_mapping = {}
        self.simple_attr2datatype_mapping = {}

        if sql.lower().startswith('select'):
            self.type = 1

            from_pattern_may_include_where = re.compile(r'from(.*)', re.S)
            from_clause_include_where_str = re.findall(from_pattern_may_include_where, sql_lowercase)[0].strip()

            if 'where' in from_clause_include_where_str:
                parts = from_clause_include_where_str.split('where')
                working_tables_str = parts[0].strip()
                self._processworking_tables_str(working_tables_str)
                

                where_index = sql_lowercase.find('where')
                where_clause_str = self._original_sql[where_index+5:]

                self._process_where_clause(where_clause_str)
            else:
                self._processworking_tables_str(from_clause_include_where_str)

            self._get_all_attributes()
            # print("self._all_attributes", self._all_attributes)
            selected_attributes_pattern = re.compile(r'select(.*?)from', re.S)
            selected_attributes_str = re.findall(selected_attributes_pattern, sql_lowercase)[0].strip()
            self._process_select_clause(selected_attributes_str)
            
            
        else:
            print("We only support selection now! Sorry!")
            exit()
        
        self.equal_attributes_from_where_clause = {} # equal attributes according to the constraints in the where clause, e.g., t1 = t2 and t2 = t3, then t1, t2 and t3 are equal attributes, {'t1':[t2, t3]}
        # self._get_equal_variables_in_constraints() # get values of above parameter

        self.simple_attribute_mapping = {} # t0.c1(AttributePart) maps to SelectedAttribute("t0.c1")
        self._get_simple_attribute_mapping()
        
        self.drop_columns = [] 
        self._get_drop_columns()

        
    @property
    def execution_sql(self):
        if self.type == 1:
            print("type", self.type)
            attributes_strs = []
            if self._selected_attributes['is_star']:
                for key in self._all_attributes:
                    if key == 'condition':
                        if self._reasoning_engine == 'z3':
                            attr_strs = []
                            for attr in self._all_attributes[key]:
                                attr_strs.append(str(attr))
                            attributes_strs.append("{} as condition".format(" || ".join(attr_strs)))
                        elif self._reasoning_engine.lower() == 'bdd':
                            for attr in self._all_attributes[key]:
                                attributes_strs.append(str(attr))
                    else:
                        for attr in self._all_attributes[key]:
                            attributes_strs.append(str(attr))
            else:
                for key in self._selected_attributes['attributes']:
                    attributes_strs.append(str(key))
                    
                # attr_strs = []
                # for attr in self._all_attributes['condition']:
                #     attr_strs.append(str(attr))
                # attributes_strs.append("{} as condition".format(" || ".join(attr_strs)))

                for key in self._all_attributes:
                    if key == 'condition':
                        if self._reasoning_engine == 'z3':
                            attr_strs = []
                            for attr in self._all_attributes[key]:
                                attr_strs.append(str(attr))
                            attributes_strs.append("{} as condition".format(" || ".join(attr_strs)))
                        elif self._reasoning_engine.lower() == 'bdd':
                            for attr in self._all_attributes[key]:
                                attributes_strs.append(str(attr))
                    else:
                        for attr in self._all_attributes[key]:
                            attributes_strs.append(str(attr))

            table_strs = []
            for table in self.working_tables:
                table_strs.append(str(table))

            sql = ""
            if len(self._position_subclause_mapping_dict) == 0:
                sql = "select {} from {}".format(", ".join(attributes_strs), ", ".join(table_strs))
            else:
                root_clause = self._position_subclause_mapping_dict['root']
                where_str = self._convert_subclause_to_SQL(root_clause)
                if where_str.startswith('(') and where_str.endswith(')'):
                    where_str = where_str[1:-1]
                sql = "select {} from {} where {}".format(", ".join(attributes_strs), ", ".join(table_strs), where_str)
            # for value in self._constraints_in_where_clause:
            #     if type(value) == list:
            #         temp_str = []
            #         for val in value:
            #             temp_str.append(str(val))
            #         where_strs.append("({})".format(' or '.join(temp_str)))
            #     else:
            #         where_strs.append(str(value))
            # print("where_strs", where_strs)
            
            # if len(where_strs) != 0:
            #     sql = "select {} from {} where {}".format(", ".join(attributes_strs), ", ".join(table_strs), " and ".join(where_strs))
            # else:
            #     sql = "select {} from {}".format(", ".join(attributes_strs), ", ".join(table_strs))
            return sql
        else:
            return None

    @property
    def sql(self):
        return self._original_sql
    
    @property
    def additional_conditions_SQL_format(self):
        # # TODO: update conjunction condition for condition column
        # # require SQL format, e.g., ARRAY[t1.c0, "Or(" || t1.c2 ", " || t1.c3 || ")", ... ]
        # conditions = []
        # for constraint in self._constraints_in_where_clause:
        #     if type(constraint) == list: # a list of conditions connnected by logical OR
        #         temp_conditions = []
        #         for cond in constraint:
        #             # print(cond)
        #             # print(cond.concatenation)
                    
        #             temp_conditions.append(cond.concatenation(self.simple_attribute_mapping, self.simple_attr2datatype_mapping))
        #         conditions.append("'Or(' || {} || ')'".format(", ".join(temp_conditions)))
        #     else:
        #         # print(type(constraint))
        #         # print(constraint.concatenation)
        #         # print(str(constraint))
        #         contained = self._if_operands_contains_faure_datatype(constraint)
        #         # print("contained", contained)
        #         if contained:
        #             conditions.append(constraint.concatenation(self.simple_attribute_mapping))
        # if len(conditions) == 0:
        #     return None
        # conjunction_conditions = "Array[{}]".format(", ".join(conditions))
        # return conjunction_conditions
        if len(self._position_subclause_mapping_dict) == 0:
            return None
        else:
            root_clause = self._position_subclause_mapping_dict['root']
            return self._convert_subclause_to_Z3format(root_clause)

    @property
    def old_conditions_attributes_BDD(self):
        old_conditions_attributes = []
        for attr in self._all_attributes['condition']:
            old_conditions_attributes.append(attr.AttributeName)
        return old_conditions_attributes

    def _processworking_tables_str(self, working_tables_str):
        for workingtable in working_tables_str.split(','):
            workingtable = workingtable.strip()
            self.working_tables.append(WorkingTable(workingtable))

    def _process_select_clause(self, selected_attributes_str):
        if selected_attributes_str == '*':
            self._selected_attributes['is_star'] = True
        else:
            i = 0
            begin_pos = i
            in_square_parenth = 0 # for array[a1, ...]
            while i < len(selected_attributes_str):
                if selected_attributes_str[i] == '[':
                    in_square_parenth += 1
                elif selected_attributes_str[i] == ']':
                    in_square_parenth -= 1
                elif selected_attributes_str[i] == ',':
                    if in_square_parenth == 0: 
                        attribute = selected_attributes_str[begin_pos:i]
                        self._selected_attributes['attributes'].append(SelectedAttribute(attribute))
                        begin_pos = i+1
            
                i += 1
            
            if begin_pos != i:
                attribute = selected_attributes_str[begin_pos:i]
                self._selected_attributes['attributes'].append(SelectedAttribute(attribute))

    def _get_all_attributes(self):
        condition_attributes = []

        for workingtable in self.working_tables:
            column_names = []
            column_datatypes = []
            if workingtable.table in self.databases:
                column_names = self.databases[workingtable.table]['names']
                column_datatypes = self.databases[workingtable.table]['types']
            else:
                self.databases[workingtable.table] = {'types':[], 'names':[]}
                cursor = conn.cursor()
                cursor.execute("SELECT column_name, data_type FROM information_schema.columns WHERE table_name = '{}';".format(workingtable.table))
                for (column_name, datatype) in cursor.fetchall():
                    self.databases[workingtable.table]['types'].append(datatype.lower())
                    self.databases[workingtable.table]['names'].append(column_name.lower())

                conn.commit()
                column_names = self.databases[workingtable.table]['names']
                column_datatypes = self.databases[workingtable.table]['types']
            
            for idx, attr_name in enumerate(column_names):
                attribute_str = None
                if workingtable.has_alias:
                    attribute_str = "{tab_alias}.{attr} as {tab_alias}_{attr}".format(tab_alias=workingtable.alias, attr=attr_name)
                else:
                    if len(self.working_tables) == 1:
                        attribute_str = "{attr}".format(attr=attr_name)
                    else:
                        attribute_str = "{tab}.{attr} as {tab}_{attr}".format(tab=workingtable.table, attr=attr_name)
                if attr_name == 'condition':
                    if self._reasoning_engine == 'z3':
                        condition_attributes.append(SelectedAttribute(attribute_str.split(" as ")[0].strip()))
                    elif self._reasoning_engine == 'bdd':
                        condition_attributes.append(SelectedAttribute(attribute_str))
                else:
                    if workingtable.table not in self._all_attributes:
                        self._all_attributes[workingtable.table] = []
                    selected_attribute = SelectedAttribute(attribute_str)
                    self._all_attributes[workingtable.table].append(selected_attribute)

                    self.simple_attr2datatype_mapping[selected_attribute.AttributePart] = column_datatypes[idx]
                    self.simple_attr2column_name_mapping[selected_attribute.AttributePart] = attr_name
        self._all_attributes['condition'] = condition_attributes

    def _process_where_clause(self, where_caluse_str):
        """
        Assume single parenthesis
        a = 1 and a != 2 and (c = 1 or c = 2 ) and d = any(p) and not d = any(p)
        """
        self._split_subclause_in_where_clause(where_caluse_str)
        
        # for constraint in constraints:
        #     if constraint.startswith('(') and constraint.endswith(')'):
        #         temp_conditions = []
        #         conditions = constraint.split("or")
        #         for condition in conditions:
        #             temp_conditions.append(Constraint(condition))
        #         self._constraints_in_where_clause.append(deepcopy(temp_conditions))
        #     else:
        #         self._constraints_in_where_clause.append(Constraint(constraint))

        for pos in self._position_subclause_mapping_dict.keys():
            disjunction_condition_list = self._process_subclause(self._position_subclause_mapping_dict[pos])
            self._position_subclause_mapping_dict[pos] = disjunction_condition_list
        
        # print("self._position_subclause_mapping_dict", self._position_subclause_mapping_dict)

    def _process_subclause(self, subclause):
        disjunction_conditions = re.split('or', subclause, flags=re.IGNORECASE)
        # print(or_conditions)

        disjunction_condition_list = []
        for cond in disjunction_conditions:
            atoms = re.split('and', cond, flags=re.IGNORECASE )
            conjunction_condition_list = []
            for atom in atoms:
                atom = atom.strip()
                if atom.startswith('<') and atom.endswith('>'):
                    conjunction_condition_list.append(int(atom.lstrip('<').rstrip('>'))) # pos_idx
                else:
                    conjunction_condition_list.append(Constraint(atom)) # atom constraint
            disjunction_condition_list.append(conjunction_condition_list)
        
        # print("disjunction_condition_list", disjunction_condition_list)
        return disjunction_condition_list
    
    def _split_subclause_in_where_clause(self, where_clause_str):
        position_subclause_mapping_dict = {}
        id_num = 0
        stack = []
        new_clause = None
        i = 0
        skip_closed_parenth_num = 0
        while i < len(where_clause_str):
            # print(where_clause_str[i])
            if where_clause_str[i] == '(':
                if i > 0 and where_clause_str[i-1].isalpha():
                    skip_closed_parenth_num += 1
                else:
                    stack.append(i)

                # print("left_parenth_position", left_parenth_position)
            elif where_clause_str[i] == ')':
                if skip_closed_parenth_num != 0:
                    skip_closed_parenth_num -= 1
                else:
                    left_parenth_position = stack.pop()
                    block = where_clause_str[left_parenth_position + 1 : i]
                    pos = '<{}>'.format(id_num)
                    new_clause = where_clause_str[:left_parenth_position] + pos + where_clause_str[i+1:]
                    where_clause_str = new_clause
                    # update i to the first position after <id_num>
                    i = left_parenth_position + len(pos) - 1

                    position_subclause_mapping_dict[id_num] = block
                    id_num += 1
                    continue
            i += 1
        
        position_subclause_mapping_dict['root'] = where_clause_str
        # print("position_subclause_mapping_dict", position_subclause_mapping_dict)
        # print("where_clause_str", where_clause_str)
        # return position_subclause_mapping_dict
        self._position_subclause_mapping_dict = position_subclause_mapping_dict
        # self._where_clause_with_subclause_pos = where_clause_str

    def _convert_subclause_to_SQL(self, clause):
        # root_clause = self._position_subclause_mapping_dict['root']

        disjunction_strs = []
        for conjunction_list in clause:
            conjunction_strs = []
            for atom in conjunction_list:
                if isinstance(atom, Constraint):
                    conjunction_strs.append(str(atom))
                else:
                    sub_clause = self._position_subclause_mapping_dict[atom]
                    conjunction_strs.append(self._convert_subclause_to_SQL(sub_clause))
            if len(conjunction_strs) == 1:
                disjunction_strs.append(conjunction_strs[0])
            else:
                disjunction_strs.append('({})'.format(' and '.join(conjunction_strs)))
        
        if len(disjunction_strs) == 1:
            return disjunction_strs[0]
        else:
            return "({})".format(' or '.join(disjunction_strs))
            # return ' or '.join(disjunction_strs)
    
    def _convert_subclause_to_Z3format(self, clause):
        # root_clause = self._position_subclause_mapping_dict['root']

        disjunction_strs = []
        for conjunction_list in clause:
            conjunction_strs = []
            for atom in conjunction_list:
                if isinstance(atom, Constraint):
                    conjunction_strs.append(atom.concatenation(self.simple_attribute_mapping))
                else:
                    sub_clause = self._position_subclause_mapping_dict[atom]
                    conjunction_strs.append(self._convert_subclause_to_Z3format(sub_clause))
            if len(conjunction_strs) == 1:
                disjunction_strs.append(conjunction_strs[0])
            else:
                disjunction_strs.append("'And(' || {} || ')'".format(" || ', ' || ".join(conjunction_strs)))
        
        if len(disjunction_strs) == 1:
            return disjunction_strs[0]
        else:
            return "'Or(' || {} || ')'".format(" || ', ' || ".join(disjunction_strs))

    def _get_equal_variables_in_constraints(self):

        temp_dict = {}
        for constraint in self._constraints_in_where_clause:
            if type(constraint) == list:
                continue
            else:
                if constraint.negation:
                    continue
                elif constraint._left_operand['function'] is not None or  constraint._right_operand['function'] is not None:
                    continue
                elif str(constraint._left_operand["attribute"]).strip("'")[0].isdigit() or str(constraint._right_operand["attribute"]).strip("'")[0].isdigit():
                    continue
                elif constraint._operator == '=':
                    left_opd = str(constraint._left_operand["attribute"])
                    right_opd = str(constraint._right_operand["attribute"])

                    if left_opd not in temp_dict and right_opd not in temp_dict:
                        temp_dict[left_opd] = [right_opd]
                        temp_dict[right_opd] = left_opd
                    elif left_opd in temp_dict and right_opd not in temp_dict:
                        if type(temp_dict[left_opd]) == list:
                            temp_dict[left_opd].append(right_opd)
                            temp_dict[right_opd] = left_opd
                        else:
                            idx = temp_dict[left_opd]
                            temp_dict[idx].append(right_opd)
                            temp_dict[right_opd] = idx
                    elif left_opd not in temp_dict and right_opd in temp_dict:
                        if type(temp_dict[right_opd]) == list:
                            temp_dict[right_opd].append(left_opd)
                            temp_dict[left_opd] = right_opd
                        else:
                            idx = temp_dict[right_opd]
                            temp_dict[idx].append(left_opd)
                            temp_dict[left_opd] = idx
                    else:
                        if type(temp_dict[left_opd]) == list and type(temp_dict[right_opd]) == list :
                            temp_dict[left_opd] += temp_dict[right_opd]
                            temp_dict[left_opd].append(right_opd)
                            temp_dict[right_opd] = left_opd
                        elif type(temp_dict[left_opd]) == list and type(temp_dict[right_opd]) != list:
                            idx = temp_dict[right_opd]
                            temp_dict[idx] += temp_dict[left_opd]
                            temp_dict[idx].append(left_opd)
                            temp_dict[left_opd] = idx
                        elif type(temp_dict[left_opd]) != list and type(temp_dict[right_opd]) == list:
                            idx = temp_dict[left_opd]
                            temp_dict[idx] += temp_dict[right_opd]
                            temp_dict[idx].append(right_opd)
                            temp_dict[right_opd] = idx
        
        for simp_attr in temp_dict:
            if type(temp_dict[simp_attr]) == list:
                self.equal_attributes_from_where_clause[simp_attr] = temp_dict[simp_attr]
    
    def _get_simple_attr2datatype_mapping(self):
        print(self.simple_attribute_mapping.keys())
        for table in self._all_attributes:
            if table == 'condition':
                pass
            else:
                print(table)
                for idx, attribute in enumerate(self._all_attributes[table]):
                    print(str(attribute))
                    print(idx)
                    self.simple_attr2column_name_mapping[attribute.AttributePart] = self.databases[table]['names'][idx]
                    self.simple_attr2datatype_mapping[attribute.AttributePart] = self.databases[table]['types'][idx]
        
    def _get_simple_attribute_mapping(self):
        simple_attr_mapping = {}
        if not self._selected_attributes['is_star']:
            for attribute in self._selected_attributes['attributes']:
                if attribute.AttributePart not in simple_attr_mapping:
                    simple_attr_mapping[attribute.AttributePart] = attribute
        
        # print("self._all_attributes", self._all_attributes)
        for table in self._all_attributes:
            if table == 'condition': # 'condition' is not a table but a column
                continue
            for attribute in self._all_attributes[table]:
                if attribute.AttributePart not in simple_attr_mapping:
                    simple_attr_mapping[attribute.AttributePart] = attribute

        self.simple_attribute_mapping = simple_attr_mapping

    def _get_drop_columns(self):
        
        drop_columns = []
        if self._selected_attributes['is_star']:
            # drop duplicated columns
            for attr in self.equal_attributes_from_where_clause:
                for col in self.equal_attributes_from_where_clause[attr]:

                    drop_columns.append(self.simple_attribute_mapping[col].AttributeName)

            if self._reasoning_engine.lower() == 'bdd':
                # drop old condition attributes
                for attr in self._all_attributes['condition']:
                    drop_columns.append(attr.AttributeName)


        else:
            for table in self._all_attributes:
                if table == 'condition': 
                    if self._reasoning_engine.lower() == 'bdd':
                        for attr in self._all_attributes['condition']:
                            drop_columns.append(attr.AttributeName)
                    continue
                for attr in self._all_attributes[table]:
                    drop_columns.append(attr.AttributeName)

        self.drop_columns = drop_columns

    def _if_operands_contains_faure_datatype(self, constraint):
        left_attribute = constraint._left_operand['attribute']
        right_attribute = constraint._right_operand['attribute']
        # print(self.simple_attr2datatype_mapping)
        left_simple_attr = left_attribute.AttributePart
        right_simple_attr = right_attribute.AttributePart
        # if left_simple_attr in self.simple_attr2datatype_mapping:  print("left", self.simple_attr2datatype_mapping[left_simple_attr].lower())
        # if right_simple_attr in self.simple_attr2datatype_mapping:  print("right", self.simple_attr2datatype_mapping[right_simple_attr].lower())

        # print("if left_attr is faure_type", left_simple_attr in self.simple_attr2datatype_mapping and \
        #         (self.simple_attr2datatype_mapping[left_simple_attr].lower() in self._FAURE_DATATYPE or \
        #         self.simple_attr2datatype_mapping[left_simple_attr] == 'USER-DEFINED'))
        # if left_simple_attr in self.simple_attr2datatype_mapping:
        #     print(self.simple_attr2datatype_mapping[left_simple_attr])

        # print("if right_attr is faure_type", right_simple_attr in self.simple_attr2datatype_mapping and 
        #         (self.simple_attr2datatype_mapping[right_simple_attr].lower() in self._FAURE_DATATYPE or 
        #         self.simple_attr2datatype_mapping[right_simple_attr].lower() == 'user-defined'))

        # if right_simple_attr in self.simple_attr2datatype_mapping:
        #     print(self.simple_attr2datatype_mapping[right_simple_attr])
        # True only the datatype of attribute is Faure datatype(learn from user input) or USER-DEFINED(learn from database), update it.
        if (left_simple_attr in self.simple_attr2datatype_mapping and \
                (self.simple_attr2datatype_mapping[left_simple_attr].lower() in self._FAURE_DATATYPE or \
                self.simple_attr2datatype_mapping[left_simple_attr].lower() == 'user-defined')) \
            or \
            (right_simple_attr in self.simple_attr2datatype_mapping and 
                (self.simple_attr2datatype_mapping[right_simple_attr].lower() in self._FAURE_DATATYPE or 
                self.simple_attr2datatype_mapping[right_simple_attr].lower() == 'user-defined')) :
            return True
        else:
            return False

class WorkingTable:
    def __init__(self, table_str) -> None:
        self.has_alias = False
        parts = None
        if " as " in table_str:
            self.has_alias = True
            parts = table_str.split(" as ")
        else:
            parts = table_str.split()
            self.has_alias = (len(parts) == 2)

        self.table = parts[0].strip()
        self.alias = None

        if self.has_alias:
            self.alias = parts[1].strip()
    
    @property
    def TableName(self):
        return self.table
    
    def __str__(self) -> str:
        if self.has_alias:
            return "{} {}".format(self.table, self.alias)
        else:
            return self.table

class Constraint:
    def __init__(self, constraint) -> None:
        print("constraint", constraint)
        self.operators = ['!=', '<=', '>=', '=', '<', '>']
        self.negation = False
        
        if constraint.lower().startswith("not"):
            self.negation = True
            constraint = constraint[3:-1]
        self._constraint_str = constraint
        self._contains_function = self._if_contains_function(self._constraint_str)

        self._left_operand = {'function':None, 'attribute':None}
        self._operator = None
        self._right_operand = {'function':None, 'attribute':None}
        print("self._constraint_str", self._constraint_str)
        self._split_constraint()
    
    def concatenation(self, simple_attr_mapping):
        is_array = False

        left_simple_attr = self._left_operand['attribute'].AttributePart
        right_simple_attr = self._right_operand['attribute'].AttributePart

        left_opd = ""
        left_attribute = ""
        
        if left_simple_attr in simple_attr_mapping:
            left_attribute = simple_attr_mapping[left_simple_attr].AttributeName
        else:
            left_attribute = str(self._left_operand['attribute'])
        # print("self._left_operand", self._left_operand)
        if self._left_operand['function'] is None:
            # print(self._left_operand['attribute'])
            left_opd = left_attribute
            # print("left_opd", left_opd)
        else:
            
            left_opd = "'{}('|| {} || ')'".format(self._left_operand['function'], left_attribute)

        right_opd = ""
        right_attribute = ""
        if right_simple_attr in simple_attr_mapping:
            right_attribute = simple_attr_mapping[right_simple_attr].AttributeName
        else:
            right_attribute = right_simple_attr

        if self._right_operand['function'] is None:
            right_opd = right_attribute
        else:
            # ANY() function only locates right operand
            if self._right_operand['function'].lower() == 'any': # assume the attribute is ArrayAttribute
                is_array = True
                right_opd = "{}".format(self._right_operand['attribute'].concatenation(simple_attr_mapping))
            else:
                right_opd = "'{}(' || {} || ')'".format(self._right_operand['function'], right_attribute)
        # print("left", left_opd)
        # print("right", right_opd)
        if self.negation:
            if is_array:
                return "{} || ' \\not_in ' || {}".format(left_opd, right_opd)
            elif self._operator == '=':
                return "'not' || {} || ' == ' || {}".format(left_opd, right_opd)
            else:
                return "'not' || {} || ' {} ' || {}".format(left_opd, self._operator, right_opd)
        else:
            if is_array:
                return "{} || ' \\in ' || {}".format(left_opd, right_opd)
            elif self._operator == '=':
                return "{} || ' == ' || {}".format(left_opd, right_opd)
            else:
                return "{} || ' {} ' || {}".format(left_opd, self._operator, right_opd)

    def __str__(self) -> str:
        left_opd = ""
        # print("self._left_operand", self._left_operand)
        if self._left_operand['function'] is None:
            # print(self._left_operand['attribute'])
            left_opd = str(self._left_operand['attribute'])
            # print("left_opd", left_opd)
        else:
            left_opd = "{}({})".format(self._left_operand['function'], str(self._left_operand['attribute']))
        # print("left_opd", left_opd)
        right_opd = ""
        if self._right_operand['function'] is None:
            right_opd = str(self._right_operand['attribute'])
        else:
            right_opd = "{}({})".format(self._right_operand['function'], str(self._right_operand['attribute']))
        # print("right_opd", right_opd)
        if self.negation:
            return "not {} {} {}".format(left_opd, self._operator, right_opd)
        else:
            return "{} {} {}".format(left_opd, self._operator, right_opd)

        # if "any(" in constraint.lower():
    def _if_contains_function(self, string):
        # print("string", string)
        function_pattern = re.compile(r'([a-zA-Z]+\([^\)]+\))', re.S)
        match = re.search(function_pattern, string)
        if match is not None:
            function_name_pattern = re.compile(r'(.*?)\(.*?\)', re.S)
            function_name = re.findall(function_name_pattern, match.group())[0]
            # print("function_name", function_name)
            return function_name
        
        return None
    
    def _split_constraint(self):
        left_opd = None
        right_opd = None
        # print(self._constraint_str)
        for opr in self.operators:
            if opr in self._constraint_str:
                self._operator = opr
                items = self._constraint_str.split(opr)
                left_opd = items[0].strip()
                right_opd = items[1].strip()
                break
        attribute_pattern = re.compile(r'\((.*?)\)')
        left_match = self._if_contains_function(left_opd)
        if left_match is not None:
            self._left_operand['function'] = left_match

            attribute_str = re.findall(attribute_pattern,  left_opd)[0]
            self._left_operand['attribute'] = SelectedAttribute(attribute_str)
        else:
            self._left_operand['attribute'] = SelectedAttribute(left_opd)
        
        right_match = self._if_contains_function(right_opd)
        if right_match is not None:
            self._right_operand['function'] = right_match

            attribute_str = re.findall(attribute_pattern,  right_opd)[0]
            self._right_operand['attribute'] = SelectedAttribute(attribute_str)
        else:
            self._right_operand['attribute'] = SelectedAttribute(right_opd)

        
        
        

        
        
if __name__ == '__main__':
    # sql = "select t1.c0 as c0, t0.c1 as c1, t0.c2 as c2, ARRAY[t1.c0, t0.c0] as c3, 1 as c4 from R t0, l t1, pod t2, pod t3 where t0.c4 = '0' and t0.c0 = t1.c1 and t0.c1 = t2.c0 and t0.c2 = t3.c0 and t2.c1 = t3.c1 and t0.c0 = ANY(ARRAY[t1.c0, t0.c0])"
    # sql = "select t1.c0 as c0, t0.c1 as c1, ARRAY[t0.c0, t0.c2[1]] as c2, 2 as c3 from R t0, l t1, l t2, l t3 where t0.c3 = '1' and t0.c0 = t1.c1 and t1.c0 = t2.c0 and t2.c0 = t3.c0"
    sql = "SELECT t1.c1 as c0, t0.c1 as c1, ARRAY[t0.c0, t0.c2[1]] as c2, 2 as c3 FROM R t0, l t1 WHERE \
    t0.c3 = any(array[t0.c2]) or ((t0.c3 = '1' and t0.c0 = t1.c0) or (t0.c3 = '1' and t0.c0 != t1.c0) or t1.c0 = '1')"
    p = SQL_Parser(sql, reasoning_engine='z3', databases={
        'pod':{
            'types':['integer', 'int4_faure', 'text[]'], 
            'names':['c0', 'c1', 'condition']
        }, 
        'R':{
            'types':['integer', 'integer','integer[]', 'integer', 'text[]'], 
            'names':['c0', 'c1', 'c2', 'c3', 'condition']
        }, 
        'l':{
            'types':['integer', 'integer', 'text[]'], 
            'names':['c0', 'c1', 'condition']
        }})

    
    # p = SQL_Parser(sql)
    print(p.execution_sql)
    print(p.additional_conditions_SQL_format)

