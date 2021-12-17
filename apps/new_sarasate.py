from ravel.app import AppConsole, mk_watchcmd
import psycopg2
import tabulate
import re
from z3 import *
import time

class SarasateConsole(AppConsole):

    def default(self, line):
        "Execute a PostgreSQL statement"
        try:
            # select_clause, from_clause, defined_where_clause, where_lists = self.pre_processing(line)
            # self.generator(select_clause, from_clause, defined_where_clause, where_lists)
            tree = self.generate_tree(line)
            self.data(tree)
            self.upd_condition(tree)
            self.z3()

        except psycopg2.ProgrammingError as e:
            print(e)
            return

        try:
            self.db.cursor.execute("select * from output;")
            data = self.db.cursor.fetchall()
            if data is not None:
                names = [row[0] for row in self.db.cursor.description]
                print(tabulate.tabulate(data, headers=names))
        except psycopg2.ProgrammingError:
            # no results, eg from an insert/delete
            pass
        except TypeError as e:
            print(e)
    
    def do_data(self, line):
        tree = self.generate_tree(line)
        self.data(tree)
    
    def do_condition(self, line):
        tree = self.generate_tree(line)
        self.upd_condition(tree)
    
    def do_z3(self, line):
        self.z3()
        
    def generate_tree(self, query):
        tree = {}
        # remove ;
        if ';' in query:
            query = query[:-1]
        query_lower = query.lower()
        
        select_pattern = re.compile(r'select(.*?)from', re.S)
        select_clause = re.findall(select_pattern, query_lower)
        tree["select"] = self.process_select_clause(select_clause[0].strip())
        
        from_clause = ""
        from_pattern_may_include_where = re.compile(r'from(.*)', re.S)
        from_clause_may_include_where = re.findall(from_pattern_may_include_where, query_lower)[0].strip()

        '''
        get substring from 'from' keyword to the end
        sql may contain 'where' clause or not
        '''
        if 'where' in from_clause_may_include_where:
            patern = re.compile(r'(.*?)where', re.S)
            from_clause = re.findall(patern, from_clause_may_include_where)[0].strip()
            # detect the location of where
            where_index = query_lower.find('where')
            where_clause = query[where_index+5:]
            tree["where"] = self.process_where_clause(where_clause.strip())
        else:
            from_clause = from_clause_may_include_where
        tree["from"] = self.process_from_clause(from_clause)

        print(tree)
        return tree

    def tree_to_str(self, tree):
        tree_copy = copy.deepcopy(tree)
        sql_parts = []

        select_clause = tree_copy['select']
        select_part = ''
        if '*' in select_clause:
            select_part = '*'
        else:
            for idx, c in enumerate(select_clause):
                c[0] = "".join(c[0])
                if c[1] == 'as':
                    select_clause[idx] = " ".join(c)
                else:
                    select_clause[idx] = "".join(c)
            select_part = ", ".join(select_clause)
        sql_parts.append('select')
        sql_parts.append(select_part)

        from_clause = tree_copy['from']
        for idx, f in enumerate(from_clause):
            if f[1] == '' or f[1] == ' ':
                from_clause[idx] = "".join(f)
            else:
                from_clause[idx] = " ".join(f)
        from_part = ", ".join(from_clause)
        sql_parts.append('from')
        sql_parts.append(from_part)

        if 'where' in tree_copy.keys():
            sql_parts.append('where')
            where_clause = tree_copy['where']
            key = list(where_clause.keys())[0]
            conditions = where_clause[key]
            for idx, f in enumerate(conditions):
                # '''
                # len f = 3, use default operator [left_opd, operator, right_opd]
                # len f = 4, use user-defined function [usr_func, '(', [left_opd, right_opd], ')']
                # '''
                # if len(f) == 3:
                #     f[0] = "".join(f[0])
                #     f[2] = "".join(f[2])
                #     where_clause[key][idx] = " ".join(f)
                # else:
                #     f[2][0] = "".join(f[2][0])
                #     f[2][1] = "".join(f[2][1])
                #     f[2] = ", ".join(f[2])
                #     where_clause[key][idx] = "".join(f)
                f = self.process_opr(f) # operator to user-defined function
                f[2][0] = "".join(f[2][0])
                f[2][1] = "".join(f[2][1])
                f[2] = ", ".join(f[2])
                where_clause[key][idx] = "".join(f)
            where_part = " {} ".format(key).join(where_clause[key])
            sql_parts.append(where_part)

        sql = " ".join(sql_parts)
        # print(sql)
        return sql

    def process_opr(self, cond):
        # if (not cond[0][2].isdigit()) and (not cond[2][2].isdigit()):
        #     usr_func = opr_to_func(cond[1])
        #     return [usr_func, '(', [cond[0], cond[2]], ')']
        usr_func = self.opr_to_func(cond[1])
        return [usr_func, '(', [cond[0], cond[2]], ')']
        # return cond

    def opr_to_func(self, opr):
        if opr == '!=' or opr == '<>':
            return 'not_equal'
        elif opr == '<':
            return 'less'
        elif opr == '>':
            return 'greater'
        elif opr == '<=':
            return 'leq'
        elif opr == '>=':
            return 'geq'
        elif opr == '=':
            return 'equal'
        
    def process_select_clause(self, clause):
        cols = []
        if '*' in clause:
            return "*"
        for col in clause.split(','):
            col = col.strip()

            tuple = [] #[tablename, '.'/'', colname, 'as'/'', renaming_name]
            # whether exits renaming col, keyword is AS or space(omit AS)
            newname_list = ['', '']
            if 'as' in col or ' ' in col:
                items = []
                if 'as' in col:
                    items = col.split('as')
                    newname_list[0] = 'as'
                else:
                    items = col.split(' ')
                    newname_list[0] = ' '
                newname_list[1] = items[1].strip()
                col = items[0].strip()
            
            # whether determine table name
            if '.' in col:
                items = col.split('.')
                tuple = [items[0].strip(), '.', items[1].strip()]
            else:
                tuple = ['', '', col]
            
            t = [tuple]
            t.extend(newname_list) # t --> [[tablename, flag, colname], flag, newcolname]
            cols.append(t)
        
        return cols

    def process_from_clause(self, clause):
        cols = []
        for col in clause.split(','):
            col = col.strip()

            tuple = [''] #[tablename, 'as'/'', renaming_name]
            # whether exits renaming table, keyword is AS or space(omit AS)
            newname_list = ['', '']
            if 'as' in col or ' ' in col:
                items = []
                if 'as' in col:
                    items = col.split('as')
                    newname_list[0] = 'as'
                else:
                    items = col.split(' ')
                    newname_list[0] = ' '
                newname_list[1] = items[1].strip()
                col = items[0].strip()
            
            tuple[0] = col
        
            tuple += newname_list
            cols.append(tuple)
        # cols = [col.strip() for col in clause.split(',')]
        return cols

    def process_where_clause(self, clause):
        cond_list = []
        conditions = re.split('and|or', clause, flags=re.IGNORECASE)
        for c in conditions:
            c = c.strip() 
            match = re.search('!=|<=|>=|<>|<|>|=', c)
            left_opd = c[:match.span()[0]].strip()
            opr = match.group()
            right_opd = c[match.span()[1]:].strip()
            
            # whether specify table's name
            left_opr_list = ['', '', ''] # [tablename, '.'/'', col]
            if '.' in left_opd:
                items = left_opd.split('.')
                left_opr_list[0] = items[0].strip()
                left_opr_list[1] = '.'
                left_opr_list[2] = items[1].strip()
            else:
                left_opr_list[2] = left_opd

            # whether specify table's name
            right_opr_list = ['', '', ''] # [tablename, '.'/'', col]
            if '.' in right_opd:
                items = right_opd.split('.')
                right_opr_list[0] = items[0].strip()
                right_opr_list[1] = '.'
                right_opr_list[2] = items[1].strip()
            else:
                right_opr_list[2] = right_opd
            
            # cond = process_opr([left_opr_list, opr, right_opr_list]) #(left_operand, operator, right_operand)
            cond = [left_opr_list, opr, right_opr_list]
            cond_list.append(cond)
        
        
        match = re.search('and|or', clause, flags=re.IGNORECASE)
        keyword = match.group().lower() if match is not None else ""

        return {keyword:cond_list}

    def test(self, clause, cond_list):
        last = 0 
        i = 0
        while i < len(clause):
            if clause[i] == '(': 
                if i > last:
                    cond_list.append(clause[last:i].strip())
                    temp_list = []
                    j = self.test(clause[i+1:], temp_list)
                    cond_list.append(temp_list)
                    i = i + j + 1
                    last = i
            elif clause[i] == ')':
                if i > last:
                    cond_list.append(clause[last:i].strip())
                return i + 1
            else:
                i = i + 1

    def get_all_columns(self, tables):
        columns = []
        col_conds = []
        # cursor = conn.cursor()
        if len(tables) == 1:
            t = tables[0]
            self.db.cursor.execute("select * from {} limit 1".format(t[0])) # t[0] is tablename
            for col in self.db.cursor.description:
                if t[2] == '': # t[2] is renaming tablename, if t[2] not none, use renaming tablename in column name, else use original tablename in column name
                    columns.append([['', '', col[0]], '', ''])
                else:
                    columns.append([[t[2], '.', col[0]], 'as', '{}_{}'.format(t[2], col[0])])
        else:
            for t in tables:
                self.db.cursor.execute("select * from {} limit 1".format(t[0])) # t[0] is tablename
                for col in self.db.cursor.description:
                    if 'cond' in col[0]:
                        if t[2] == '':
                            col_conds.append("{}.{}".format(t[0], col[0]))
                        else:
                            col_conds.append("{}.{}".format(t[2], col[0]))
                        continue
                    if t[2] == '': # t[2] is renaming tablename, if t[2] not none, use renaming tablename in column name, else use original tablename in column name
                        columns.append([[t[0], '.', col[0]], 'as', '{}_{}'.format(t[0], col[0])])
                    else:
                        columns.append([[t[2], '.', col[0]], 'as', '{}_{}'.format(t[2], col[0])])
            # print(col_conds)
            columns.append([['', '', ' || '.join(col_conds)], 'as', 'condition'])
        # print(columns)
        return columns
                

    #create data content
    def data(self, tree):
        print("\n************************Step 1: create data content****************************")
        # cursor = conn.cursor()
        table_num = len(tree['from'])

        """
        # if the number of table > 1
        # it operates join, no matter it is * or selected columns, extract all columns from all tables
        # if the number of table = 1
        # it may operates selection or projection
        """
        sql = ""
        # if table_num > 1: 
        #     columns = get_all_columns(tree['from'])
        #     new_tree = copy.deepcopy(tree)
        #     new_tree['select'] = columns
        #     sql = "create table output as " + tree_to_str(new_tree)
        #     print(sql)

        # else:
        #     print("selection or projection")
        #     print("Step 1: create data content")
        #     sql = "create table output as " + tree_to_str(tree)
        #     print(sql)

        columns = self.get_all_columns(tree['from'])
        new_tree = copy.deepcopy(tree)
        new_tree['select'] = columns
        sql = "create table output as " + self.tree_to_str(new_tree)
        print(sql)
        
        begin = time.time()
        self.db.cursor.execute("DROP TABLE IF EXISTS output")
        self.db.cursor.execute(sql)
        print("\nexecuting time: ", time.time()-begin)
        # conn.commit()

    def upd_condition(self, tree):
        print("\n************************Step 2: update condition****************************")
        # cursor = conn.cursor()

        where_caluse = tree['where']
        keyword = list(where_caluse.keys())[0]
        conditions = copy.deepcopy(where_caluse[keyword])

        sql = ""
        cond_list = set()
        for cond in conditions:
            if cond[0][1] == '.': cond[0][1] = '_'
            if cond[2][1] == '.': cond[2][1] = '_'
            left_opd = "".join(cond[0])
            right_opd = "".join(cond[2])

            if cond[1] == '=':
                cond_list.add("{} || ' {} ' || {}".format(left_opd, '==', right_opd))
            else:
                cond_list.add("{} || ' {} ' || {}".format(left_opd, cond[1], right_opd))
        
        if keyword == '' or keyword == 'and':
            for c in cond_list:
                sql = "update output set condition = array_append(condition, {})".format(c)
                print(sql)
                self.db.cursor.execute(sql)
        else:
            # keyword == or
            sql = "update output set condition = array_append(condition, {})".format("'Or(' || " + " || ' , ' || ".join(cond_list) + " || ')'")
            print(sql)
            self.db.cursor.execute(sql)

        '''
        Check the number of tables
        if num > 1, means there are multiple tables to do join operation,
        remove redundent columns and duplicated columns.
        '''
        table_num = len(tree['from'])
        drop_cols = []
        # if table_num > 1:
        if '*' in tree['select']:
            # remove duplicated columns
            # print('remove redundent')

            for cond in conditions:
                if cond[1] == '=':
                    left_opd = "".join(cond[0])
                    right_opd = "".join(cond[2])
                    sql = "update output set {} = {} where not is_var({})".format(left_opd, right_opd, right_opd)
                    drop_cols.append(right_opd)
                    print(sql)
        else:
            # only keep specified columns
            # print('keep specified columns')
            selected_cols = copy.deepcopy(tree['select'])

            select_col_dict = {}
            for col in selected_cols:
                if col[0][1] == '.': 
                    col[0][1] = '_'
                name = "".join(col[0])
                select_col_dict[name] = col[2]

            rename_col = []
            keys = select_col_dict.keys()
            self.db.cursor.execute("select * from output limit 1")
            for col in self.db.cursor.description:
                col = col[0]
                if col in keys and select_col_dict[col] != '' and col != select_col_dict[col] :
                    rename_col.append("{} to {}".format(col, select_col_dict[col]))
                    continue
                if col == 'condition':
                    continue
                if col not in keys:
                    drop_cols.append(col)

            if len(rename_col) > 0: 
                for new_col in rename_col:
                    sql = "ALTER TABLE output rename column " + new_col
                    print(sql)
                    self.db.cursor.execute(sql)

        if len(drop_cols) > 0:
            sql = "ALTER TABLE output drop column " + ", drop column ".join(drop_cols)
            print(sql)
            self.db.cursor.execute(sql)
        # conn.commit()
                
    def z3(self):
        print("\n************************Step 3: Normalization****************************")
        # cursor = conn.cursor()
        # print('Step3: Normalization')
        sql = 'delete from output where is_contradiction(condition);'
        print(sql)
        self.db.cursor.execute(sql)

        sql = "UPDATE output SET condition = '{}' WHERE is_tauto(condition);"
        print(sql)
        self.db.cursor.execute(sql)

        sql = "UPDATE output SET condition = remove_redundant(condition) WHERE has_redundant(condition);"
        print(sql)
        self.db.cursor.execute(sql)

        # conn.commit()
    
    def do_watch(self, line):
        """Launch an xterm window to watch database tables in real-time
           Usage: watch [table1(,max_rows)] [table2(,max_rows)] ...
           Example: watch hosts switches cf,5"""
        if not line:
            return

        args = line.split()
        if len(args) == 0:
            print("Invalid syntax")
            return

        cmd, cmdfile = mk_watchcmd(self.env.db, args)
        self.env.mkterm(cmd, cmdfile)

shortcut = "s"
description = "Relational Algebra for Conditional Table."
console = SarasateConsole