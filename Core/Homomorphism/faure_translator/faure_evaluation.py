from copy import deepcopy
import sys
import time
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
from Backend.reasoning.Z3.z3smt import z3SMTTools
# BDD manager Module
import BDD_managerModule as bddmm
import Backend.reasoning.CUDD.BDD_manager.encodeCUDD as encodeCUDD

from Core.Homomorphism.faure_translator.parser import SQL_Parser
from tqdm import tqdm
import databaseconfig as cfg
import psycopg2 
from psycopg2.extras import execute_values
# conn = psycopg2.connect(
#     host=cfg.postgres["host"], 
#     database=cfg.postgres["db"], 
#     user=cfg.postgres["user"], 
#     password=cfg.postgres["password"])

class FaureEvaluation:
    """
    Faure Evaluation
    Currently support Z3 and BDD engine.

    Functions:
    ----------
    _data()
        step 1(data) for both Z3 and BDD
    
    _upd_condition_z3()
        step 2(update) for Z3
    
    _upd_condition_BDD(domains, variables)
        step 2(update) for BDD. Currently BDD works for c-variables with the same domain. # TODO: support different domains for different c-variables
    
    _simplication_z3()
        step 3(simplication) for Z3.

    _get_column_datatype_mapping()
        get the mapping between column and datatype. It only works after step 1. 
        
    _process_condition_on_ctable(tablename, variables, domains)
        convert a c-table with text condition to a c-table with BDD reference
    """
    def __init__(self, conn, SQL, additional_condition=None, output_table='output', databases={}, domains={}, reasoning_engine='z3', reasoning_sort='Int', simplication_on=True, information_on=False) -> None:
        """
        Parameters:
        ------------
        conn: psycopg2.connect()
            An instance of Postgres connection
        
        SQL: string
            SQL for faure evaluation
        
        additional_condition: string
            None by default. If not None, it is an additional condition that would be appended to condition column of the output table before doing simplication.

        output_table: string
            "output" by default. Customize output table.

        databases: dict
            The information(i.e., tablename and its attributes datatype) of correspinding tables. Default is an empty dict. The format is {'tablename': ['datatype1', 'datatype2', ...], ...}.

        domains: dict
            The domain of c-variables. Default an empty dict. The format is {'var1': ['val1', 'val2', ...], ...}
            If reasoning engine is BDD, it could not be empty. 
            If the reasonsing sort is 'BitVec', the values of domain for each c-variables can be empty. E.g., {'x':[], 'y':[]}. The default domain for IP is 2^32.
        
        reasoning_engine: 'z3' or 'bdd'
            We currently support Z3 and BDD as the reasoning engine. 
        
        reasoning_sort: 'Int' or 'BitVec'
            We currently support reasoning sort 'Int' and 'BitVec' for z3 engine. 
            BDD engine supports integer and IP data (we use 'Int' and 'BitVec' as flags to specify the reasoning type for BDD, i.e., 'Int' for integer data, 'BitVec' for IP data).
        
        simplication_on: Boolean
            Only works for z3 engine. When simplication_on is True, we would simplify the conditions in the output table.
        
        information_on: Boolean
            It is a siwtch for printing progress information such as the steps, running sqls.
        """
        self._conn = conn
        self._SQL = SQL.strip().rstrip(";")

        self.output_table=output_table
        self._information_on = information_on
        self._reasoning_engine = reasoning_engine
        self._reasoning_sort = reasoning_sort
        self._is_IP = reasoning_sort.lower() == 'bitvec' # if it is IP address
        self._SQL_parser = SQL_Parser(self._SQL, reasoning_engine, databases) # A parser to parse SQL, return SQL_Parser instance

        self.data_time = 0.0 # record time for step 1: data
        self.update_condition_time = {} # record time for step 2, format: {'update_condition': 0, 'instantiation': 0, 'drop':0}. 
        self.simplication_time = {} # record time for step 3, format: {'contradiction': 0, 'redundancy': 0}
        self.column_datatype_mapping = {} # mapping between column and datatype for output table
        
        self._additional_condition = additional_condition
        
        self._empty_condition_idx = None # the reference of the empty condition with BDD

        # step 1: data
        self._data()
        # print(self._reasoning_engine)
        if self._reasoning_engine.lower() == 'z3':
            # Step 2: update
            self._upd_condition_z3()

            self._z3Smt = None # An instance of Z3SMTtool
            if simplication_on:
                self._get_column_datatype_mapping()
                self._z3Smt = z3SMTTools(list(domains.keys()), domains, self._reasoning_sort)
                # Step 3: simplication
                self._simplification_z3()

        elif self._reasoning_engine.lower() == 'bdd':
            # assume all variables have the same domain
            if len(domains.keys()) == 0:
                print("Domain is empty!")
                exit()

            variables = list(domains.keys())
            domain_list =  domains[variables[0]]

            if self._reasoning_sort.lower() == 'bitvec':
                bddmm.initialize(len(variables), 2**32-1) # the domain of IP address is 2^32
            else:
                bddmm.initialize(len(variables), len(domain_list))

            for workingtable in self._SQL_parser.working_tables:
                print(workingtable.TableName), 
                print(self._SQL_parser.databases)
                self._process_condition_on_ctable(workingtable.TableName, variables, domain_list)

            self._get_column_datatype_mapping()

            # Step 2: update
            self._upd_condition_BDD(domain_list, variables)

        else:
            print("Unsupported reasoning engine", self._reasoning_engine)
            exit()

    def _data(self):
        if self._information_on:
            print("\n************************Step 1: create data content****************************")
        
        cursor = self._conn.cursor()
        cursor.execute("drop table if exists {}".format(self.output_table))
        data_sql = "create table {} as {}".format(self.output_table, self._SQL_parser.execution_sql)

        if self._information_on:
            print(data_sql)
        
        begin_data = time.time()
        cursor.execute(data_sql)
        end_data = time.time()

        self.data_time = end_data - begin_data

        if self._information_on:
            print("\ndata executing time: ", self.data_time)
        self._conn.commit()

    def _upd_condition_z3(self):
        if self._information_on:
            print("\n************************Step 2: update condition****************************")
        
        cursor = self._conn.cursor()

        '''
        Update conjunction constraints into conditional column
        '''
        conjunction_condition = self._SQL_parser.additional_conditions_SQL_format
        if conjunction_condition is None:
            print("No additional conditions for c-variables!")
            self.update_condition_time['update_condition'] = 0
        else:
            upd_sql = "update {} set condition = condition || {}".format(self.output_table, conjunction_condition)
            if self._additional_condition is not None: # append additional conditions to output table
                upd_sql = "{} || Array['{}']".format(upd_sql, self._additional_condition)
            
            if self._information_on:
                print(upd_sql)
                
            begin_upd = time.time()
            cursor.execute(upd_sql)
            end_upd = time.time()
            self.update_condition_time['update_condition'] = end_upd - begin_upd
            self._conn.commit()

        '''
        Check the selected columns
        if select *, drop duplicated columns,
        else only keep selected columns
        '''
        sqls = []
        for key_simple_attr in self._SQL_parser.equal_attributes_from_where_clause:
            key_name = self._SQL_parser.simple_attribute_mapping[key_simple_attr].AttributeName

            # if the datatype of attribute is Faure datatype(self-set) or USER-DEFINED(learn from database), update it. Same as the following 'is_faure_datatype_attr'
            is_faure_datatype_key = self._SQL_parser.simple_attr2datatype_mapping[key_simple_attr].lower() in self._SQL_parser._FAURE_DATATYPE or self._SQL_parser.simple_attr2datatype_mapping[key_simple_attr] == 'USER-DEFINED'
            # print("is_faure_datatype_key", key_simple_attr, self._SQL_parser.simple_attr2datatype_mapping[key_simple_attr], is_faure_datatype_key)
            for attr in self._SQL_parser.equal_attributes_from_where_clause[key_simple_attr]:
                attr_name = self._SQL_parser.simple_attribute_mapping[attr].AttributeName
                
                is_faure_datatype_attr = self._SQL_parser.simple_attr2datatype_mapping[attr].lower() in self._SQL_parser._FAURE_DATATYPE or self._SQL_parser.simple_attr2datatype_mapping[attr] == 'USER-DEFINED'
                # print("is_faure_datatype_attr", attr, self._SQL_parser.simple_attr2datatype_mapping[attr], is_faure_datatype_attr)
                if is_faure_datatype_key or is_faure_datatype_attr:
                    sql = "update {} set {} = {} where not is_var({})".format(self.output_table,  attr_name, key_name, key_name)
                    sqls.append(sql)
            
        begin_instantiated = time.time()
        for sql in sqls:
            if self._information_on:
                print(sql)
            cursor.execute(sql)
        end_instantiated = time.time()
        self.update_condition_time['instantiation'] = end_instantiated-begin_instantiated
        self._conn.commit()

        if self._SQL_parser.type == 1: # selection
            drop_columns = self._SQL_parser.drop_columns

            if len(drop_columns) == 0:
                self.update_condition_time['drop'] = 0
            else:
                drop_sql = "ALTER TABLE {} drop column ".format(self.output_table) + ", drop column ".join(drop_columns)
                if self._information_on:
                    print(drop_sql)
                
                begin_drop = time.time()
                cursor.execute(drop_sql)
                end_drop = time.time()
                self.update_condition_time['drop'] = end_drop-begin_drop

            self._conn.commit()

        else:
            self._conn.commit()
            print("Coming soon!")
            exit()
            
    def _simplification_z3(self):
        if self._information_on:
            print("\n************************Step 3: Normalization****************************")
        cursor = self._conn.cursor()

        if 'id' not in self.column_datatype_mapping:
            cursor.execute("ALTER TABLE {} ADD COLUMN id SERIAL PRIMARY KEY;".format(self.output_table))
        self._conn.commit()

        '''
        delete contradiction
        '''
        if self._information_on:
            print("delete contradiction")
        
        contrd_begin = time.time()
        cursor.execute("select id, condition from {}".format(self.output_table))
        contrad_count = cursor.rowcount
        # logging.info("size of input(delete contradiction): %s" % str(count))
        del_tuple = []
        for i in tqdm(range(contrad_count)):
            row = cursor.fetchone()
            is_contrad = self._z3Smt.iscontradiction(row[1])

            if is_contrad:
                del_tuple.append(row[0])
            
        if len(del_tuple) == 0:
            pass
        elif len(del_tuple) == 1:
            cursor.execute("delete from {} where id = {}".format(self.output_table, del_tuple[0]))
        else:
            cursor.execute("delete from {} where id in {}".format(self.output_table, tuple(del_tuple)))

        contrd_end = time.time()
        self.simplication_time['contradiction'] = contrd_end - contrd_begin
        self._conn.commit()

        '''
        set tautology and remove redundant
        '''
        # print("remove redundant")
        redun_begin = time.time()
        cursor.execute("select id, condition from {}".format(self.output_table))
        redun_count = cursor.rowcount
        # logging.info("size of input(remove redundancy and tautology): %s" % str(count))
        upd_cur = self._conn.cursor()

        for i in tqdm(range(redun_count)):
            row = cursor.fetchone()
            has_redun, result = self._z3Smt.has_redundancy(row[1])
            if has_redun:
                if result != '{}':
                    result = ['"{}"'.format(r) for r in result]
                    upd_cur.execute("UPDATE {} SET condition = '{}' WHERE id = {}".format(self.output_table, "{" + ", ".join(result) + "}", row[0]))
                else:
                    upd_cur.execute("UPDATE {} SET condition = '{{}}' WHERE id = {}".format(self.output_table, row[0]))
        redun_end = time.time()
        self.simplication_time["redundancy"] = redun_end - redun_begin
        self._conn.commit()

        if self._information_on:
            for k, v in self._z3Smt.solver.statistics():
                if (k == "max memory"):
                    print ("Solver Max Memory: %s : %s" % (k, v))

    def _get_column_datatype_mapping(self):
        """
        Because the datatypes are read from database, the 'int4_faure' and 'inet_faure' are faure datatype that return 'USER-DEFINE' from database; 
        the array datatype returns 'ARRAY' from datatype. We cannot make the accurate datatype for ARRAY. #TODO: specify the accurate datatype for array
        """
        cursor = self._conn.cursor()
        cursor.execute("SELECT column_name, data_type FROM information_schema.columns WHERE table_name = '{}';".format(self.output_table))
        for column_name, data_type in cursor.fetchall():
            self.column_datatype_mapping[column_name] = data_type
            if data_type.lower() == 'user-defined':
                if self._reasoning_sort.lower() == 'int':
                    self.column_datatype_mapping[column_name] = 'int4_faure'
                elif self._reasoning_sort.lower() == 'bitvec':
                    self.column_datatype_mapping[column_name] = 'inet_faure'
                else:
                    print("Unsupported reasoning sort:", self._reasoning_sort)
                    exit()
            else:
                self.column_datatype_mapping[column_name] = data_type
        self._conn.commit()
    
    def _upd_condition_BDD(self, domains, variables):
        if self._information_on:
            print("\n************************Step 2: update condition****************************")
        cursor = self._conn.cursor()

        if 'id' not in self.column_datatype_mapping:
            cursor.execute("ALTER TABLE {} ADD COLUMN id SERIAL PRIMARY KEY;".format(self.output_table))
        self._conn.commit()

        '''
        conjunction conditions
        '''
        conjunction_condition = self._SQL_parser.additional_conditions_SQL_format
        old_constraints = self._SQL_parser.old_conditions_attributes_BDD

        new_reference_mapping = {}
        if conjunction_condition is not None:
            
            select_sql = "select ARRAY[{}] as old_conditions, {} as conjunction_condition, id from {}".format(", ".join(old_constraints), conjunction_condition, self.output_table) 
            if self._information_on:
                print(select_sql)
                
            begin_upd = time.time()
            cursor.execute(select_sql)
            end_upd = time.time()
            count_num = cursor.rowcount
            
            for i in range(count_num):
                (old_conditions, conjunctin_conditions, id) = cursor.fetchone()
                # print(old_conditions, conjunctin_conditions, id)
                '''
                Logical AND all original conditions for all tables
                '''
                # print("result", bddmm.operate_BDDs(0, 1, "&"))
                old_bdd = old_conditions[0]
                for cond_idx in range(1, len(old_conditions)):
                    bdd1 = old_conditions[cond_idx]
                    # print("old_bdd", old_bdd, "bdd1", bdd1)
                    old_bdd = bddmm.operate_BDDs(int(bdd1), int(old_bdd), "&")
                    # print('old', old_bdd)

                '''
                get BDD reference number for conjunction condition
                '''
                conjunction_str = "And({})".format(", ".join(conjunctin_conditions))
                encoded_conjunction_str, variables_arr = encodeCUDD.convertToCUDD(conjunction_str, domains, variables, self._is_IP)
                conjunction_ref = bddmm.str_to_BDD(encoded_conjunction_str)

                # Logical AND original BDD and conjunction BDD
                new_ref = bddmm.operate_BDDs(old_bdd, conjunction_ref, "&")
                new_reference_mapping[id] = new_ref
        else:
            if self._information_on:
                print("No conjunction conditions for c-variables!")
            self.update_condition_time['update_condition'] = 0
            
            select_sql = "select ARRAY[{}] as old_conditions, id from {}".format(", ".join(old_constraints), self.output_table) 
            if self._information_on:
                print(select_sql)
                
            begin_upd = time.time()
            cursor.execute(select_sql)
            end_upd = time.time()
            count_num = cursor.rowcount
            
            for i in range(count_num):
                (old_conditions, id) = cursor.fetchone()
                # print(old_conditions, conjunctin_conditions, id)
                '''
                Logical AND all original conditions for all tables
                '''
                # print("result", bddmm.operate_BDDs(0, 1, "&"))
                old_bdd = old_conditions[0]
                for cond_idx in range(1, len(old_conditions)):
                    bdd1 = old_conditions[cond_idx]
                    # print("old_bdd", old_bdd, "bdd1", bdd1)
                    old_bdd = bddmm.operate_BDDs(int(bdd1), int(old_bdd), "&")
                    # print('old', old_bdd)

                new_reference_mapping[id] = old_bdd
        
        '''
        append additional conditions to output table
        '''
        if self._additional_condition is not None:
            encoded_additional_conditions, _ = encodeCUDD.convertToCUDD(self._additional_condition, domains, variables, self._is_IP)
            additional_ref = bddmm.str_to_BDD(encoded_additional_conditions)
            for id in new_reference_mapping.keys():
                cond_ref = new_reference_mapping[id]
                new_ref = bddmm.operate_BDDs(cond_ref, additional_ref, '&')
                # update condition reference for each tuple after appending additional conditions
                new_reference_mapping[id] = new_ref

        '''
        add condition column of integer type
        update bdd reference number on condition column
        '''
        sql = "alter table if exists {} add column condition integer".format(self.output_table)
        cursor.execute(sql)
        self._conn.commit()

        begin_upd = time.time()
        for key in new_reference_mapping.keys():
            sql = "update {} set condition = {} where id = {}".format(self.output_table, new_reference_mapping[key], key)
            cursor.execute(sql)
        end_upd = time.time()
        self._conn.commit()

        self.update_condition_time['update_condition'] = end_upd - begin_upd
        self._conn.commit()
        '''
        Check the selected columns
        if select *, drop duplicated columns,
        else only keep selected columns
        '''
        sqls = []
        for key_simple_attr in self._SQL_parser.equal_attributes_from_where_clause:
            key_name = self._SQL_parser.simple_attribute_mapping[key_simple_attr].AttributeName
            is_faure_datatype_key = self._SQL_parser.simple_attr2datatype_mapping[key_simple_attr].lower() in self._SQL_parser._FAURE_DATATYPE

            for attr in self._SQL_parser.equal_attributes_from_where_clause[key_simple_attr]:
                attr_name = self._SQL_parser.simple_attribute_mapping[attr].AttributeName

                is_faure_datatype_attr = self._SQL_parser.simple_attr2datatype_mapping[attr].lower() in self._SQL_parser._FAURE_DATATYPE

                if is_faure_datatype_key or is_faure_datatype_attr:
                    sql = "update {} set {} = {} where not is_var({})".format(self.output_table,  attr_name, key_name, key_name)
                    sqls.append(sql)
            
        begin_instantiated = time.time()
        for sql in sqls:
            if self._information_on:
                print(sql)
            cursor.execute(sql)
        end_instantiated = time.time()
        self.update_condition_time['instantiation'] = end_instantiated-begin_instantiated

        if self._SQL_parser.type == 1: # selection
            drop_columns = self._SQL_parser.drop_columns

            drop_sql = "ALTER TABLE {} drop column ".format(self.output_table) + ", drop column ".join(drop_columns)
            if self._information_on:
                print(drop_sql)
            
            begin_drop = time.time()
            cursor.execute(drop_sql)
            end_drop = time.time()
            self.update_condition_time['drop'] = end_drop-begin_drop

            self._conn.commit()

        else:
            print("Coming soon!")
            exit()

    def _process_condition_on_ctable(self, tablename, variables, domains):
        """
        convert text condition to BDD reference in a c-table

        Parameters:
        -----------
        tablename: string
            the tablename of c-table
        
        variables: list
            A list of c-variables
        
        domains: list
            A list of values for c-variables. All c-varaibles have the same domain. 
        """
        cursor = self._conn.cursor()

        sql = "select {} from {}".format(", ".join(self._SQL_parser.databases[tablename]['names']), tablename)
        cursor.execute(sql)

        count_num = cursor.rowcount
        
        '''
        locate condition
        '''
        cond_idx = -1

        new_tuples = []
        for i in tqdm(range(count_num)):
            row = cursor.fetchone()
            list_row = list(row)
            if type(list_row[cond_idx]) == int: # if the condition is int datatype, return
                return
            if len(list_row[cond_idx]) == 0:
                # list_row[cond_idx] = None
                if self._empty_condition_idx is None:
                    condition = ""
                    begin_process = time.time()
                    encoded_c, variablesArray = encodeCUDD.convertToCUDD(condition, domains, variables, self._is_IP)
                    end_process_encode = time.time()
                    empty_condition_idx = bddmm.str_to_BDD(encoded_c)
                    end_process_strToBDD = time.time()
                    if self._information_on:
                        print("Time to encode condition {}: {} s".format(empty_condition_idx, end_process_encode-begin_process))
                        print("Time to str_to_BDD in condition {}: {} s".format(empty_condition_idx, end_process_strToBDD-end_process_encode))
                    self._empty_condition_idx = empty_condition_idx
                list_row[cond_idx] = self._empty_condition_idx
            else:
                condition = ", ".join(list_row[cond_idx])

                # Call BDD module 
                begin_process = time.time()
                encoded_c, variablesArray = encodeCUDD.convertToCUDD(condition, domains, variables, self._is_IP)
                end_process_encode = time.time()
                bdd_idx = bddmm.str_to_BDD(encoded_c)
                end_process_strToBDD = time.time()
                if self._information_on:
                    print("Time to encode condition {}: {} s".format(bdd_idx, end_process_encode-begin_process))
                    print("Time to str_to_BDD in condition {}: {} s".format(bdd_idx, end_process_strToBDD-end_process_encode))
                list_row[cond_idx] = bdd_idx

            row = tuple(list_row)
            new_tuples.append(deepcopy(row))

        sql = "drop table if exists {tablename}".format(tablename=tablename)
        cursor.execute(sql)

        self.column_datatype_mapping['condition'] = 'integer'

        columns = []
        for idx, name in enumerate(self._SQL_parser.databases[tablename]['names']):
            datatype = self._SQL_parser.databases[tablename]['types'][idx]

            if name == 'condition':
                datatype = 'integer'
                self._SQL_parser.databases[tablename]['types'][idx] = datatype # update it

            elif datatype.lower() == 'user-defined':
                if self._reasoning_sort.lower() == 'int':
                    datatype = 'int4_faure'
                elif self._reasoning_sort.lower() == 'bitvec':
                    datatype = 'inet_faure'
                else:
                    print("Unsupported reasoning sort:", self._reasoning_sort)
                    exit()

                self._SQL_parser.databases[tablename]['types'][idx] = datatype # update it

            columns.append("{} {}".format(name, datatype))
        sql = "create table {} ({})".format(tablename, ", ".join(columns))
        cursor.execute(sql)

        sql = "insert into {tablename} values %s".format(tablename=tablename)
        execute_values(cursor, sql, new_tuples)
        # cursor.executemany(new_tuples)
        self._conn.commit()

if __name__ == '__main__':
    # sql = "select t1.c0 as c0, t0.c1 as c1, t0.c2 as c2, ARRAY[t1.c0, t0.c0] as c3, 1 as c4 from R t0, l t1, pod t2, pod t3 where t0.c4 = 0 and t0.c0 = t1.c1 and t0.c1 = t2.c0 and t0.c2 = t3.c0 and t2.c1 = t3.c1 and t0.c0 = ANY(ARRAY[t1.c0, t0.c0])"
    # databases = {
    #     'pod':{
    #         'types':['integer', 'int4_faure', 'text[]'], 
    #         'names':['c0', 'c1', 'condition']
    #     }, 
    #     'R':{
    #         'types':['integer', 'integer', 'integer', 'integer[]', 'integer', 'text[]'], 
    #         'names':['c0', 'c1', 'c2', 'c3', 'c4', 'condition']
    #     }, 
    #     'l':{
    #         'types':['integer', 'integer', 'text[]'], 
    #         'names':['c0', 'c1', 'condition']
    #     }}
    conn = psycopg2.connect(
        host=cfg.postgres["host"], 
        database=cfg.postgres["db"], 
        user=cfg.postgres["user"], 
        password=cfg.postgres["password"])

    domains = {
        'd1':['1', '2'],
        'd2':['1', '2'],
        'd':['1', '2']
    }
    # domains = {
    #     'd1':['10.0.0.1', '10.0.0.2'],
    #     'd2':['10.0.0.1', '10.0.0.2'],
    #     'd':['10.0.0.1', '10.0.0.2']
    # }
    # sql = "select t3.a1 as a1, t1.a2 as a2 from R t1, R t2, L t3, L t4 where t1.a1 = t3.a2 and t2.a1 = t4.a2 and t3.a1 = t4.a1 and t1.a2 = '10.0.0.1'"
    sql = "select t3.a1 as a1, t1.a2 as a2 from R t1, R t2, L t3, L t4 where t1.a1 = t3.a2 and t2.a1 = t4.a2 and t3.a1 = t4.a1 and t1.a2 = '1';"
    FaureEvaluation(conn, sql, additional_condition="d != 2", databases={}, domains=domains, reasoning_engine='z3', reasoning_sort='Int', simplication_on=False, information_on=True)


    # bddmm.initialize(1, 2**32-1)
    # bdd1_str = ""
    # bdd2_str = "b == 10.0.0.1"
    # bdd3_str = "b == 1"

    # encoded_bdd1, _ = encodeCUDD.convertToCUDD(bdd1_str, ['10.0.0.1', '10.0.0.2'], ['b'], True)
    # encoded_bdd2, _ = encodeCUDD.convertToCUDD(bdd2_str, ['10.0.0.1', '10.0.0.2'], ['b'], True)
    # encoded_bdd3, _ = encodeCUDD.convertToCUDD(bdd3_str, ['1', '2'], ['b'], False)
    # print("encoded_bdd1", encoded_bdd1)
    # print("encoded_bdd2", encoded_bdd2)
    # print("encoded_bdd2", encoded_bdd3)

    # bdd1 = bddmm.str_to_BDD(encoded_bdd1)
    # print("bdd1", bdd1)
    # bdd2 = bddmm.str_to_BDD(encoded_bdd2)
    # print("bdd2", bdd2)

    # bdd3 = bddmm.operate_BDDs(bdd1, bdd1, "&")
    # print("bdd3", bdd3)

    # bdd4 = bddmm.operate_BDDs(bdd2, bdd1, "&")
    # print("bdd4", bdd4)


    