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
    def __init__(self, conn, SQL, output_table='output', databases={}, domains={}, reasoning_engine='z3', reasoning_sort='Int', simplication_on=True, information_on=False) -> None:
        self._conn = conn
        self._SQL = SQL.strip()

        self._databases = {}
        for table in databases:
            table_lower = table.lower()
            self._databases[table_lower] = {'types': [], 'names': []}
            for i in range(len(databases[table]['names'])):
                self._databases[table_lower]['types'].append(databases[table]['types'][i].lower()) 
                self._databases[table_lower]['names'].append(databases[table]['names'][i].lower()) 

        self.output_table=output_table
        self._information_on = information_on
        self._reasoning_engine = reasoning_engine
        self._SQL_parser = SQL_Parser(SQL.strip(), reasoning_engine, databases)

        self.data_time = 0.0
        self.update_condition_time = {}
        self.simplication_time = {}
        self.column_datatype_mapping = {}
        

        self._empty_condition_idx = None
        # print(self._reasoning_engine)
        if self._reasoning_engine.lower() == 'z3':

            self._data()
            self._upd_condition_z3()

            self._z3Smt = None
            if simplication_on:
                self._get_column_datatype_mapping()
                self._z3Smt = z3SMTTools(list(domains.keys()), domains, reasoning_sort)
                self._simplification_z3()

        elif self._reasoning_engine.lower() == 'bdd':
            
            # assume all variables have the same domain
            variables = list(domains.keys())
            domain_list =  domains[variables[0]]

            bddmm.initialize(len(variables), len(domain_list))

            for workingtable in self._SQL_parser._working_tables:
                self._process_condition_on_ctable(workingtable.TableName, variables, domain_list)
            self._data()

            self._get_column_datatype_mapping()
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
        additional_condition = self._SQL_parser.additional_conditions_SQL_format
        if additional_condition is None:
            print("No additional conditions for c-variables!")
            self.update_condition_time['update_condition'] = 0
        else:
            upd_sql = "update {} set condition = condition || {}".format(self.output_table, additional_condition)
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
        cursor = self._conn.cursor()
        cursor.execute("SELECT column_name, data_type FROM information_schema.columns WHERE table_name = '{}';".format(self.output_table))
        for column_name, data_type in cursor.fetchall():
            self.column_datatype_mapping[column_name] = data_type
        self._conn.commit()
    
    def _upd_condition_BDD(self, domains, variables):
        if self._information_on:
            print("\n************************Step 2: update condition****************************")
        cursor = conn.cursor()

        if 'id' not in self.column_datatype_mapping:
            cursor.execute("ALTER TABLE {} ADD COLUMN id SERIAL PRIMARY KEY;".format(self.output_table))
        self._conn.commit()

        '''
        conjunction conditions
        '''
        additional_condition = self._SQL_parser.additional_conditions_SQL_format
        if additional_condition is not None:
            old_constraints = self._SQL_parser.old_conditions_attributes_BDD
            
            select_sql = "select ARRAY[{}] as old_conditions, {} as conjunction_condition, id from {}".format(", ".join(old_constraints), additional_condition, self.output_table) 
            if self._information_on:
                print(select_sql)
                
            begin_upd = time.time()
            cursor.execute(select_sql)
            end_upd = time.time()
            count_num = cursor.rowcount
            new_reference_mapping = {}
            for i in range(count_num):
                (old_conditions, conjunctin_conditions, id) = cursor.fetchone()

                '''
                Logical AND all original conditions for all tables
                '''
                old_bdd = old_conditions[0]
                for cond_idx in range(1, len(old_conditions)):
                    bdd1 = old_conditions[cond_idx]
                    old_bdd = bddmm.operate_BDDs(bdd1, old_bdd, "&")

                '''
                get BDD reference number for conjunction condition
                '''
                conjunction_str = "And({})".format(", ".join(conjunctin_conditions))
                encoded_conjunction_str, variables_arr = encodeCUDD.convertToCUDD(conjunction_str, domains, variables)
                conjunction_ref = bddmm.str_to_BDD(encoded_conjunction_str)

                # Logical AND original BDD and conjunction BDD
                new_ref = bddmm.operate_BDDs(old_bdd, conjunction_ref, "&")

                new_reference_mapping[id] = new_ref

                '''
                add integer type of condition column
                update bdd reference number on condition column
                '''
                sql = "alter table if exists {} add column condition integer".format(self.output_table)
                cursor.execute(sql)
                self._conn.commit()

                for key in new_reference_mapping.keys():
                    sql = "update {} set condition = {} where id = {}".format(self.output_table, new_reference_mapping[key], key)
                    cursor.execute(sql)
                self._conn.commit()

            self.update_condition_time['update_condition'] = end_upd - begin_upd
            self._conn.commit()
        else:
            print("No additional conditions for c-variables!")
            self.update_condition_time['update_condition'] = 0

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
        convert condition to BDD version
        """
        cursor = self._conn.cursor()

        sql = "select {} from {}".format(", ".join(self._databases[tablename]['names']), tablename)
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

            if len(list_row[cond_idx]) == 0:
                # list_row[cond_idx] = None
                if self._empty_condition_idx is None:
                    condition = ""
                    begin_process = time()
                    encoded_c, variablesArray = encodeCUDD.convertToCUDD(condition, domains, variables)
                    end_process_encode = time()
                    empty_condition_idx = bddmm.str_to_BDD(encoded_c)
                    end_process_strToBDD = time()
                    if self._information_on:
                        print("Time to encode condition {}: {} s".format(empty_condition_idx, end_process_encode-begin_process))
                        print("Time to str_to_BDD in condition {}: {} s".format(empty_condition_idx, end_process_strToBDD-end_process_encode))
                    self._empty_condition_idx = empty_condition_idx
                list_row[cond_idx] = self._empty_condition_idx
            else:
                condition = ", ".join(list_row[cond_idx])

                # Call BDD module 
                begin_process = time()
                encoded_c, variablesArray = encodeCUDD.convertToCUDD(condition, domains, variables)
                end_process_encode = time()
                bdd_idx = bddmm.str_to_BDD(encoded_c)
                end_process_strToBDD = time()
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
        for idx, name in enumerate(self._databases[tablename]['names']):
            columns.append("{} {}".format(name, self._databases[tablename]['types'][idx]))
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
    sql = "select t3.a1 as a1, t1.a2 as a2 from R t1, R t2, L t3, L t4 where t1.a1 = t3.a2 and t2.a1 = t4.a2 and t3.a1 = t4.a1 and t1.a2 = '1'"
    FaureEvaluation(conn, sql, databases={}, domains=domains, reasoning_engine='bdd', simplication_on=True, information_on=True)

    