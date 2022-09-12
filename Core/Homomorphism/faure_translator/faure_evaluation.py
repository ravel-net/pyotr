import sys
import time
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
from Backend.reasoning.Z3.z3smt import z3SMTTools
from Core.Homomorphism.faure_translator.parser import SQL_Parser
from tqdm import tqdm
import databaseconfig as cfg
import psycopg2 
conn = psycopg2.connect(
    host=cfg.postgres["host"], 
    database=cfg.postgres["db"], 
    user=cfg.postgres["user"], 
    password=cfg.postgres["password"])

class FaureEvaluation:
    def __init__(self, conn, SQL, output_table='output', databases={}, domains={}, reasoning_engine='z3', reasoning_sort='Int', simplication_on=True, information_on=False) -> None:
        self._conn = conn
        self._SQL = SQL.strip()
        self.output_table=output_table
        self._information_on = information_on
        self._SQL_parser = SQL_Parser(SQL.strip(), databases)

        self.data_time = 0.0
        self.update_condition_time = {}
        self.simplication_time = {}

        self._data()
        self._upd_condition()

        self.column_datatype_mapping = {}
        cursor = self._conn.cursor()
        cursor.execute("SELECT column_name, data_type FROM information_schema.columns WHERE table_name = '{}';".format(self.output_table))
        for column_name, data_type in cursor.fetchall():
            self.column_datatype_mapping[column_name] = data_type
        conn.commit()

        self._z3Smt = None
        if simplication_on:
            self._z3Smt = z3SMTTools(list(domains.keys()), domains, reasoning_sort)
            self._simplification()
                

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
        conn.commit()

    def _upd_condition(self):
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
            conn.commit()

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

                if is_faure_datatype_key or is_faure_datatype_key:
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

            drop_sql = "ALTER TABLE output drop column " + ", drop column ".join(drop_columns)
            if self._information_on:
                print(drop_sql)
            
            begin_drop = time.time()
            cursor.execute(drop_sql)
            end_drop = time.time()
            self.update_condition_time['drop'] = end_drop-begin_drop

            conn.commit()

        else:
            print("Coming soon!")
            exit()
            
    def _simplification(self):
        if self._information_on:
            print("\n************************Step 3: Normalization****************************")
        cursor = self._conn.cursor()

        if 'id' not in self.column_datatype_mapping:
            cursor.execute("ALTER TABLE output ADD COLUMN id SERIAL PRIMARY KEY;")
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
            cursor.execute("delete from output where id = {}".format(del_tuple[0]))
        else:
            cursor.execute("delete from output where id in {}".format(tuple(del_tuple)))

        contrd_end = time.time()
        self.simplication_time['contradiction'] = contrd_end - contrd_begin
        self._conn.commit()

        '''
        set tautology and remove redundant
        '''
        # print("remove redundant")
        redun_begin = time.time()
        cursor.execute("select id, condition from output")
        redun_count = cursor.rowcount
        # logging.info("size of input(remove redundancy and tautology): %s" % str(count))
        upd_cur = self._conn.cursor()

        for i in tqdm(range(redun_count)):
            row = cursor.fetchone()
            has_redun, result = self._z3Smt.has_redundancy(row[1])
            if has_redun:
                if result != '{}':
                    result = ['"{}"'.format(r) for r in result]
                    upd_cur.execute("UPDATE output SET condition = '{}' WHERE id = {}".format("{" + ", ".join(result) + "}", row[0]))
                else:
                    upd_cur.execute("UPDATE output SET condition = '{{}}' WHERE id = {}".format(row[0]))
        redun_end = time.time()
        self.simplication_time["redundancy"] = redun_end - redun_begin
        self._conn.commit()

        if self._information_on:
            for k, v in self._z3Smt.solver.statistics():
                if (k == "max memory"):
                    print ("Solver Max Memory: %s : %s" % (k, v))





if __name__ == '__main__':
    sql = "select t1.c0 as c0, t0.c1 as c1, t0.c2 as c2, ARRAY[t1.c0, t0.c0] as c3, 1 as c4 from R t0, l t1, pod t2, pod t3 where t0.c4 = 0 and t0.c0 = t1.c1 and t0.c1 = t2.c0 and t0.c2 = t3.c0 and t2.c1 = t3.c1 and t0.c0 = ANY(ARRAY[t1.c0, t0.c0])"
    databases = {
        'pod':{
            'types':['integer', 'int4_faure', 'text[]'], 
            'names':['c0', 'c1', 'condition']
        }, 
        'R':{
            'types':['integer', 'integer', 'integer', 'integer[]', 'integer', 'text[]'], 
            'names':['c0', 'c1', 'c2', 'c3', 'c4', 'condition']
        }, 
        'l':{
            'types':['integer', 'integer', 'text[]'], 
            'names':['c0', 'c1', 'condition']
        }}
    FaureEvaluation(conn, sql, databases=databases, domains={}, simplication_on=True, information_on=True)

    