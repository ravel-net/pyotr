from copy import deepcopy
import sys
import time
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
from Backend.reasoning.Z3.z3smt import z3SMTTools
# BDD manager Module
# import BDD_managerModule as bddmm
import Backend.reasoning.CUDD.BDD_manager.encodeCUDD as encodeCUDD
# from Backend.reasoning.CUDD.BDDTools import BDDTools

from Core.Faure.parser import SQL_Parser
from tqdm import tqdm
import databaseconfig as cfg
import psycopg2 
from psycopg2.extras import execute_values
from utils.logging import timeit
import logging
from utils import parsing_utils
logging.basicConfig(filename='program.log', level=logging.DEBUG)
logging.debug('[Datalog] Start Logging ...')
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
        
    _process_condition_on_ctable(tablename, variables, domains)
        convert a c-table with text condition to a c-table with BDD reference
    """
    @timeit
    def __init__(self, conn, SQL, reasoning_tool=None, additional_condition=None, output_table='output', databases={}, domains={}, reasoning_engine='z3', reasoning_sort={}, simplication_on=True, information_on=False, faure_evaluation_mode='contradiction', sqlPartitioned={}) -> None:
        """
        Parameters:
        ------------
        conn: psycopg2.connect()
            An instance of Postgres connection
        
        SQL: string
            SQL for faure evaluation

        reasoning_tool: object
            Object of z3 Solver or BDDManagerMondule
        
        additional_condition: string
            None by default. If not None, it is an additional condition that would be appended to condition column of the output table before doing simplication.

        output_table: string
            "output" by default. Customize output table.

        databases: dict
            The information(i.e., tablename and its attributes datatype) of correspinding tables. Default is an empty dict. 
            The format is {'tablename': {'types': ['datatype1', 'datatype2', ...], 'names': ['attr1', 'attr2', ...]}, ...}.
            include condition and its type

        domains: dict
            The domain of c-variables. Default an empty dict. The format is {'var1': ['val1', 'val2', ...], ...}
            If reasoning engine is BDD, it could not be empty. 
            If the reasonsing sort is 'BitVec', the values of domain for each c-variables can be empty. E.g., {'x':[], 'y':[]}. The default domain for IP is 2^32.
        
        reasoning_engine: 'z3' or 'bdd'
            We currently support Z3 and BDD as the reasoning engine. 
        
        reasoning_sort: dict
            Set reasoning sort for each variable: 'Int' or 'BitVec'.
            Format: {var1: 'Int', var2: 'BitVec', ...}; the reasoning sort of this variable would be 'Int'if you don't set reasoning type for the variable.
            We currently support reasoning sort 'Int' and 'BitVec' for z3 engine. 
            BDD engine supports integer and IP data (we use 'Int' and 'BitVec' as flags to specify the reasoning type for BDD, i.e., 'Int' for integer data, 'BitVec' for IP data).
        
        simplication_on: Boolean
            Only works for z3 engine. When simplication_on is True, we would simplify the conditions in the output table.
        
        information_on: Boolean
            It is a siwtch for printing progress information such as the steps, running sqls.

        faure_evaluation_mode: string
            the value is chosen from "contradiction" and "implication". 
            "contradiction" means the valuation function is checking if the condition is contradictory
            "implication" means the valuation function is checking if the old condition implies the join condition

            
        """
        self._conn = conn
        self._SQL = SQL.strip().rstrip(";")

        self.output_table=output_table
        self._information_on = information_on
        self._simplification_on = simplication_on
        self._reasoning_engine = reasoning_engine
        self._reasoning_sort = reasoning_sort
        self._additional_condition = additional_condition
        self._domains = domains
        self._databases = databases
        self._faure_evaluation_mode = faure_evaluation_mode
        self._summary_nodes = sqlPartitioned["summary_nodes"]
        self._tables = sqlPartitioned["tables"]
        self._constraints = sqlPartitioned["constraints"]
        self._constraintsZ3Format = sqlPartitioned["constraintsZ3Format"]

        self.data_time = 0.0 # record time for step 1: data
        self.update_condition_time = {} # record time for step 2, format: {'update_condition': 0, 'instantiation': 0, 'drop':0}. 
        self.simplication_time = {} # record time for step 3, format: {'contradiction': 0, 'redundancy': 0}

        # self._z3Smt = z3SMTTools(list(self._domains.keys()), self._domains, self._reasoning_sort)
        self._reasoning_tool = reasoning_tool

        if self._SQL.lower().startswith('with'):
            cursor = conn.cursor()
            cursor.execute(self._SQL)
            #conn.commit()

            if simplication_on:
                self._reasoning_tool.simplification(self.output_table)
        else:
            # self._SQL_parser = SQL_Parser(conn, self._SQL, True, reasoning_engine, databases)
            self._additional_condition = additional_condition
            self._empty_condition_idx = None # the reference of the empty condition with BDD
            
            if self._reasoning_engine.lower() == 'z3':
                # integration of step 1 and step 2
                if self._faure_evaluation_mode == 'contradiction':
                    self._integration()
                    
                elif self._faure_evaluation_mode == 'implication':
                    self._integration_implication_mode()

                    self._reserve_tuples_by_checking_implication_z3()
                else:
                    print("Please input correct mode! 'contradiction' or 'implication'")

                if self._additional_condition:
                    self._append_additional_condition()

                if simplication_on:
                    # Step 3: simplication
                    self._reasoning_tool.simplification(self.output_table, self._conn)

            elif self._reasoning_engine.lower() == 'bdd':
                # step 1: data
                self._integration()

                # Step 2: update
                self._upd_condition_BDD()

            else:
                print("Unsupported reasoning engine", self._reasoning_engine)
                exit()

    @timeit
    def getSelectSQL(self, mode = "contradiction"):
        arrayPart = parsing_utils.getArrayPart(self._constraintsZ3Format)
        tablesAsConditions = parsing_utils.getTablesAsConditions(self._tables)
        if mode == "contradiction":
            if arrayPart:
                conditionPart = tablesAsConditions + " || Array[" + arrayPart + "]::text[] as condition"
            else:
                conditionPart = tablesAsConditions + "::text[] as condition"
            selectPart = self._summary_nodes+[conditionPart]
            sql = "select " + ", ".join(selectPart) + " from " + ", ".join(self._tables)
            if (self._constraints):
                sql += " where " + "(" + " and ".join(self._constraints) + ")"
            return sql  
        elif mode == "implication":
            if arrayPart:
                conditionPart = tablesAsConditions + "::text[] as old_conditions, " + arrayPart + "::text as conjunction_condition"
            else:
                conditionPart = tablesAsConditions + "::text[] as old_conditions, " + "'' as conjunction_condition"
            selectPart = self._summary_nodes+[conditionPart]
            sql = "select " + ", ".join(selectPart) + " from " + ", ".join(self._tables)
            if (self._constraints):
                sql += " where " + " and ".join(self._constraints)
            return sql        
        else:
            print("implication mode not supported yet", mode)
            exit()    

    @timeit
    def _integration(self):
        if self._information_on:
            print("\n************************Step 1: data with complete condition****************************")
        
        cursor = self._conn.cursor()
        cursor.execute("drop table if exists {}".format(self.output_table))
        select_sql = self.getSelectSQL(mode = self._faure_evaluation_mode)
        data_sql = "create table {} as {}".format(self.output_table, select_sql)
        if self._information_on:
            print(data_sql)
        
        begin_data = time.time()
        cursor.execute(data_sql)
        end_data = time.time()

        self.data_time = end_data - begin_data

        if self._information_on:
            print("\ncombined executing time: ", self.data_time)
        # start = time.time()
        self._conn.commit()
        # end = time.time()
        # logging.info("Time: Commit took {}".format(end-start))
    
    @timeit
    def _integration_implication_mode(self):
        if self._information_on:
            print("\n************************Step 1: data with complete condition****************************")
        
        cursor = self._conn.cursor()
        cursor.execute("drop table if exists {}".format(self.output_table))
        select_sql = self.getSelectSQL(mode = self._faure_evaluation_mode)
        # data_sql = "create table {} as {}".format(self.output_table, self._SQL_parser.implication_mode_sql)
        data_sql = "create table {} as {}".format(self.output_table, select_sql)
        if self._information_on:
            print(data_sql)
        
        begin_data = time.time()
        cursor.execute(data_sql)
        end_data = time.time()

        self.data_time = end_data - begin_data

        if self._information_on:
            print("\ncombined executing time: ", self.data_time)
        # start = time.time()
        self._conn.commit()
        # end = time.time()
        # logging.info("Time: Commit took {}".format(end-start))

    @timeit
    def _append_additional_condition(self):
        cursor = self._conn.cursor()
        cursor.execute("update {} set condition = condition || Array['{}']".format(self.output_table, self._additional_condition))
        # conn.commit()

    @timeit
    def _upd_condition_BDD(self):
        if self._information_on:
            print("\n************************Step 2: update condition****************************")
        cursor = self._conn.cursor()

        # if 'id' not in self.column_datatype_mapping:
        cursor.execute("ALTER TABLE {} ADD COLUMN if not exists id SERIAL PRIMARY KEY;".format(self.output_table))
        #self._conn.commit()

        select_sql = "select old_conditions, conjunction_condition, id from {}".format(self.output_table) 
        if self._information_on:
            print(select_sql)
        
        begin_upd = time.time()
        cursor.execute(select_sql)
        end_upd = time.time()

        count_num = cursor.rowcount
        data_tuples = cursor.fetchall()
        #self._conn.commit()
        new_reference_mapping = {}
        for i in range(count_num):
            
            (old_conditions, conjunctin_conditions, id) = data_tuples[i]
            '''
            Logical AND all original conditions for all tables
            '''
            old_bdd = old_conditions[0]
            for cond_idx in range(1, len(old_conditions)):
                bdd1 = old_conditions[cond_idx]
                old_bdd = self._reasoning_tool.operate_BDDs(int(bdd1), int(old_bdd), "&")

            '''
            get BDD reference number for conjunction condition
            '''
            if conjunctin_conditions and len(conjunctin_conditions) != 0:
                # conjunction_str = "And({})".format(", ".join(conjunctin_conditions))
                conjunction_ref = self._reasoning_tool.str_to_BDD(conjunctin_conditions)

                # Logical AND original BDD and conjunction BDD
                new_ref = self._reasoning_tool.operate_BDDs(old_bdd, conjunction_ref, "&")
                new_reference_mapping[id] = new_ref
            else:
                new_reference_mapping[id] = old_bdd

        
        '''
        append additional conditions to output table
        '''
        if self._additional_condition:
            additional_ref = self._reasoning_tool.str_to_BDD(self._additional_condition)
            for id in new_reference_mapping.keys():
                cond_ref = new_reference_mapping[id]
                new_ref = self._reasoning_tool.operate_BDDs(cond_ref, additional_ref, '&')
                # update condition reference for each tuple after appending additional conditions
                new_reference_mapping[id] = new_ref

        '''
        add condition column of integer type
        update bdd reference number on condition column
        '''
        sql = "alter table if exists {} drop column if exists old_conditions, drop column if exists conjunction_condition, add column condition integer".format(self.output_table)
        cursor.execute(sql)
        #self._conn.commit()

        begin_upd = time.time()
        for key in new_reference_mapping.keys():
            sql = "update {} set condition = {} where id = {}".format(self.output_table, new_reference_mapping[key], key)
            cursor.execute(sql)
        end_upd = time.time()
        #self._conn.commit()

        self.update_condition_time['update_condition'] = end_upd - begin_upd
        #self._conn.commit()

        sql = "alter table if exists {} drop column if exists id".format(self.output_table)
        cursor.execute(sql)
        #self._conn.commit()
    
    @timeit
    def _reserve_tuples_by_checking_implication_z3(self):
        if self._information_on:
            print("\n************************Step 2: reserve tuples by checking implication****************************")
        cursor = self._conn.cursor()

        # if 'id' not in self.column_datatype_mapping:
        cursor.execute("ALTER TABLE {} ADD COLUMN if not exists id SERIAL PRIMARY KEY;".format(self.output_table))
        #self._conn.commit()

        select_sql = "select old_conditions, conjunction_condition, id from {}".format(self.output_table) 
        if self._information_on:
            print(select_sql)
        
        cursor.execute(select_sql)

        count_num = cursor.rowcount
        data_tuples = cursor.fetchall()
        #self._conn.commit()

        
        update_tuples = []
        for i in range(count_num):
            (old_conditions, conjunctin_conditions, id) = data_tuples[i]
            
            old_cond = None
            # old_conditions = [item for subconditions in old_conditions for item in subconditions]
            if old_conditions == None or len(old_conditions) == 0:
                old_cond = "1 == 1"
            elif len(old_conditions) == 1:
                old_cond = old_conditions[0]
            else:
                old_cond = "And({})".format(", ".join(old_conditions))

            if self._reasoning_tool.is_implication(old_cond, conjunctin_conditions): # all possible instances are matched the program
                update_tuples.append((id, [old_cond, conjunctin_conditions]))
            
        
        cursor.execute("create temp table if not exists temp_update(uid integer, condition text[])")
        cursor.execute("truncate temp_update") # if exists, truncate temp_update table
        execute_values(cursor, "insert into temp_update values %s", update_tuples)

        
        sql = "SELECT column_name FROM information_schema.columns where table_name = '{}';".format(self.output_table.lower())
        cursor.execute(sql)
        columns_without_condition = [name for (name, ) in cursor.fetchall() if 'condition' not in name and 'id' not in name]

        sql = "create table temp_{} as select {}, t2.condition as condition from {} t1, temp_update t2 where t1.id = t2.uid".format(self.output_table, ", ".join(columns_without_condition), self.output_table)
        cursor.execute(sql)

        cursor.execute("drop table if exists {}".format(self.output_table))
        cursor.execute("alter table temp_{output} rename to {output}".format(output=self.output_table))
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
    # conn = psycopg2.connect(
    #     host=cfg.postgres["host"], 
    #     database=cfg.postgres["db"], 
    #     user=cfg.postgres["user"], 
    #     password=cfg.postgres["password"])

    # domains = {
    #     'd1':['1', '2'],
    #     'd2':['1', '2'],
    #     'd':['1', '2']
    # }
    # # domains = {
    # #     'd1':['10.0.0.1', '10.0.0.2'],
    # #     'd2':['10.0.0.1', '10.0.0.2'],
    # #     'd':['10.0.0.1', '10.0.0.2']
    # # }
    # # sql = "select t3.a1 as a1, t1.a2 as a2 from R t1, R t2, L t3, L t4 where t1.a1 = t3.a2 and t2.a1 = t4.a2 and t3.a1 = t4.a1 and t1.a2 = '10.0.0.1'"
    # sql = "select t3.a1 as a1, t1.a2 as a2 from R t1, R t2, L t3, L t4 where t1.a1 = t3.a2 and t2.a1 = t4.a2 and t3.a1 = t4.a1 and (t1.a2 = '1' or t1.a2 = '2');"
    # FaureEvaluation(conn, sql, additional_condition="d != 2", databases={}, domains=domains, reasoning_engine='z3', reasoning_sort='Int', simplication_on=False, information_on=True)
    z3smt = z3SMTTools(variables=['x'], domains={}, reasoning_type={})
    conn = psycopg2.connect(
        host=cfg.postgres["host"], 
        database=cfg.postgres["db"], 
        user=cfg.postgres["user"], 
        password=cfg.postgres["password"])

    # sql = "SELECT t1.n1 as n1, t2.n2 as n2 FROM R t1, L t2 WHERE t1.n2 = t2.n1"
    sql = "select t0.c0 as c0 from R t0, R t1 where t0.c0 = t1.c0 and (t0.c0 > 2 And (t0.c0 > 2 And (t0.c0 < 7 And t0.c0 < 7))) and (t0.c0 > 0 And (t0.c0 > 0 And t0.c0 < 10))"
    # additional_condition = "And(y == 1, x == 2)"
    additional_condition = None
    FaureEvaluation(conn, sql, reasoning_tool=z3smt, additional_condition=additional_condition, databases={}, reasoning_engine='z3', reasoning_sort={}, simplication_on=False, information_on=True, mode='implication')


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


    