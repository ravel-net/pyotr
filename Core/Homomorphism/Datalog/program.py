import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
import psycopg2 
from psycopg2.extras import execute_values
from copy import deepcopy
from Core.Homomorphism.Datalog.rule import DT_Rule
from Core.Homomorphism.Datalog.DL_minimization import minimizeAtoms, minimizeRules, enhancedMinimization
from Backend.reasoning.Z3.z3smt import z3SMTTools
from Backend.reasoning.CUDD.BDDTools import BDDTools
from Core.Homomorphism.faure_translator.faure_evaluation import FaureEvaluation
import Core.Homomorphism.Optimizations.merge_tuples.merge_tuples_tautology as merge_tuples_z3
import databaseconfig as cfg
import time
import logging
logging.basicConfig(filename='program.log', level=logging.DEBUG)
logging.debug('[Program] Start Logging ...')

class DT_Program:
    """
    A class used to represent a datalog program.

    Attributes
    ----------
    __MAX_ITERATIONS : int
        the maximum number of times a datalog program should be run (in case fixed point isn't reached)
    __OPERATORS : string[]
        operators supported in queries. Currently, only array concatination operator "||" is supported
    _rules : DT_Rule[]
        array of datalog rules


    Methods
    -------
    contains(program2)
        does this program uniformly contain program2?
    minimize()
        minimize this datalog program
    execute(conn)
        run this datalog program on database pointed by psycopg2 connection "conn"
    initiateDB(conn)
        initiate tables in this datalog program on database pointed by psycopg2 connection "conn"
    contained_by_rule(rule2)
        does rule2 uniformly contain this program?
    """
    
    __MAX_ITERATIONS = 10
    __OPERATORS = ["||"]
    
    # databaseTypes is a dictionary {"database name":[ordered list of column types]}. By default, all column types are integers. If we need some other datatype, we need to specify using this parameter
    def __init__(self, program_str, databaseTypes={}, domains=[], c_variables=[], reasoning_engine='z3', reasoning_type='Int', datatype='Integer', simplification_on=False, c_tables=[]):
        logging.info("Initiating program: \n" + program_str)
        start = time.time()
        self._rules = []
        # IMPORTANT: The assignment of variables cannot be random. They have to be assigned based on the domain of any c variable involved
        self._program_str = program_str
        self._databaseTypes = databaseTypes
        self._domains = domains
        self._c_variables = c_variables
        self._reasoning_engine = reasoning_engine
        self._reasoning_type = reasoning_type
        self._datatype = datatype
        self._simplification_on = simplification_on
        self._c_tables = c_tables
        self.z3tools = z3SMTTools(variables=c_variables,domains=domains, reasoning_type=reasoning_type)

        if isinstance(program_str, DT_Rule):
            self._rules.append(program_str)
        else:
            rules_str = program_str.split("\n")
            for rule in rules_str:
                self._rules.append(DT_Rule(rule, databaseTypes, self.__OPERATORS, domains, c_variables, reasoning_engine, reasoning_type, datatype, simplification_on, c_tables))
        end = time.time()
        logging.info("Time: init took {}".format(end-start))
    # def __eq__(self, other):
    #     return True if self._account_number == other._account_number else False
    
    def __str__(self):
        DT_Program_str = ""
        for rule in self._rules:
            DT_Program_str += str(rule) + "\n"
        return DT_Program_str[:-1] # removing the last \n
    
    # Uniform containment. self C dt_program2 (self program contains dt_program2)
    def contains(self, dt_program2):
        # consider rules in dt_program2 one by one, i.e., self contains rule1 of dt_program2, self contains rule2 of dt_program2, ...
        logging.info("Calling contains")
        start = time.time()
        for rule in dt_program2._rules:
            if not self.contains_rule(rule):
                end = time.time()
                logging.info("Time: contains returned False and took {}".format(end-start))
                return False
        end = time.time()
        logging.info("Time: contains returned true and took {}".format(end-start))
        return True

    def execute(self, conn):
        # # program_sql = "WITH recursive temp_G(c0, c1, c2, condition, depth) AS (\
        # #                     select c0, c1, c2, condition, 1 as depth from G\
        # #                     UNION\
        # #                     select t1.c0 as c0, t2.c1 as c1, t3.c1 as c2, \
        # #                         t1.condition || t2.condition || t3.condition || t4.condition || t5.condition ||\
        # #                         Array[\
        # #                             t1.c1 || ' == ' || t2.c0,\
        # #                             t2.c0 || ' == ' || t3.c0,\
        # #                             t1.c2 || ' == ' || t3.c1,\
        # #                             t3.c1 || ' == ' || t4.c0,\
        # #                             t4.c0 || ' == ' || t4.c1,\
        # #                             t4.c1 || ' == ' || t5.c0,\
        # #                             t2.c1 || ' == ' || t5.c1\
        # #                         ] as condition,\
        # #                         t1.depth+1 as depth\
        # #                     from temp_G t1, A t2, A t3, A t4, A t5\
        # #                     where t1.c1 = t2.c0 \
        # #                         and t2.c0 = t3.c0 \
        # #                         and t1.c2 = t3.c1 \
        # #                         and t3.c1 = t4.c0 \
        # #                         and t4.c0 = t4.c1 \
        # #                         and t4.c1 = t5.c0 \
        # #                         and t2.c1 = t5.c1\
        # #                         and depth < 3\
        # #                     )\
        # #                     insert into G select c0, c1, c2, condition from temp_G;"
        # # program_sql = "WITH RECURSIVE temp_R(c0, c1, depth, condition) AS (\
        # #                     SELECT c0, c1, 1, condition from L\
        # #                     UNION\
        # #                     SELECT t1.c0 as c0, t2.c1 as c1, depth+1 as depth, t1.condition || t2.condition || Array[t1.c1 || ' == ' || t2.c0] as condition\
        # #                     FROM temp_R t1, L t2\
        # #                     WHERE t1.c1 = t2.c0 and depth < 2\
        # #                 )\
        # #                 insert into R SELECT c0, c1, condition from temp_R;"
        # program_sql = "WITH recursive temp_G(c0, c1, c2) AS (\
        #                 select c0, c1, c2 from G0\
        #                 UNION\
        #                 select t1.c0 as c0, t2.c1 as c1, t3.c1 as c2\
        #                 from temp_G t1, A t2, A t3, A t4, A t5\
        #                 where t1.c1 = t2.c0 \
        #                     and t2.c0 = t3.c0 \
        #                     and t1.c2 = t3.c1 \
        #                     and t3.c1 = t4.c0 \
        #                     and t4.c0 = t4.c1 \
        #                     and t4.c1 = t5.c0 \
        #                     and t2.c1 = t5.c1\
        #                 )\
        #                 insert into G select c0, c1, c2 from temp_G;"
        # print("program_sql", program_sql)
        # # table = "G"
        # # eval_time = time.time()
        # # FaureEvaluation(conn, program_sql, output_table=table, domains=self._domains, reasoning_engine=self._reasoning_engine, reasoning_sort=self._reasoning_type, simplication_on=False, information_on=False)
        # # eval_end = time.time()
        

        # # # input()
        # # # delete redundants
        # # merge_begin = time.time()
        # # num = merge_tuples_z3.merge_tuples(table, # tablename of header
        # #                             "{}_out".format(table), # output tablename
        # #                             self.z3tools, # reasoning type of engine
        # #                             simplification_on=self._simplication_on,
        # #                             information_on=False
        # #                             ) 
        # # merge_end = time.time()
        # # print("**********************\nevaluation time:", eval_end-eval_time, "\n***************************************\n")
        # # print("count: ", num, "merging time:", merge_end-merge_begin, "\n**********************\n")

        # # return False
        # program_sql = "WITH RECURSIVE temp_R(c0, c1) AS (\
        #                 SELECT * from L \
        #                 UNION \
        #                 SELECT t1.c0 as c0, t2.c1 as c1 \
        #                 FROM temp_R t1, L t2\
        #                 WHERE t1.c1 = t2.c0\
        #             )\
        #             insert into R SELECT * from temp_R;"
        # cursor = conn.cursor()
        # cursor.execute(program_sql)
        # conn.commit()
        # return False
        logging.info("Calling execute")
        start = time.time()
        changed = False
        for rule in self._rules:
            print("\n------------------------")
            print("executing rule:", rule)
            DB_changes = rule.execute(conn)
            changed = changed or DB_changes
        end = time.time()
        logging.info("Time: execute took {}".format(end-start))
        return changed




    def initiateDB(self, conn):
        logging.info("Calling initiateDB")
        start = time.time()
        databases = []
        db_names = []
        for rule in self._rules:
            for db in rule.getDBs:
                if db["name"] not in db_names:
                    db_names.append(db["name"])
                    databases.append(db)

        for db in databases:
            cursor = conn.cursor()
            cursor.execute("DROP TABLE IF EXISTS {};".format(db["name"]))
            table_creation_query = "CREATE TABLE {}(".format(db["name"])
            num_cols = len(db["column_names"]) # assuming that last column is always condition
            for col in range(num_cols): 
                table_creation_query += '{} {},'.format(db["column_names"][col], db["column_types"][col])
            table_creation_query = table_creation_query[:-1]
            table_creation_query += ");"
            # print(table_creation_query)
            cursor.execute(table_creation_query)
        conn.commit()
        end = time.time()
        logging.info("Time: initiateDB took {}".format(end-start))



    # Uniform containment. 
    # self contains one rule of dt_program2
    def contains_rule(self, rule2):
        logging.info("Calling contains_rule")
        start = time.time()
        conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
        conn.set_session()
        changed = True
        self.initiateDB(conn)

        # num = 100
        # tuples = []

        # for i in range(num):
        #     # tuples.append(["x"+str(i), "x"+str(i+1), "{}"])
        #     tuples.append([i, i+1])
        
        # cursor = conn.cursor()
        # execute_values(cursor, "insert into L values %s", tuples)
        # conn.commit()

        rule2.addConstants(conn)
        iterations = 0
        while (changed and iterations < self.__MAX_ITERATIONS): # run until a fixed point reached or MAX_ITERATION reached
            iterations += 1
            changed = self.execute(conn)
            if self._simplification_on and self._reasoning_engine == 'z3':
                simp_begin = time.time()
                self.z3tools.simplification(rule2._head.db["name"], conn)
                simp_end = time.time()
                logging.info("Time: simplification_time: {}".format(simp_end-simp_begin))
                # input()
        
            check_head_begin = time.time()
            if rule2.isHeadContained(conn):
                check_head_end = time.time()
                logging.info("Time: checking_head: {}".format(check_head_end-check_head_begin))
                end = time.time()
                logging.info("Time: contains_rule took {}".format(end-start))
                return True
            check_head_end = time.time()
            logging.info("Time: checking_head: {}".format(check_head_end-check_head_begin))
        end = time.time()
        logging.info("Time: contains_rule took {}".format(end-start))
        return False

    # Takes a newRules (a list of rules as strings) as input, and replaces the current program with the new rules
    def replaceProgram(self, newRules):
        logging.info("Calling replaceProgram")
        start = time.time()
        newProgram = DT_Program(program_str="\n".join(newRules), databaseTypes=self._databaseTypes, domains=self._domains, c_variables=self._c_variables, reasoning_engine=self._reasoning_engine, reasoning_type=self._reasoning_type, datatype=self._datatype, simplification_on=self._simplification_on, c_tables=self._c_tables)
        # newObj = func(newProgram)
        self.__dict__.update(newProgram.__dict__)
        end = time.time()
        logging.info("Time: replaceProgram took {}".format(end-start))

    def replaceRule(self, ruleNum, newRule):
        logging.info("Calling replaceRule")
        start = time.time()
        self._rules[ruleNum] = newRule
        end = time.time()
        logging.info("Time: replaceRule took {}".format(end-start))

    def deleteRule(self, ruleNum):
        logging.info("Calling deleteRule")
        start = time.time()
        self._rules.pop(ruleNum)
        end = time.time()
        logging.info("Time: deleteRule took {}".format(end-start))

    def copyWithDeletedRule(self, ruleNum):
        logging.info("Calling copyWithDeletedRule")
        start = time.time()
        newProgram = deepcopy(self)
        newProgram.deleteRule(ruleNum)
        end = time.time()
        logging.info("Time: copyWithDeletedRule took {}".format(end-start))
        return newProgram
        

    # minimize. Does minimization in place. Make sure to make a copy if you want the original program
    #TODO IMPORTANT: Program only rule should be entire program. Method: Delete contained rule and then add a rule without atom
    def minimize(self, minimizeAtomsOn = True, minimizeRulesOn = True, enhancedMinimizationOn = False):
        if minimizeAtomsOn:
            logging.info("Calling minimizeAtomsOn")
            start = time.time()
            minimizeAtoms(self)
            end = time.time()
            logging.info("Time: minimizeAtomsOn took {}".format(end-start))
        if minimizeRulesOn:
            logging.info("Calling minimizeRules")
            start = time.time()
            minimizeRules(self)
            end = time.time()
            logging.info("Time: minimizeRules took {}".format(end-start))
        if enhancedMinimizationOn:
            logging.info("Calling enhancedMinimization")
            start = time.time()
            enhancedMinimization(self)
            end = time.time()
            logging.info("Time: enhancedMinimization took {}".format(end-start))
    
    @property
    def numRules(self):
        return len(self._rules)

    def getRule(self, ruleNum):
        return self._rules[ruleNum]