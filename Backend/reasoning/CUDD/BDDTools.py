# BDD manager Module
import BDD_managerModule as bddmm
import Backend.reasoning.CUDD.BDD_manager.encodeCUDD as encodeCUDD
from tqdm import tqdm
import time
from copy import deepcopy
from psycopg2.extras import execute_values
from utils.logging import timeit
from Core.Datalog.conditionTree import ConditionTree
from utils import parsing_utils

def singleton(cls, *args, **kw):
    instances = {}
    def _singleton(*args, **kw):
        if cls not in instances:
            instances[cls] = cls(*args, **kw)
        return instances[cls]
    return _singleton

@singleton
class BDDTools:
    ########@timeit
    def __init__(self, variables, domains={}, reasoning_types={}, mapping = {}, bits = 32) -> None:
        # assume all variables have the same domain
        # if len(domains.keys()) == 0:
        #     print("Domain is empty!")
        #     exit()

        self.variables = variables
        self.varToIntMapping = {}
        # self.domain_list =  domains[variables[0]]
        self.domain_list =  domains
        self._is_IP = False
        self.bits = bits
        self._mapping = mapping
        self._empty_condition_idx = None
        self.name = "bdd"

            # bddmm.initialize(len(variables)) # the domain of IP address is 2^32
        # else:
        # print("variables", variables)
        upd_variables = encodeCUDD.getUpdatedVariables(variables, domains, self._is_IP, self.bits)
        bddmm.initialize(len(upd_variables))

        # since variables are represented by integers, we pre-compute the mapping from the variables array
        count = 2 # starting from 2 since 0 and 1 are reserved for true and false
        for var in upd_variables:
            self.varToIntMapping[var] = str(count)
            count += 1

    # @timeit
    def encodeCond(self, condition):
        conditionTree = ConditionTree(condition).toString(mode = "Replace String", replacementDict=self._mapping)
        conditionTreeReplaced = ConditionTree(conditionTree)
        if conditionTreeReplaced.getIsTrue():
            encoded_c = "(1)"
        else:
            encoded_c = conditionTreeReplaced.toString(mode = "BDD", replacementDict = self.varToIntMapping, bits = self.bits)
        encoded_c = encoded_c.replace(" ","")
        return encoded_c
    
    def print_dd(self, bdd_idx1):
        return bddmm.print_dd(bdd_idx1)

    # @timeit
    def str_to_engine(self, condition):
        encoded_c = self.encodeCond(condition)
        bdd_condition_idx = bddmm.str_to_BDD(encoded_c)
        return bdd_condition_idx

    ########@timeit
    def operate(self, bdd_idx1, bdd_idx2, operator):
        result_idx = bddmm.operate_BDDs(int(bdd_idx1), int(bdd_idx2), operator)
        return result_idx
    
    def transform(self, bdd_idx1, bdd_idx2, bdd_idx3):
        # print("Transformer called. Exiting")
        # exit()
        result_idx = bddmm.transform_BDDs(int(bdd_idx1), int(bdd_idx2), int(bdd_idx3))
        return result_idx
    
    ########@timeit
    def is_implication(self, bdd_idx1, bdd_idx2):
        if bddmm.is_implication(bdd_idx1, bdd_idx2) == 1:
            return True
        else:
            return False

    ########@timeit
    def evaluate(self, bdd_idx):
        return bddmm.evaluate(bdd_idx)

    ########@timeit
    def is_equivalent(self, bdd_idx1, bdd_idx2):
        return self.is_implication(bdd_idx1, bdd_idx2) and self.is_implication(bdd_idx2, bdd_idx1)

    def iscontradiction(self, condition):
        # if len(condition) != 1:
        #     print("Is contradiction with bdd should only be called with one condition. Condition {} is not acceptable. Exiting".format(condition))
        #     exit()
        result = self.evaluate(int(condition))
        if str(result) == '0':
            return True
        else:
            return False
    
    # @timeit
    def process_condition_on_ctable(self, conn, tablename):
        """
        convert text condition to BDD reference in a c-table

        Parameters:
        -----------
        conn:
            psycopg2 connection to database

        tablename: string
            the tablename of c-table
        """
        cursor = conn.cursor()

        # get column names
        cursor.execute("SELECT column_name FROM information_schema.columns WHERE table_name = '{}';".format(tablename.lower())) # this SQL needs lowercase of tablename
        columns = []
        for (column_name, ) in cursor.fetchall():
            columns.append(column_name.lower())

        '''
        locate column index of condition and transformer
        '''
        cond_idx = -1
        
        if 'condition' in columns:
            cond_idx = columns.index('condition')
        else:
            print("No condition column! Check if the target table is correct!")
            exit()

        if 'transformer' in columns:
            trans_idx = columns.index('transformer')
        else:
            trans_idx = -1

        # loads table in memory. TODO: We only need to load condition and transformer columns. This could be made more efficient
        cursor.execute("select {attributes} from {tablename}".format(attributes=", ".join(columns), tablename=tablename))

        '''
        Loop over table and converts conditions into indexes
        '''
        count_num = cursor.rowcount
        new_tuples = []
        for i in tqdm(range(count_num)):
            row = cursor.fetchone()
            list_row = list(row)
            if len(list_row[cond_idx]) == 0:
                # list_row[cond_idx] = None
                if self._empty_condition_idx is None:
                    condition = ""
                    empty_condition_idx = self.str_to_engine(condition)
                    self._empty_condition_idx = empty_condition_idx
                list_row[cond_idx] = "{" + str(self._empty_condition_idx) + "}"
            else:
                condition = ", ".join(list_row[cond_idx])
                # Call BDD module 
                bdd_idx = self.str_to_engine(condition)
                list_row[cond_idx] = "{" + str(bdd_idx) + "}"

            if trans_idx != -1 and len(list_row[trans_idx]) != 0: # for transformer, each condition will have two bdds. (1) actual rewriting BDD, (2) Same BDD but with all ones where we need to rewrite. Note that the user has to make sure to provide both conditions, because bdd backend is agnostic to how the conditions are provided
                transformerConditions = list_row[trans_idx]
                transformerBDDIdxes = []
                for condition in transformerConditions:
                    bdd_idx = self.str_to_engine(condition)
                    transformerBDDIdxes.append(str(bdd_idx))
                    onesCondition = parsing_utils.convertToAllOnes(condition) # e.g. *1001*0 is converted to *1111*1
                    bdd_idx2 = self.str_to_engine(onesCondition)
                    transformerBDDIdxes.append(str(bdd_idx2))
                list_row[trans_idx] = "{" + ",".join(transformerBDDIdxes) + "}"
            row = tuple(list_row)
            new_tuples.append(deepcopy(row))
        
        # truncate content in target table
        sql = "truncate table {tablename};".format(tablename=tablename)

        # drop condition column
        sql += "alter table if exists {tablename} drop column if exists condition;".format(tablename=tablename)

        # drop transformer column
        if trans_idx != -1:
            sql += "alter table if exists {tablename} drop column if exists transformer;".format(tablename=tablename)

            sql += "alter table if exists {tablename} add column IF NOT EXISTS transformer text[];".format(tablename=tablename)

        sql += "alter table if exists {tablename} add column IF NOT EXISTS condition text[];".format(tablename=tablename)
        cursor.execute(sql)


        sql = "insert into {tablename} values %s".format(tablename=tablename)
        execute_values(cursor, sql, new_tuples)
        # cursor.executemany(new_tuples)
        # conn.commit()