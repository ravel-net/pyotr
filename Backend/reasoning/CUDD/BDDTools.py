# BDD manager Module
import BDD_managerModule as bddmm
import Backend.reasoning.CUDD.BDD_manager.encodeCUDD as encodeCUDD
from tqdm import tqdm
import time
from copy import deepcopy
from psycopg2.extras import execute_values

class BDDTools:

    def __init__(self, variables, domains={}, reasoning_type='Int') -> None:
        # assume all variables have the same domain
        # if len(domains.keys()) == 0:
        #     print("Domain is empty!")
        #     exit()

        self.variables = variables
        # self.domain_list =  domains[variables[0]]
        self.domain_list =  domains
        self._reasoning_sort = reasoning_type
        self._is_IP = False
        self._empty_condition_idx = None

        if self._reasoning_sort.lower() == 'bitvec':
            self._is_IP = True
            # bddmm.initialize(len(variables)) # the domain of IP address is 2^32
        # else:
        # print("variables", variables)
        upd_variables = encodeCUDD.getUpdatedVariables(variables, domains, self._is_IP)
        bddmm.initialize(len(upd_variables))

        # condition1 = "And(d1 == 5, d2 == 1)"
        
        # encoded_c, upd_variables = encodeCUDD.convertToCUDD(condition1, self.domain_list, self.variables, self._is_IP)
        # print(encoded_c)
        # idx = bddmm.str_to_BDD(encoded_c)
        # print(idx)
    
    def str_to_BDD(self, condition):
        print("condition", condition)
        encoded_c, variablesArray = encodeCUDD.convertToCUDD(condition, self.domain_list, self.variables, self._is_IP)
        print("variablesArray", variablesArray)
        print("encoded_c", encoded_c)
        bdd_condition_idx = bddmm.str_to_BDD(encoded_c)
        return bdd_condition_idx

    def operate_BDDs(self, bdd_idx1, bdd_idx2, operator):

        result_idx = bddmm.operate_BDDs(int(bdd_idx1), int(bdd_idx2), operator)

        return result_idx
    
    def is_implication(self, bdd_idx1, bdd_idx2):
        if bddmm.is_implication(bdd_idx1, bdd_idx2) == 1:
            return True
        else:
            return False

    def evaluate(self, bdd_idx):
        return bddmm.evaluate(bdd_idx)

    def process_condition_on_ctable(self, conn, tablename):
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
        cursor = conn.cursor()

        cursor.execute("SELECT column_name FROM information_schema.columns WHERE table_name = '{}';".format(tablename.lower())) # this SQL needs lowercase of tablename
        columns = []
        for (column_name, ) in cursor.fetchall():
            columns.append(column_name.lower())
        conn.commit()

        '''
        locate condition
        '''
        cond_idx = -1
        
        if 'condition' in columns:
            cond_idx = columns.index('condition')
        else:
            print("No condition column! Check if the target table is correct!")
            exit()

        cursor.execute("select {attributes} from {tablename}".format(attributes=", ".join(columns), tablename=tablename))

        count_num = cursor.rowcount

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
                    empty_condition_idx = self.str_to_BDD(condition)
                    end_process_strToBDD = time.time()
                    # if self._information_on:
                    #     print("Time to str_to_BDD in condition {}: {} s".format(empty_condition_idx, end_process_strToBDD-begin_process))
                    self._empty_condition_idx = empty_condition_idx
                list_row[cond_idx] = self._empty_condition_idx
            else:
                condition = ", ".join(list_row[cond_idx])

                # Call BDD module 
                begin_process = time.time()
                bdd_idx = self.str_to_BDD(condition)
                end_process_strToBDD = time.time()
                # if self._information_on:
                #     print("Time to str_to_BDD in condition {}: {} s".format(bdd_idx, end_process_strToBDD-begin_process))
                list_row[cond_idx] = bdd_idx

            row = tuple(list_row)
            new_tuples.append(deepcopy(row))
        
        # truncate content in target table
        sql = "truncate table {tablename}".format(tablename=tablename)
        cursor.execute(sql)

        # alter table condition column's datatype from text[] to integer
        sql = "alter table if exists {tablename} drop column if exists condition".format(tablename=tablename)
        cursor.execute(sql)

        sql = "alter table if exists {tablename} add column IF NOT EXISTS condition integer".format(tablename=tablename)
        cursor.execute(sql)

        sql = "insert into {tablename} values %s".format(tablename=tablename)
        execute_values(cursor, sql, new_tuples)
        # cursor.executemany(new_tuples)
        conn.commit()