"""
This is for generate policy data 
"""
import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
import math
import psycopg2
from psycopg2.extras import execute_values
import databaseconfig as cfg
from Core.Datalog.program import DT_Program
from Core.Datalog.database import DT_Database
import time
from Core.Datalog.table import DT_Table
import random
import numpy as np

DATABASE = cfg.postgres['db']
HOST = cfg.postgres['host']
USER = cfg.postgres['user']
PASSWORD = cfg.postgres['password']

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

def generate_policy1(size):
    """
    policy 1 includes static routing policy and filter policy
    """
    path_base = 40000
    address_base = 10000
    tuples = []

    count = math.ceil(size / 2) # half for static routing policy

    # static policy: [1.2.3.4, x, [x == 1.2.3.4]]
    for i in range(count):
        c_var = "{}".format(i-1000000)
        path = path_base + i
        addr = address_base + i
        
        condition = "{} == {}".format(c_var, path)
        t = [addr, c_var, [condition]]
        tuples.append(t)

    # filter policy [y, z, [y != 1.2.3.5]]
    for i in range(count, size):
        c_var1 = "{}".format(i-2000000)
        c_var2 = "{}".format(i-3000000)
        addr = address_base + i

        condition = "{} != {}".format(c_var1, addr)
        t = [c_var1, c_var2, [condition]]
        tuples.append(t)

    # for i in range(0, size):
    #     num1 = random.randrange(1,size*10)
    #     num2 = random.randrange(1,size*10)
    #     t = [num1, num2, [""]]
    #     tuples.append(t)

    return tuples

def generate_policy3(size, numPaths, mode = "normal"):
    """
    policy 3 is load balance policy
    """
    address_base = 20000

    tuples = []
    for i in range(0, size, 2):
        addr1 = address_base + i
        addr2 = address_base + i + 1

        path1 = i % numPaths
        path2 = path1 + 1
        if path2 >= numPaths:
            path2 = 0

        c_var = "{}".format(i-4000000)
        if mode == "faure":
            c_var = "u{}".format(i) 
            
        # c_var2 = "v{}".format(i)

        # t1 = [addr1, path1, c_var1, ["{} == 1".format(c_var1), "{} != 1".format(c_var2)]]
        # t2 = [addr1, path2, c_var1, ["{} != 1".format(c_var1), "{} == 1".format(c_var2)]]
        # t3 = [addr2, path1, c_var2, ["{} == 1".format(c_var2), "{} != 1".format(c_var1)]]
        # t4 = [addr2, path2, c_var2, ["{} != 1".format(c_var2), "{} == 1".format(c_var1)]]

        # t1 = [addr1, c_var, min(path1, path2), max(path1,path2), ["Or({} == {}, {} == {})".format(c_var,path2,c_var,path1)]]
        # t2 = [addr2, path1, path1, path1, ["{} == {}".format(c_var, path2)]]
        # t3 = [addr2, path2, path2, path2, ["{} == {}".format(c_var, path1)]]

        t1 = [addr1, c_var, ["Or({} == {}, {} == {})".format(c_var,path2,c_var,path1)]]
        t2 = [addr2, path1, ["{} == {}".format(c_var, path2)]]
        t3 = [addr2, path2, ["{} == {}".format(c_var, path1)]]

        tuples += [t1, t2, t3]
    return tuples

def store_tables(tablename, attribute_names, datatypes, data):
    conn = psycopg2.connect(host=HOST, database=DATABASE, user=USER, password=PASSWORD)

    cursor = conn.cursor()

    cursor.execute("drop table if exists {}".format(tablename))

    attr_type_pairs = ["{} {}".format(attribute_names[i], datatypes[i])for i in range(len(attribute_names))]
    cursor.execute("create table {} ({})".format(tablename, ", ".join(attr_type_pairs)))

    execute_values(cursor, "insert into {} values %s".format(tablename), data)

    conn.commit()
    conn.close()

# conditions of the form [("dest","> 20000"), ("path","< 100"),...]
def selectQueries(table, mode, conditions):
    if (mode == "faure" and "faure" not in table) or (mode != "faure" and "faure" in table):
        print("Error: Table name is {} in mode {}".format(table, mode))
        exit()
    
    conditionalColumnAdd = False

    conditionalColumn = "Array['And(' || "
    for conditionTuple in conditions[:-1]:
        conditionalColumn += conditionTuple[0] 
        conditionalColumn += " || " + "'{},' || ".format(conditionTuple[1]) 
    conditionTuple = conditions[-1]
    conditionalColumn += conditionTuple[0] 
    conditionalColumn += " || " + "'{})']".format(conditionTuple[1]) 

    condition_part = "("
    for conditionTuple in conditions[:-1]:
        if mode == "faure":
            condition_part += conditionTuple[0] + conditionTuple[1]
            condition_part += " and "
        else:
            condition_part += "({} {} or {} < 0)".format(conditionTuple[0],conditionTuple[1],conditionTuple[0])
            condition_part += " and "
    conditionTuple = conditions[-1]
    if mode == "faure":
        condition_part += conditionTuple[0] + conditionTuple[1]
        condition_part += ")"
    else:
        condition_part += "({} {} or {} < 0)".format(conditionTuple[0],conditionTuple[1],conditionTuple[0])
        condition_part += ")"

    if conditionalColumnAdd:
        sql1 = "select dest, path, condition || {} from {} where {}".format(conditionalColumn, table, condition_part)
    else:
        sql1 = "select dest, path from {} where {}".format(table, condition_part)
    return sql1
    
# Make the variable conditionalColumnAdd in function selectQueries to True if you want to add conditions.
if __name__ == '__main__':
    mode = sys.argv[1]
    size = 100 # 10,000,000
    paths = 5

    p3_data = generate_policy3(size, paths, mode)
    start = time.time()
    if (mode == "faure"):
        store_tables("p3_faure", ["dest", "path", "condition"], ["int4_faure", "int4_faure", "text[]"], p3_data)
    else:
        store_tables("p3", ["dest", "path", "condition"], ["integer", "integer", "text[]"], p3_data)
    end = time.time()
    print("Store Time p3_{}:{}".format(mode,end-start))

    # p3_data = generate_policy3(size, paths, mode)
    # start = time.time()
    # if (mode == "faure"):
    #     store_tables("p3_faure", ["dest", "path", "min", "max", "condition"], ["int4_faure", "int4_faure","integer", "integer","text[]"], p3_data)
    # else:
    #     store_tables("p3", ["dest", "path", "min", "max", "condition"], ["integer", "integer", "integer", "integer", "text[]"], p3_data)
    # end = time.time()
    # print("Store Time p3_{}:{}".format(mode,end-start))
    

    cursor = conn.cursor()
    conditions = [("dest"," >= 20000"),("dest"," < 30000")] #query2 small
    # conditions = [("dest"," >= 1000000"),("dest"," < 2000000")] #query2
    # conditions = [("path"," >= 1"),("path"," < 3")] # query1

    # cursor.execute("CREATE INDEX idx_p1_path ON p1 using BRIN(path);")
    # cursor.execute("CREATE INDEX idx_p1_dest ON p1 using BRIN(dest);")

    # cursor.execute("CREATE INDEX idx_p2_path ON p3(path);")
    # cursor.execute("CREATE INDEX idx_p2_dest ON p3(dest);")
    # cursor.execute("CREATE INDEX idx_p2_path1 ON p3(min);")
    # cursor.execute("CREATE INDEX idx_p2_dest1 ON p3(max);")
    # cursor.execute("CREATE INDEX idx_p3_path ON p3 using brin(path);")
    # cursor.execute("CREATE INDEX idx_p3_dest ON p3 using brin(dest);")
    # conn.commit()

    # cursor.execute("CREATE INDEX idx_p1_dest ON p1(dest);")
    # cursor.execute("CREATE INDEX idx_p2_dest ON p3(dest);")

    if (mode == "faure"):
        sql1 = selectQueries("p3_faure", mode, conditions)
    else:
        sql1 = selectQueries("p3", mode, conditions)

    # sql1 = "select dest,path,condition from p3 where ((path < 0 and min >= 1 and max < 3) or (path >= 1 and path < 3));"

    print(sql1)
    iterations = 1
    times = []
    for i in range(iterations):
        start = time.time()
        cursor.execute(sql1)
        end = time.time()
        times.append(end-start)
        # a = cursor.fetchall()
        # print(a)
        # print("Length:", len(cursor.fetchall()))
    print("Average Time Taken in {} runs: {}".format(iterations, np.mean(times)))

    # p1 = "R(a,b) :- p1(a,b), p3(a,b)"
    # # program1 = DT_Program(p1, database, optimizations={"simplification_on":True})
    # program1 = DT_Program(p1, database)
    # program1.execute(conn)

