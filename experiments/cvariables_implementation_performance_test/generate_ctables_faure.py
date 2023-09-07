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
        c_var = "x{}".format(i)
        path = path_base + i
        addr = address_base + i
        
        condition = "{} == {}".format(c_var, path)
        t = [addr, c_var, [condition]]
        tuples.append(t)

    # filter policy [y, z, [y != 1.2.3.5]]
    for i in range(count, size):
        c_var1 = "y{}".format(i)
        c_var2 = "z{}".format(i)
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

def generate_policy3(size, numPaths):
    """
    policy 3 is load balance policy
    """
    address_base = 20000
    path_base = 50000
    tuples = []
    for i in range(0, size, 2):
        addr1 = address_base + i
        addr2 = address_base + i + 1

        path1 = i % numPaths
        path2 = path1 + 1
        if path2 >= numPaths:
            path2 = 0

        c_var = "u{}".format(i)
        # c_var2 = "v{}".format(i)

        # t1 = [addr1, path1, c_var1, ["{} == 1".format(c_var1), "{} != 1".format(c_var2)]]
        # t2 = [addr1, path2, c_var1, ["{} != 1".format(c_var1), "{} == 1".format(c_var2)]]
        # t3 = [addr2, path1, c_var2, ["{} == 1".format(c_var2), "{} != 1".format(c_var1)]]
        # t4 = [addr2, path2, c_var2, ["{} != 1".format(c_var2), "{} == 1".format(c_var1)]]

        t1 = [addr1, c_var, ["Or({} == {}, {} == {})".format(c_var,path2,c_var,path1)]]
        t2 = [addr2, path1, ["{} == {}".format(c_var, path2)]]
        t3 = [addr2, path2, ["{} == {}".format(c_var, path1)]]

        tuples += [t1, t2, t3]

    # for i in range(0, math.ceil(size/2)):
    #     num1 = random.randrange(1,size*10)
    #     num2 = random.randrange(1,size*10)
    #     t = [num1, num2, [""]]
    #     tuples += t

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

def joinQuery():
  ############################### size = 100000 ######################################
    # 16.67 seconds
    sql1 = "select t0.dest as dest, t0.path as path from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path) and t0.path > 10000;"

    # 69.6 seconds
    # sql1 = "select t0.dest as dest, t0.path as path, t0.condition || t1.condition || Array['And(' || t0.dest ||  ' == '  || t1.dest || ', ' || t0.path ||  ' == '  || t1.path || ')']::text[] as condition from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path);" 

    # ========================= Non-random =========================================================
    ############################### size = 100,000 ######################################
    # psycopg2.errors.InternalError_: invalid DSA memory alloc request size 1543503872
    # sql1 = "select t0.dest as dest, t0.path as path from p1 t0, p3 t1 where ((t0.dest = t1.dest or t0.dest< 0) and (t0.path = t1.path or t0.path< 0));"

    # psycopg2.errors.InternalError_: invalid DSA memory alloc request size 1543503872
    # sql1 = "select t0.dest as dest, t0.path as path, t0.condition || t1.condition || Array['And(' || t0.dest ||  ' == '  || t1.dest || ', ' || t0.path ||  ' == '  || t1.path || ')']::text[] as condition from p1 t0, p3 t1 where ((t0.dest = t1.dest or t0.dest< 0) and (t0.path = t1.path or t0.path< 0));" 


    ############################### size = 25000 ######################################
    # 93.8 seconds
    # sql1 = "select t0.dest as dest, t0.path as path from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path);"

    ############################### size = 100000 ######################################
    # 12.3 seconds
    # sql1 = "select t0.dest as dest, t0.path as path from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path);"

    # 69.6 seconds
    # sql1 = "select t0.dest as dest, t0.path as path, t0.condition || t1.condition || Array['And(' || t0.dest ||  ' == '  || t1.dest || ', ' || t0.path ||  ' == '  || t1.path || ')']::text[] as condition from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path);" 


    ############################### size = 10000 ######################################
    # 14.9 seconds
    # sql1 = "select t0.dest as dest, t0.path as path from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path);"

    # 69.6 seconds
    # sql1 = "select t0.dest as dest, t0.path as path, t0.condition || t1.condition || Array['And(' || t0.dest ||  ' == '  || t1.dest || ', ' || t0.path ||  ' == '  || t1.path || ')']::text[] as condition from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path);" 

    ############################### size = 5000 ######################################
    # 17.2 seconds
    # sql1 = "select t0.dest as dest, t0.path as path, t0.condition || t1.condition || Array['And(' || t0.dest ||  ' == '  || t1.dest || ', ' || t0.path ||  ' == '  || t1.path || ')']::text[] as condition from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path);" 

    # 12.7 seconds
    # sql1 = "select t0.dest as dest, t0.path as path, t0.condition || t1.condition || Array[t0.dest ||  ' == '  || t1.dest]::text[] as condition from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path);" 

    # 7.87 seconds
    # sql1 = "select t0.dest as dest, t0.path as path, t0.condition || t1.condition::text[] as condition from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path);" 

    # 31.5 seconds
    # sql1 = "select t0.dest as dest, t0.path as path, t0.condition || t1.condition || Array['And(' || t0.dest ||  ' == '  || t1.dest || ', ' || t0.path ||  ' == '  || t1.path || ')']::text[] as condition from p1 t0, p3 t1;"

    # 6.09 seconds
    # sql1 = "select t0.dest as dest, t0.path as path, t0.condition as condition from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path);"

    # 3.7 seconds
    # sql1 = "select t0.dest as dest, t0.path as path from p1 t0, p3 t1 where (t0.dest = t1.dest and t0.path = t1.path);"

def selectQuery():
    sql1 = "select dest, path as path from p1_faure where (dest > 20000 and dest < 50000)"
    return sql1
            

if __name__ == '__main__':
    # size = 5000000
    size = 20
    path = 5

    # p1_data = generate_policy1(size)
    start = time.time()
    # store_tables("p1_faure", ["dest", "path", "condition"], ["int4_faure", "int4_faure", "text[]"], p1_data)
    end = time.time()
    print("Store Time p1_faure:",end-start)

    p3_data = generate_policy3(size, path)
    print(p3_data)
    start =time.time()
    store_tables("p3_faure", ["dest", "path", "condition"], ["int4_faure", "int4_faure", "text[]"], p3_data)
    end = time.time()
    print("Store Time p3_faure:",end-start)
    exit()

    cursor = conn.cursor()

    sql1 = selectQuery()


    iterations = 50
    times = []
    for i in range(iterations):
        start = time.time()
        cursor.execute(sql1)
        end = time.time()
        times.append(end-start)
    print("Average Time Taken in {} runs: {}".format(iterations, np.mean(times)))

    # p1 = "R(a,b) :- p1(a,b), p3(a,b)"
    # # program1 = DT_Program(p1, database, optimizations={"simplification_on":True})
    # program1 = DT_Program(p1, database)
    # program1.execute(conn)




