"""
This is for generate policy data 
"""
import math
import psycopg2
from psycopg2.extras import execute_values
import databaseconfig as dbconfig

DATABASE = dbconfig.postgres['database']
HOST = dbconfig.postgres['host']
USER = dbconfig.postgres['user']
PASSWORD = dbconfig.postgres['password']

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

    return tuples

def generate_policy3(size):
    """
    policy 3 is load balance policy
    """
    address_base = 20000
    path_base = 50000
    tuples = []
    for i in range(0, size, 2):
        addr1 = address_base + i
        addr2 = address_base + i + 1

        path1 = path_base + i
        path2 = path_base + i + 1

        c_var = "u{}".format(i)
        # c_var2 = "v{}".format(i)

        # t1 = [addr1, path1, c_var1, ["{} == 1".format(c_var1), "{} != 1".format(c_var2)]]
        # t2 = [addr1, path2, c_var1, ["{} != 1".format(c_var1), "{} == 1".format(c_var2)]]
        # t3 = [addr2, path1, c_var2, ["{} == 1".format(c_var2), "{} != 1".format(c_var1)]]
        # t4 = [addr2, path2, c_var2, ["{} != 1".format(c_var2), "{} == 1".format(c_var1)]]

        t1 = [addr1, c_var, []]
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
        
    
if __name__ == '__main__':
    size = 10
    p1_data = generate_policy1(size)
    store_tables("p1", ["dest", "path", "condition"], ["int4_faure", "int4_faure", "text[]"], p1_data)

    p3_data = generate_policy3(size)
    store_tables("p3", ["dest", "path", "condition"], ["int4_faure", "int4_faure", "text[]"], p3_data)



