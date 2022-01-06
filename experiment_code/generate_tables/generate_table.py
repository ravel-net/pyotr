import psycopg2
from tqdm import tqdm 
import time
import sys


host = '127.0.0.1'
user = 'postgres'
password = 'mubashir'
database = 'test'

# generate the F table
# input: tablename(subset of raw rib table,such as rib1000)
def gen_f_table(tablename = "rib1000", type = "inet", file_name = "f_table_inet.txt"):
    """
    Generate the F table
    @param tablename: the name of the F table, default rib1000
    """

    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    #create f_table in database
    cur.execute("DROP TABLE IF EXISTS f_table_{}".format(tablename))
    cur.execute("CREATE TABLE f_table_{}(id SERIAL PRIMARY KEY, fid {})".format(tablename,type))
    f = open(file_name, "r")
    lines = f.readlines()
    for line in lines:
        if len(line) < 2:
            continue
        line = line.strip()
        line = line.strip("`")
        cur.execute("INSERT INTO f_table_{} VALUES (DEFAULT,'{}')".format(tablename, line))
    conn.commit()
    conn.close()
    
def gen_r_table(tablename = "rib1000", type = "inet", file_name = "rib1000_inet.txt"):
    """
    Generate the F table
    @param tablename: the name of the F table, default rib1000
    """

    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    #create f_table in database
    cur.execute("DROP TABLE IF EXISTS {}".format(tablename))
    cur.execute("CREATE TABLE {}(id SERIAL PRIMARY KEY, prefix {})".format(tablename,type))
    f = open(file_name, "r")
    lines = f.readlines()
    for line in lines:
        if len(line) < 2:
            continue
        line = line.strip()
        line = line.strip("`")
        cur.execute("INSERT INTO {} VALUES (DEFAULT,'{}')".format(tablename, line))
    conn.commit()
    conn.close()

if __name__ == '__main__':
    data_type = sys.argv[1]
    f_table_file = sys.argv[2]
    rib_file = sys.argv[3]
    gen_f_table("rib1000", data_type, f_table_file)
    gen_r_table("rib1000", data_type, rib_file)
# gen_f_table(tablename = 'rib1000')