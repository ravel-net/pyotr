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
def gen_f_table(tablename = "rib1000"):
    """
    Generate the F table
    @param tablename: the name of the F table, default rib1000
    """

    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    #create f_table in database
    cur.execute("DROP TABLE IF EXISTS f_table_{}".format(tablename))
    cur.execute("CREATE TABLE f_table_{}(id SERIAL PRIMARY KEY, fid inet)".format(tablename))
    cur.execute("INSERT INTO f_table_{} VALUES (DEFAULT,'192.168.1.1')".format(tablename))
    conn.commit()
    conn.close()
    
if __name__ == '__main__':
	gen_f_table()
# gen_f_table(tablename = 'rib1000')