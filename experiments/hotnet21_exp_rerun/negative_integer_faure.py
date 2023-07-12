import sys
from os.path import dirname, abspath
from turtle import pos

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time
from Core.Datalog.program import DT_Program
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
import psycopg2
from psycopg2.extras import execute_values
import databaseconfig as cfg

conn = psycopg2.connect(host=cfg.postgres["host"], database="routeview", user=cfg.postgres["user"], password=cfg.postgres["password"])


def q6(r_table):
    T1 = DT_Table(name="T1", columns={"fid":"inet", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    R = DT_Table(name=r_table, columns={"fid":"inet", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    database = DT_Database(tables=[R,T1])
    T1.initiateTable(conn)
    # R.initiateTable(conn)
    conn.commit()
    # cursor = conn.cursor()
    # cursor.execute("INSERT INTO R VALUES (1,2,3),(4,5,6)")
    # conn.commit()

    p1 = "T1(fid, n1, n2)[x+y+z=1] :- {}(fid,n1,n2),(x+y+z=1)".format(r_table)
    program1 = DT_Program(p1, database)
    start = time.time()
    program1.execute(conn)
    end = time.time()

def q7():
    T2 = DT_Table(name="T2", columns={"fid":"inet", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    T1 = DT_Table(name="T1", columns={"fid":"inet", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    database = DT_Database(tables=[T1,T2])
    T2.initiateTable(conn)
    # R.initiateTable(conn)
    conn.commit()
    # cursor = conn.cursor()
    # cursor.execute("INSERT INTO R VALUES (1,2,3),(4,5,6)")
    # conn.commit()

    p1 = "T2(fid, 14315,9526)[y=0] :- T1(fid,14315,9526),(y=0)"
    program1 = DT_Program(p1, database)
    start = time.time()
    program1.execute(conn)
    end = time.time()

def q8(r_table):
    R = DT_Table(name=r_table, columns={"fid":"inet", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    T3 = DT_Table(name="T3", columns={"fid":"inet", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    database = DT_Database(tables=[T3,R])
    T3.initiateTable(conn)
    # R.initiateTable(conn)
    conn.commit()
    # cursor = conn.cursor()
    # cursor.execute("INSERT INTO R VALUES (1,2,3),(4,5,6)")
    # conn.commit()

    p1 = "T3(fid,53767,n2)[y+x<2] :- {}(fid,53767,n2),(y+z<0)".format(r_table)
    program1 = DT_Program(p1, database)
    start = time.time()
    program1.execute(conn)
    end = time.time()


if __name__ == "__main__":
    q6("rib100_r")
    print("q6 done!\n")
    # q7()
    # print("q7 done!\n")
    # q8("rib1000_r")
    # print("q8 done!\n")
