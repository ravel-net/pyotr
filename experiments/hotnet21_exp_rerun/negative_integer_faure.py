import os
import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time
import datetime
from Core.Datalog.program import DT_Program
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
import psycopg2
from psycopg2.extras import execute_values
import databaseconfig as cfg
from utils.logging import timeit
import logging

conn = psycopg2.connect(host=cfg.postgres["host"], database="routeview", user=cfg.postgres["user"], password=cfg.postgres["password"])

@timeit
def q4q5(f_table):
    F = DT_Table(name=f_table, columns={"fid":"text", "nid1":"integer_faure", "nid2":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    R = DT_Table(name="{}_r".format(f_table), columns={"fid":"text", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})

    database = DT_Database(tables=[F,R])
    R.initiateTable(conn)
    conn.commit()

    p1 = "{R}(fid,n1,n2):- {F}(fid,n1,n2)\n{R}(fid,n1,n2):-{F}(fid,n1,n3),{R}(fid,n3,n2)".format(F=f_table, R="{}_r".format(f_table))
    program1 = DT_Program(p1, database)
    start = time.time()
    program1.execute(conn)
    end = time.time()

@timeit
def q6(r_table):
    T1 = DT_Table(name="T1", columns={"fid":"text", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    R = DT_Table(name=r_table, columns={"fid":"text", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    database = DT_Database(tables=[R,T1])
    T1.initiateTable(conn)
    # R.initiateTable(conn)
    conn.commit()
    # cursor = conn.cursor()
    # cursor.execute("INSERT INTO R VALUES (1,2,3),(4,5,6)")
    # conn.commit()

    p1 = "T1(fid, n1, n2)[x+y+z=1] :- {}(fid,n1,n2),(x+y+z=1)".format(r_table)
    program1 = DT_Program(p1, database, optimizations={'recursive_rules':False})
    start = time.time()
    program1.execute(conn)
    end = time.time()

@timeit
def q7():
    T2 = DT_Table(name="T2", columns={"fid":"text", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    T1 = DT_Table(name="T1", columns={"fid":"text", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    database = DT_Database(tables=[T1,T2])
    T2.initiateTable(conn)
    # R.initiateTable(conn)
    conn.commit()
    # cursor = conn.cursor()
    # cursor.execute("INSERT INTO R VALUES (1,2,3),(4,5,6)")
    # conn.commit()

    p1 = "T2(fid, 14315,9526)[y=0] :- T1(fid,14315,9526),(y=0)"
    program1 = DT_Program(p1, database, optimizations={'recursive_rules':False})
    start = time.time()
    program1.execute(conn)
    end = time.time()

@timeit
def q8(r_table):
    R = DT_Table(name=r_table, columns={"fid":"text", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    T3 = DT_Table(name="T3", columns={"fid":"text", "source":"integer_faure", "dest":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "u":"condition", "v":"condition"})
    database = DT_Database(tables=[T3,R])
    T3.initiateTable(conn)
    # R.initiateTable(conn)
    conn.commit()
    # cursor = conn.cursor()
    # cursor.execute("INSERT INTO R VALUES (1,2,3),(4,5,6)")
    # conn.commit()

    p1 = "T3(fid,53767,n2)[y+x<2] :- {}(fid,53767,n2),(y+z<0)".format(r_table)
    program1 = DT_Program(p1, database, optimizations={'recursive_rules':False})
    start = time.time()
    program1.execute(conn)
    end = time.time()

def clean_tables():
    cursor = conn.cursor()
    cursor.execute("drop table if exists t1")
    cursor.execute("drop table if exists t2")
    cursor.execute("drop table if exists t3")
    conn.commit()

if __name__ == "__main__":
    # tables = ['rib10_r', 'rib100_r', 'rib1000_r', 'rib10000_r', 'rib100000_r']
    # q4q5("f_table_rib10")
    table = sys.argv[1]
    num = 1
    if table == 'clean':
        clean_tables()
    else:
        query = sys.argv[2]
        # for table in tables:
        print('\n{} begin.....\n'.format(table))
        with open("time.log", "a") as f:
            for n in range(num):
                if query == 'q6':
                    begin_q6 = time.time()
                    q6(table)
                    end_q6 = time.time()
                    f.write("Time:q6 {} took {}\n".format(table, end_q6-begin_q6))
                    print("q6 done!\n")
                elif query == 'q7':
                    begin_q7 = time.time()
                    q7()
                    end_q7 = time.time()
                    f.write("Time:q7 {} took {}\n".format(table, end_q7-begin_q7))
                    print("q7 done!\n")
                elif query == 'q8':
                    begin_q8 = time.time()
                    q8(table)
                    end_q8 = time.time()
                    f.write("Time:q8 {} took {}\n".format(table, end_q8-begin_q8))
                    print("q8 done!\n")
                elif query == 'q4q5':
                    q4q5_begin = time.time()
                    q4q5(table)
                    q4q5_end = time.time()
                    f.write("Time:q4q5 {} took {}\n".format(table, q4q5_end-q4q5_begin))
                    print("q4q5 done!\n")
                if num > 1 and n != num - 1:
                    clean_tables()
                
            # if os.path.isfile('program.log'):
            #     os.rename('time.log', '{}_{}_{}.log'.format(table, query, datetime.datetime.now().strftime('%Y%m%d%H%M%S')))
            conn.close()