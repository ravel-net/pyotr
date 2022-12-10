from copy import deepcopy
import sys
import time
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(dirname(abspath(__file__))))))
sys.path.append(root)
from Backend.reasoning.Z3.z3smt import z3SMTTools
from Core.Homomorphism.faure_translator.sketchy_recursive_code.faure_evaluation_copy import FaureEvaluation

import databaseconfig as cfg
import psycopg2 
from psycopg2.extras import execute_values

def test_cvariables():
    """
    P:
    p1: R(x, y) :- L(x, y)
    p2: R(x, y) :- R(x, z), L(z, y)

    Q:
    q1: R(x, y) :- R(x, z), L(z, u), L(u, y)

    check P uniformly contains Q
    """
    
    conn = psycopg2.connect(
        host=cfg.postgres["host"], 
        database=cfg.postgres["db"], 
        user=cfg.postgres["user"], 
        password=cfg.postgres["password"])

    databases = {
        'R':{
            'names':['n1', 'n2', 'condition'],
            'types':['int4_faure', 'int4_faure', 'text[]']
        },
        'L':{
            'names':['n1', 'n2', 'condition'],
            'types':['int4_faure', 'int4_faure', 'text[]']
        }
    }

    L = [
        ['z', 'u', '{}'],
        ['u', 'y', '{}']
    ]

    R = [
        ['x', 'z', '{}']
    ]

    cursor = conn.cursor()
    cursor.execute("drop table if EXISTS L")
    cursor.execute("create table L (n1 int4_faure, n2 int4_faure, condition text[])")

    execute_values(cursor, "insert into L values %s", L)

    cursor = conn.cursor()
    cursor.execute("drop table if EXISTS R")
    cursor.execute("create table R (n1 int4_faure, n2 int4_faure, condition text[])")

    execute_values(cursor, "insert into R values %s", R)

    conn.commit()

    with_sql = "WITH RECURSIVE temp_R(n1, n2) AS (\
                    SELECT * from L\
                    UNION \
                    SELECT t1.n1 as n1, t2.n2 as n2 \
                    FROM temp_R t1, L t2\
                    WHERE t1.n2 = t2.n1\
                )\
                SELECT * from temp_R;"

    FaureEvaluation(conn, with_sql, is_recursive=True, databases=databases, simplication_on=True, information_on=False)

if __name__ == '__main__':
    test_cvariables()





    
    
    