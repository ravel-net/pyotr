import time

import sys
from os.path import dirname, abspath
root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)

import psycopg2
from psycopg2.extras import execute_values
import random
from Core.Updates.update_storms import update_storms
import databaseconfig as dbconfig

def create_db_connection():
    host = dbconfig.postgres['host']
    user = dbconfig.postgres['user']
    password = dbconfig.postgres['password']
    db = dbconfig.postgres['db']

    conn = psycopg2.connect(host=host, user=user, password=password, database=db)

    return conn

def shut_down_db(conn):
    conn.close()

def test1():
    conn = create_db_connection()

    existing_tuples = [
        ('2', 'y1', 's1', ['y1 == 10']),
        ('1', 'y2', 's1', ['y2 == 20']),
        ('0', 'y3', 'GW', ['y3 == 0'])
    ]

    delta_tuples = [
        ('3', 'x1', 's2', ['x1 == 30']),
        ('3', 'x2', 's2', ['x2 == 20']),
    ]

    cursor = conn.cursor()
    cursor.execute("drop table if exists R1")
    cursor.execute("create table R1 (priority text, header int4_faure, action text, condition text[])")
    execute_values(cursor, "insert into R1 values %s", existing_tuples)

    cursor.execute("drop table if exists R1_delta")
    cursor.execute("create table R1_delta (priority text, header int4_faure, action text, condition text[])")
    execute_values(cursor, "insert into R1_delta values %s", delta_tuples)

    conn.commit()

    update_storms(conn, 'R1', "R1_delta", "output")

    shut_down_db(conn)


def test2():
    conn = create_db_connection()

    existing_tuples = [
        ('2', 'y1', 's1', ['p1']),
        ('1', 'y2', 's1', ['p2']),
        ('0', 'y3', 'GW', ['p0'])
    ]

    delta_tuples = [
        ('3', 'x1', 's2', ['p4']),
        ('3', 'x2', 's2', ['p5']),
    ]

    cursor = conn.cursor()
    cursor.execute("drop table if exists R1")
    cursor.execute("create table R1 (priority text, header int4_faure, action text, condition text[])")
    execute_values(cursor, "insert into R1 values %s", existing_tuples)

    cursor.execute("drop table if exists R1_delta")
    cursor.execute("create table R1_delta (priority text, header int4_faure, action text, condition text[])")
    execute_values(cursor, "insert into R1_delta values %s", delta_tuples)

    conn.commit()

    update_storms(conn, 'R1', "R1_delta", "output")

    shut_down_db(conn)

def test3():
    conn = create_db_connection()

    existing_tuples = [
        ('2', 'y1', 's1', ['p1']),
        ('2', 'y2', 's1', ['y2 == 15']),
        ('1', 'y3', 's0', ['y3 == 20']),
        ('1', 'y4', 's1', ['y4 == 30']),
        ('0', 'y5', 'GW', ['y5 == 0'])
    ]

    delta_tuples = [
        ('3', 'x1', 's2', ['x1 == 30']),
        ('3', 'x2', 's2', ['x2 == 20']),
    ]

    cursor = conn.cursor()
    cursor.execute("drop table if exists R1")
    cursor.execute("create table R1 (priority text, header int4_faure, action text, condition text[])")
    execute_values(cursor, "insert into R1 values %s", existing_tuples)

    cursor.execute("drop table if exists R1_delta")
    cursor.execute("create table R1_delta (priority text, header int4_faure, action text, condition text[])")
    execute_values(cursor, "insert into R1_delta values %s", delta_tuples)

    conn.commit()

    update_storms(conn, 'R1', "R1_delta", "output")

    shut_down_db(conn)

def performance_test_for_integer_type():
    """
    test performance with integer reasoning type in conditions. i.e., the condition is x == 10
    the baseline table has 100 rules, test 10, 100, 1000 delta rules, there are three level of priority, i.e., 1, 2, 3
    each level of priority has 1/3 of testing rules
    Assume there are 30 actions, randomly choose one of 30 actions for rules.
    """

    num_base_rules = 100
    num_testing_rules = 100
    base_tuples = []
    actions = ["s{}".format(i) for i in range(30)]
    for i in range(num_base_rules):
        header_var = "x{}".format(i)
        action = random.sample(actions, 1)
        condition = ["{} == {}".format(header_var, gen_random_number())]
        if i % 3 == 0:
            base_tuples.append(("1", header_var, action, condition))
        elif i % 3 == 1:
            base_tuples.append(("2", header_var, action, condition))
        else:
            base_tuples.append(("3", header_var, action, condition))
    
    delta_tuples = []
    for i in range(num_testing_rules):
        header_var = "y{}".format(i)
        action = random.sample(actions, 1)
        condition = ["{} == {}".format(header_var, gen_random_number())]
        if i % 3 == 0:
            delta_tuples.append(("1", header_var, action, condition))
        elif i % 3 == 1:
            delta_tuples.append(("2", header_var, action, condition))
        else:
            delta_tuples.append(("3", header_var, action, condition))
        
    conn = create_db_connection()
    
    cursor = conn.cursor()
    cursor.execute("drop table if exists R1")
    cursor.execute("create table R1 (priority text, header int4_faure, action text, condition text[])")
    execute_values(cursor, "insert into R1 values %s", base_tuples)

    cursor.execute("drop table if exists R1_delta")
    cursor.execute("create table R1_delta (priority text, header int4_faure, action text, condition text[])")
    execute_values(cursor, "insert into R1_delta values %s", delta_tuples)

    conn.commit()

    update_storms(conn, 'R1', "R1_delta", "output")

    shut_down_db(conn)

def gen_random_number(lower_bound=0, upper_bound=10000):
    num = random.randint(lower_bound, upper_bound)
    return num

if __name__ == '__main__':
    # test1()
    # test2()
    # test3()
    performance_test_for_integer_type()