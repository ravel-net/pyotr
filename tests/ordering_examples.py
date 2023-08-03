import time

import sys
from os.path import dirname, abspath
root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)
from Core.Datalog.program import DT_Program
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
import psycopg2 
import databaseconfig as cfg
from tabulate import tabulate
from copy import deepcopy

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

# # ordering example 1 (consistent updates)
# v = 1, u = 2, x = 3, y = 4, d = 5
# y1 = -1, y2 = -2, y3 = -3, y3 = -4, y5 = -5
def ordering_example1():
    R = DT_Table(name="R", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"})

    V = DT_Table(name="V", columns={"violation":"integer", "path":"integer_faure[]"}, cvars={"p":"path"})

    F = DT_Table(name="F", columns={"header":"integer_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"y4":"next_hop","y5":"next_hop","y1":"next_hop","y2":"next_hop","y3":"next_hop"}, domain={"next_hop":[5,1,2,3,4,401],"node":[5,1,2,3,4,401]})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[F,R,V], cVarMapping = {'-1':"y1",'-2':"y2",'-3':"y3",'-4':"y4",'-5':"y5"})
    
    p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nV(1, p) :- R(10, X, n2, p), F(10, n2, n)[n == p]\nR(10, X, n, p || [n]) :- R(10, X, n2, p), F(10, n2, n)"
    # p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nR(10, X, n, p || [n]) :- R(10, X, n2, p), F(10, n2, n)\nV(1, p) :- R(10, 100, 400, p)[p[array_upper(p, 1)] == p]"

    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    # conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    # conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    database.initiateDB(conn)
    conn.commit()
    variableConstants = []

    program1.execute(conn)

    sql = "insert into F values (10, 1, 3, '{}'), (10, 2, -2, '{\"Or(y2 == 1, y2 == 3)\"}'), (10, 3, -3, '{\"Or(y3 == 5, y3 == 4)\"}'), (10, 4, -4, '{\"Or(y4 == 3, y4 == 5)\"}'), (10, 5, 401, '{}')"
    input()

    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()
    
    start = time.time()
    program1.executeonce(conn)
    conn.commit()
    input()
    program1.executeonce(conn)
    conn.commit()
    input()
    end = time.time()
    database.delete(conn)
    exit()
    cursor.execute("select * from V")
    if cursor.fetchall()[0][0] == 1:
        print("Test 13 passed in {} seconds".format(end-start))
        database.delete(conn)
    else:
        print("Test 13 failed in {} seconds".format(end-start))
        database.delete(conn)
        exit()

# ordering example 2 (from consistent updates paper)
# v = 1, u = 2, w = 3, d = 4
# y1 = -1, y2 = -2, y3 = -3, y3 = -4, y5 = -5
def ordering_example2():
    R = DT_Table(name="R", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"})

    V = DT_Table(name="V", columns={"violation":"integer"})

    F = DT_Table(name="F", columns={"header":"integer_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"C4":"next_hop","C5":"next_hop","C1":"next_hop","C2":"next_hop","C3":"next_hop"}, domain={"next_hop":[1,2,3,4,401],"node":[1,2,3,4,401]})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[F,R,V], cVarMapping = {'-1':"C1",'-2':"C2",'-3':"C3",'-4':"C4",'-5':"C5"})
    
    # p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nR(10, X, n, p || [n]) :- R(10, X, n2, p)[n != p], F(10, n2, n)\nV(1) :- R(10, X, 5, p)[And(1 != p, 400 == p)]"
    p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nR(10, X, n, p || [n]) :- R(10, X, n2, p), F(10, n2, n)"

    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    # conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    # conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    database.initiateDB(conn)
    conn.commit()
    variableConstants = []

    sql = "insert into F values (10, 1, -1, '{\"Or(C1 == 4, C1 == 3)\"}'), (10, 2, -2, '{\"Or(C2 == 4, C2 == 1)\"}'), (10, 3, -3, '{\"Or(C3 == 2, C3 == 4)\"}'),(10, 4, 401, '{}')"
    input()

    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()
    
    start = time.time()
    program1.executeonce(conn)
    conn.commit()
    input()
    program1.executeonce(conn)
    conn.commit()
    input()
    end = time.time()
    database.delete(conn)
    exit()

# ordering example 3
# s = 11, v1 = 22, v2 = 33, v3 = 44, d = 55
# C1 = -1, C2 = -2, C3 = -3, C4 = -4, C5 = -5
# https://ieeexplore.ieee.org/stamp/stamp.jsp?arnumber=8500100&casa_token=BnSkzZ8MHcgAAAAA:BdUDVVwmYi_p-szvbrSQKISQPPQT6FoTXlgclcGZmLDluKkaSevytPYSMA2NnlB5BO2vEfjk7Bc
def ordering_example3():
    R1 = DT_Table(name="R1", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"})

    V1 = DT_Table(name="V1", columns={"header":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"})

    F1 = DT_Table(name="F1", columns={"header":"integer_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"v1_next":"next_hop","v2_next":"next_hop","v3_next":"next_hop"}, domain={"next_hop":[11,22,33,44,55],"node":[11,22,33,44,55]})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[F1,R1,V1], cVarMapping = {'-2':"v1_next",'-3':"v2_next",'-4':"v3_next"})
    
    # p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nR(10, X, n, p || [n]) :- R(10, X, n2, p)[n != p], F(10, n2, n)\nV(1) :- R(10, X, 5, p)[And(1 != p, 400 == p)]"
    p1 = "R1(10, X, n, [X, n]) :- F1(10, X, n)"
    p2 = "V1(10, p) :- R1(10, X, n2, p), F1(10, n2, n)[n != p]\nR1(10, X, n, p || [n]) :- R1(10, X, n2, p), F1(10, n2, n)[n != p]"

    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    program2 = DT_Program(p2, database=database, optimizations={"simplification_on":True})
    # conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    # conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    nodeMapping = {'11':"s","22":"v1","33":"v2","44":"v3","55":"d"}
    database.initiateDB(conn)
    conn.commit()
    variableConstants = []

    sql = "insert into F1 values (10, 11, 22, '{}'),(10, 22, -2, '{\"Or(v1_next == 33, v1_next == 55)\"}'),(10, 33, -3, '{\"Or(v2_next == 44, v2_next == 22)\"}'),(10, 44, -4, '{\"Or(v3_next == 55, v3_next == 33)\"}')"

    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()
    printTable("F1",database,nodeMapping)
    input()
    
    start = time.time()
    program1.executeonce(conn)
    conn.commit()
    input()
    program2.execute(conn)
    printTable("V1",database,nodeMapping)
    # input()
    database.delete(conn)
    exit()

def replaceVal(val, mapping):
    if val in mapping:
        return mapping[val]
    elif str(val) in mapping:
        return mapping[str(val)]
    elif type(val) == str:
        for replaceable in mapping:
            if str(replaceable) in val:
                val = val.replace(str(replaceable), mapping[replaceable])
        return val
    else:
        return val
    
# move this to table class
def printTable(tableName, db, nodeIntMappingReverse, condition = None):
    cursor = conn.cursor()
    # cursor.execute("SELECT * from {} where source = 1 and dest = 7".format(tableName))
    if condition:
        cursor.execute("SELECT * from {} where {}".format(tableName, condition))
    else:
        cursor.execute("SELECT * from {}".format(tableName))

    table = cursor.fetchall()
    newTable = []
    mapping = deepcopy(nodeIntMappingReverse)
    mapping.update(db.cVarMapping)
    for row in table:
        newRow = []
        for colm in row:
            if type(colm) == list:
                colmArray = []
                for item in colm:
                    colmArray.append(replaceVal(item, mapping))
                newRow.append(colmArray)
            else:
                newRow.append(replaceVal(colm, mapping))
        newTable.append(newRow)
    cursor.execute("SELECT column_name FROM information_schema.columns WHERE table_schema = 'public' AND table_name = '{}'".format(tableName.lower()))
    headers = cursor.fetchall()
    headerInArray = []
    for colm in headers:
        headerInArray.append(colm[0])
    print("\nPrinting Table: {}".format(tableName))
    print(tabulate(newTable, headers=headerInArray))

# Anduo's example 1
# X = 1, W = 2, A = 3, B = 4, Y = 5, E = 6, C = 7
# alpha = -1, beta = -2, gamma = -3, t_one = -4, t_two = -5
def distributed_example1():
    R = DT_Table(name="R", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"}, domain={"source":[1,2,3,4,5,6,7],"dest":[1,2,3,4,5,6,7]})

    V = DT_Table(name="V", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"}, domain={"source":[1,2,3,4,5,6,7],"dest":[1,2,3,4,5,6,7]})

    F = DT_Table(name="F", columns={"header":"integer_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"alpha":"next_hop", "beta":"next_hop","gamma":"next_hop","t_one":"header","t_two":"header"}, domain={"next_hop":[1,2,3,4,5,6,7],"node":[1,2,3,4,5,6,7], "header":[10,2,0,1]})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[F,R,V], cVarMapping = {'-1':"alpha",'-2':"beta",'-3':"gamma",'-4':"t_one",'-5':"t_two",'-100':"p"})

    p1 = "R(10, S, n, [S, n]) :- F(10, S, n)"
    p2 = "V(10, 1, n, p || [n]) :- R(10, 1, n2, p)[And(2 != p, 5 != p, n != p, n == 7)], F(10, n2, n)\nR(10, S, n, p || [n]) :- R(10, S, n2, p)[n != p], F(10, n2, n)"

    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    program2 = DT_Program(p2, database=database, optimizations={"simplification_on":True})
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    database.initiateDB(conn)
    conn.commit()
    variableConstants = []
# X = 1, W = 2, A = 3, B = 4, Y = 5, E = 6, C = 7
# alpha = -1, u = -2, t_one = -3, t_two = -4
    
    sql = "insert into F values (10, 1, '-1', '{\"Or(alpha == 3, alpha == 2)\"}'), (10, 2, '-2', '{\"Or(beta == 3, beta == 4)\"}'), (10, 3, '-3', '{\"Or(gamma == 2, gamma == 4)\"}'), (10, 4, 6, '{\"And(t_one == 0, And(alpha == 3, beta == 3, gamma == 4))\"}'), (10, 4, 5, '{\"t_one != 0\"}'), (10, 6, 7, '{\"t_two == 0\"}'), (10, 6, 5, '{\"And(t_two != 3, And(alpha == 3, beta == 3, gamma == 4))\"}'), (10, 5, 7, '{}')"
    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()
    input()
    start = time.time()
    program1.executeonce(conn)
    conn.commit()
    input()
    program2.execute(conn)
    end = time.time()
    cursor.execute("select * from V")
    V_values = cursor.fetchall()
    printTable("V", database, {1:'X',2:'W',3:'A',4:'B',5:'Y',6:'E',7:'C'})
    input()


# X = 11, W = 22, A = 33, E = 44, Y = 55, B = 66, C = 77, D = 88
# alpha = -1, beta = -2, u = -11, gamma = -3, sigma = -4, v = -22, t_one = -101, t_two = -201, t_three = -301, t_four = -401, l = -1111
# Anduo's email on July 29 with 3 admins
def distributed_example2():
    M1 = DT_Table(name="M1", columns={"node":"integer","condition":"text[]"}, domain={"node":[11,22,33,44,55,66,77,88]})
    M2 = DT_Table(name="M2", columns={"node":"integer","condition":"text[]"}, domain={"node":[11,22,33,44,55,66,77,88]})
    M12 = DT_Table(name="M12", columns={"node":"integer","condition":"text[]"}, domain={"node":[11,22,33,44,55,66,77,88]})
    M23 = DT_Table(name="M23", columns={"node":"integer","condition":"text[]"}, domain={"node":[11,22,33,44,55,66,77,88]})
    M123 = DT_Table(name="M123", columns={"node":"integer","condition":"text[]"}, domain={"node":[11,22,33,44,55,66,77,88]})

    R_admins = DT_Table(name="R_admins", columns={"source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path", "alpha":"source", "beta":"source","gamma":"source","sigma":"source", "u":"condition", "v":"condition", "t_one":"condition", "t_two":"condition", "t_three":"condition", "t_four":"condition", "l":"condition"}, domain={"source":[11,22,33,44,55,66,77,88],"dest":[11,22,33,44,55,66,77,88], "condition":[0,1]})

    V_admins = DT_Table(name="V_admins", columns={"path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"})

    F1 = DT_Table(name="F1", columns={"node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"alpha":"node", "beta":"node","gamma":"node","sigma":"node", "u":"condition", "v":"condition", "t_one":"condition", "t_two":"condition", "t_three":"condition", "t_four":"condition", "l":"condition"}, domain={"node":[11,22,33,44,55,66,77,88],"next_hop":[11,22,33,44,55,66,77,88], "condition":[0,1]})

    F2 = DT_Table(name="F2", columns={"node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"alpha":"node", "beta":"node","gamma":"node","sigma":"node", "u":"condition", "v":"condition", "t_one":"condition", "t_two":"condition", "t_three":"condition", "t_four":"condition", "l":"condition"}, domain={"node":[11,22,33,44,55,66,77,88],"next_hop":[11,22,33,44,55,66,77,88], "condition":[0,1]})

    F3 = DT_Table(name="F3", columns={"node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"alpha":"node", "beta":"node","gamma":"node","sigma":"node", "u":"condition", "v":"condition", "t_one":"condition", "t_two":"condition", "t_three":"condition", "t_four":"condition", "l":"condition"}, domain={"node":[11,22,33,44,55,66,77,88],"next_hop":[11,22,33,44,55,66,77,88], "condition":[0,1]})

    F_admins = DT_Table(name="F_admins", columns={"node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"alpha":"node", "beta":"node","gamma":"node","sigma":"node", "u":"condition", "v":"condition", "t_one":"condition", "t_two":"condition", "t_three":"condition", "t_four":"condition", "l":"condition"}, domain={"node":[11,22,33,44,55,66,77,88],"next_hop":[11,22,33,44,55,66,77,88], "condition":[0,1]})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[F1,F2,F3,M1,M2,M12,M23,M123,V_admins, R_admins, F_admins], cVarMapping = {'-1':"alpha",'-2':"beta",'-3':"gamma",'-4':"sigma",'-4=101':"t_one",'-201':"t_two",'-1123':"p",'-301':"t_three",'-401':"t_four",'-1111':"l"})
    
    # p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nR(10, X, n, p || [n]) :- R(10, X, n2, p)[n != p], F(10, n2, n)\nV(1) :- R(10, X, 5, p)[And(1 != p, 400 == p)]"
    p0 = "F_admins(x,y) :- F1(x,y), M1(x)\nF_admins(x,y) :- F2(x,y), M2(x)\nF_admins(x,y) :- F1(x,y), F2(x,y), M12(x)\nF_admins(x,y) :- F2(x,y), F3(x,y), M23(x)\nF_admins(x,y) :- F1(x,y), F2(x,y), F3(x,y), M123(x)"

    p1 = "R_admins(11, n, [11, n]) :- F_admins(11, n)"
    # p2 = "R_admins(11, n, p || [n]) :- R_admins(11, n2, p), F_admins(n2, n)[n != p]\nV_admins(p) :- R_admins(11, n2, p)[And(44 == p, 55 == p, 88 == p)]"
    # p2 = "R_admins(11, n, p || [n]) :- R_admins(11, n2, p), F_admins(n2, n)[n != p]"
    p2 = "V_admins(p) :- R_admins(11, n2, p), F_admins(n2, n)[n == p]\nR_admins(11, n, p || [n]) :- R_admins(11, n2, p), F_admins(n2, n)"

    program0 = DT_Program(p0, database=database, optimizations={"simplification_on":True})
    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    program2 = DT_Program(p2, database=database, optimizations={"simplification_on":True})
    # conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    # conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    nodeMapping = {'11':"X","22":"W","33":"A","44":"E","55":"Y","66":"B","77":"C","88":"D"}
    database.delete(conn)
    database.initiateDB(conn)
    conn.commit()
    variableConstants = []

# X = 11, W = 22, A = 33, E = 44, Y = 55, B = 66, C = 77, D = 88
# alpha = -1, beta = -2, u = -11, gamma = -3, sigma = -4, v = -22, t_one = -101, t_two = -201, t_three = -301, t_four = -401, l = -1111
# Anduo's email on July 29 with 3 admins

    # Correction: E goes to Y or B
    sql = "insert into F1 values (33, -1, '{\"Or(alpha == 55, alpha == 22)\"}'),(55, -2, '{\"Or(beta == 77, beta == 44)\"}'),(11, 33, '{\"And(And(alpha == 55, beta == 77),t_one == 0)\"}'),(11, 22, '{\"t_one != 0\"}'),(22,33,'{\"And(And(alpha == 55, beta == 77),t_two == 0)\"}'),(22,44,'{\"t_two != 0\"}'),(44,55,'{\"And(And(alpha == 55, beta == 77),t_three == 0)\"}'),(44,66,'{\"t_three != 0\"}')"
    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()

    sql = "insert into F2 values (44,-3,'{\"Or(gamma == 55, gamma == 66)\"}'), (55,-4,'{\"Or(sigma == 77, sigma == 44)\"}'), (66,44,'{\"And(And(gamma == 55, sigma == 77),t_four == 0)\"}'), (66,77,'{\"t_four != 0\"}'), (77,88,'{}')"
    # sql = "insert into F2 values (44,-3,'{\"Or(gamma == 55, gamma == 66)\"}'), (55,-4,'{\"Or(sigma == 77, sigma == 44)\"}'), (66,44,'{}'), (77,88,'{}')" # B always goes to E
    cursor = conn.cursor()
    cursor.execute(sql)

    sql = "insert into F3 values (66, 77, '{\"l == 1\"}'),(66, 44, '{\"l == 0\"}')"
    cursor = conn.cursor()
    cursor.execute(sql)

    sql = "insert into M1 values (11, '{}'),(22, '{}'),(33, '{}')"
    cursor = conn.cursor()
    cursor.execute(sql)

    sql = "insert into M12 values (44, '{}'),(55, '{}')"    
    cursor = conn.cursor()
    cursor.execute(sql)

    # sql = "insert into M23 values (44, '{}'),(66, '{}'),(77, '{}')"
    # Corrections: M23 only has B
    sql = "insert into M23 values (66, '{}')"
    cursor = conn.cursor()
    cursor.execute(sql)

    sql = "insert into M123 values (44, '{}')"  
    cursor = conn.cursor()
    cursor.execute(sql)

    sql = "insert into M2 values (77, '{}')"  
    cursor = conn.cursor()
    cursor.execute(sql)

    printTable("F1", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("F2", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("F3", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("M1", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("M12", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("M23", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("M123", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("M2", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})

    program0.execute(conn)
    start = time.time()
    # printTable("F_admins", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    # input()
    program1.executeonce(conn)

    # printTable("R_admins", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'}, condition="dest = 88")

    # program2.executeonce(conn)
    # conn.commit()
    # printTable("V",database,nodeMapping)
    # input()
    # program2.executeonce(conn)
    # conn.commit()
    # printTable("V",database,nodeMapping)
    # input()
    # program2.executeonce(conn)
    # conn.commit()
    # printTable("V",database,nodeMapping)
    # input()
    # program2.executeonce(conn)
    # conn.commit()
    program2.execute(conn, violationTables=[V_admins])
    end = time.time()
    conn.commit()
    printTable("V_admins",database,nodeMapping)
    printTable("R_admins",database,nodeMapping, condition="dest = 88")
    print("Time Taken:", end-start)
    input()
    database.delete(conn)
    exit()

# Example taken from NoD (Checking beliefs in networks)
# Anduo's encoding in an email on 2nd Aug 2023 (but pkt in and pkt out broken into src and dest). Format is 3 bits for dst followed by 3 bits for src
# G12 -> x == [34,35,42,43]  i.e. 10* and 01* (And(dst == [32,40], src == [2,3]))
# G13 -> x >= 32 i.e. 1** and ***
# G2B -> And(x >= 32, x <= 47) i.e. 10* and ***
# G3D -> x == [4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31,36,37,38,39,44,45,46,47,52,53,54,55,60,61,62,63] i.e. *** and 1**
# G32 -> x >= 32 i.e. 1** and ***
# Set(o5) -> And(x >= 32, x <= 47)

# R1 = 10, R2 = 20, R3 = 30, B = 111, D = 222
# i1 = -1, i2 = -2, i3 = -3, i4 = -4, i5 = -5
# o1 = -10, o2 = -20, o3 = -30, o4 = -40, o5 = -50
def EC_example1():
    R_nod = DT_Table(name="R_nod", columns={"pkt_in":"integer_faure", "pkt_out":"integer_faure", "source":"integer_faure", "dest":"integer_faure","condition":"text[]"}, cvars={"i1":"pkt_in","i2":"pkt_in","i3":"pkt_in","i4":"pkt_in","i5":"pkt_in", "o1":"pkt_out","o2":"pkt_out","o3":"pkt_out","o4":"pkt_out","o5":"pkt_out"}, domain={"source":[10,20,30,40,123,245],"dest":[10,20,30,40,123,245],"pkt_in":(0,63),"pkt_out":(0,63)})

    # V1 = DT_Table(name="V1", columns={"header":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"})

    F_nod = DT_Table(name="F_nod", columns={"pkt_in":"integer_faure", "pkt_out":"integer_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"i1":"pkt_in","i2":"pkt_in","i3":"pkt_in","i4":"pkt_in","i5":"pkt_in", "o1":"pkt_out","o2":"pkt_out","o3":"pkt_out","o4":"pkt_out","o5":"pkt_out"}, domain={"next_hop":[10,20,30,40,123,245],"node":[10,20,30,40,123,245],"pkt_in":(0,63),"pkt_out":(0,63)})

    database = DT_Database(tables=[R_nod,F_nod], cVarMapping = {'-16':"i1",'-26':"i2",'-36':"i3",'-46':"i4",'-56':"i5",'-11':"o1",'-22':"o2",'-33':"o3",'-44':"o4",'-55':"o5"})
    
    p1 = "R_nod(pkt_in, pkt_out, 10, dest) :- F_nod(pkt_in, pkt_out, 10, dest)"
    p2 = "R_nod(pkt_in, new_pktout, 10, z) :- R_nod(pkt_in, pkt_out, 10, y), F_nod(pkt_out, new_pktout, y, z)"

    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    program2 = DT_Program(p2, database=database, optimizations={"simplification_on":True})
    nodeMapping = {'10':"R1",'20':"R2",'30':"R3",'123':"B",'245':"D"}
    database.initiateDB(conn)
    conn.commit()

    sql = "insert into F_nod values (-16,-11, 10, 20, '{\"And(i1 == o1, o1 == {34,35,42,43})\"}'),(-26,-22, 10, 30, '{\"And(i2 == o2, o1 != {34,35,42,43}, o2 >= 32)\"}'),(-36,-33, 20, 123, '{\"And(i3 == o3, And(o3 >= 32, o3 <= 47))\"}'),(-46,-44, 30, 245, '{\"And(i4 == o4, o4 == {4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31,36,37,38,39,44,45,46,47,52,53,54,55,60,61,62,63})\"}'),(-56,-55, 30, 20, '{\"And(i5 != {4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31,36,37,38,39,44,45,46,47,52,53,54,55,60,61,62,63}, i5 >= 32, And(o5 >= 32, o5 >= 32, o5 <= 47, o5 != {4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31,36,37,38,39,44,45,46,47,52,53,54,55,60,61,62,63}))\"}')"

    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()
    printTable("F_nod",database,nodeMapping)
    input()
    
    start = time.time()
    program1.executeonce(conn)
    conn.commit()
    printTable("R_nod",database,nodeMapping)
    input()
    program2.execute(conn)
    printTable("R_nod",database,nodeMapping)
    # printTable("R_nod",database,nodeMapping, condition="dest = 245")
    input()
    database.delete(conn)
    exit()

if __name__ == "__main__":
    EC_example1()