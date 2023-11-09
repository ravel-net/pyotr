import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
print(root)
from Core.Datalog.program import DT_Program
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
import psycopg2 
import databaseconfig as cfg
import time

import sys
from os.path import dirname, abspath
root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)
from Core.Datalog.program import DT_Program
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
from Core.Datalog.conditionTree import ConditionTree
import psycopg2 
import databaseconfig as cfg
from tabulate import tabulate
from copy import deepcopy
from Backend.reasoning.CUDD.BDDTools import BDDTools

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

# Example taken from NoD (Checking beliefs in networks) Figure 1
# Nodes are represented as integers. C-variables are represented as negative integers. The mapping from text to integer is given below
# R1 = 10, R2 = 20, R3 = 30, B = 123, D = 245
# i1 = -16, i2 = -26, i3 = -36, i4 = -46, i5 = -56
# o1 = -11, o2 = -22, o3 = -33, o4 = -44, o5 = -55
def DoC_example1():
    cVarMapping = {"-16":"i_1","-26":"i_2","-36":"i_3","-46":"i_4","-56":"i_5","-11":"o_1","-22":"o_2","-33":"o_3","-44":"o_4","-55":"o_5"}

    variables = []
    for i in cVarMapping:
        variables.append(cVarMapping[i])

    R_nod = DT_Table(name="R_ordering", columns={"pkt_out":"bit_faure", "source":"integer","path":"integer[]","last_node":"integer","condition":"text[]"}, cvars={"o_1":"pkt_out","o_2":"pkt_out","o_3":"pkt_out","o_4":"pkt_out","o_5":"pkt_out"}, domain={"source":[10,20,30,40,123,245],"dest":[10,20,30,40,123,245],"last_node":[10,20,30,40,123,245]})

    F_nod = DT_Table(name="F_nod", columns={"pkt_in":"bit_faure", "pkt_out":"bit_faure", "node":"integer", "next_hop":"integer","condition":"text[]"}, cvars={"i_1":"pkt_in","i_2":"pkt_in","i_3":"pkt_in","i_4":"pkt_in","i_5":"pkt_in", "o_1":"pkt_out","o_2":"pkt_out","o_3":"pkt_out","o_4":"pkt_out","o_5":"pkt_out"}, domain={"next_hop":[10,20,30,40,123,245],"node":[10,20,30,40,123,245]})

    database = DT_Database(tables=[R_nod,F_nod], cVarMapping = cVarMapping)
    p1 = "R_ordering(pkt_out, 10, [n], n) :- F_nod(pkt_in, pkt_out, 10, n)[n != 10]" # only trasfers to D
    p2 = "R_ordering(new_pktout, 10, p || [n2], n2) :- R_ordering(pkt_out, 10, p, n)[n2 != p], F_nod(pkt_out, new_pktout, n, n2)"
    p3 = p1+"\n"+p2
    program_semi = DT_Program(p3, database=database, optimizations={"simplification_on":True}, bits = 6, reasoning_engine="DoCSolver")
    nodeMapping = {'10':"R1",'20':"R2",'30':"R3",'123':"B",'245':"D"}
    database.initiateDB(conn)
    conn.commit()

    '''
    The sql below creates the table below:
    pkt_in    pkt_out    node    next_hop    condition
    --------  ---------  ------  ----------  --------------------------------------------------------
    i_1       o_1        R1      R2          ['And(i_1 == #10x01x, o_1 == i_1)']
    i_2       o_2        R1      R3          ['And(And(i_2 == #1xxxxx, i_2 != #10x01x), o_2 == i_2)']
    i_3       o_3        R2      B           ['And(i_3 == #10xxxx, o_3 == i_3)']
    i_4       o_4        R3      D           ['And(i_4 == #xxx1xx, o_4 == i_4)']
    i_5       o_5        R3      R2          ['And(i_5 == #1xx0xx, o_5 == #10xxxx)']
    '''
    sql = "insert into F_nod values ('-16','-11', 10, 20, '{\"And(i_1 == #10x01x, o_1 == i_1)\"}'),('-26','-22', 10, 30, '{\"And(o_2 == i_2, i_2 != #10x01x, i_2 == #1xxxxx)\"}'),('-36','-33', 20, 123, '{\"And(o_3 == i_3, i_3 == #10xxxx)\"}'),('-46','-44', 30, 245, '{\"And(o_4 == i_4, i_4 == #xxx1xx)\"}'),('-56','-55', 30, 20, '{\"And(i_5 != #xxx1xx, i_5 == #1xxxxx, o_5 == #x0xxxx)\"}')"

    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()

    program_semi.execute_semi_naive(conn)
    program_semi.restoreStringConditions(conn)
    conn.commit()
    printTable("R_ordering", database, nodeMapping)
    printTable("F_nod", database, nodeMapping)
    exit()
    print(end-start)
    database.delete(conn)

# Example taken from NoD (Checking beliefs in networks) Figure 1
# Nodes are represented as integers. C-variables are represented as negative integers. The mapping from text to integer is given below
# Note that for BDD we use an extra column called the tranformer which is used to rewrite conditions. This allows us to reduce the number of variables in the table (we just use a single variable, i_1, to represent all packets)
# R1 = 10, R2 = 20, R3 = 30, B = 123, D = 245
# i1 = -16
def BDD_example1():
    cVarMapping = {"-16":"i_1"}

    variables = []
    for i in cVarMapping:
        variables.append(cVarMapping[i])

    R_nod = DT_Table(name="R_ordering", columns={"pkt_out":"bit_faure", "source":"integer","path":"integer[]","last_node":"integer","condition":"text[]"}, cvars={"i_1":"pkt_out"}, domain={"source":[10,20,30,40,123,245],"dest":[10,20,30,40,123,245],"last_node":[10,20,30,40,123,245]})

    F_nod = DT_Table(name="F_nod", columns={"pkt_in":"bit_faure", "pkt_out":"bit_faure", "node":"integer", "next_hop":"integer","transformer":"text[]", "condition":"text[]"}, cvars={"i_1":"pkt_in"}, domain={"next_hop":[10,20,30,40,123,245],"node":[10,20,30,40,123,245]})

    database = DT_Database(tables=[R_nod,F_nod], cVarMapping = cVarMapping)
    p1 = "R_ordering(pkt_out, 10, [n], n) :- F_nod(pkt_in, pkt_out, 10, n)[n != 10]" # only trasfers to D
    p2 = "R_ordering(new_pktout, 10, p || [n2], n2) :- R_ordering(pkt_out, 10, p, n)[n2 != p], F_nod(pkt_out, new_pktout, n, n2)"
    p3 = p1+"\n"+p2
    program_semi = DT_Program(p3, database=database, optimizations={"simplification_on":True}, bits = 6, reasoning_engine="bdd")
    database.initiateDB(conn)
    conn.commit()
    nodeMapping = {'10':"R1",'20':"R2",'30':"R3",'123':"B",'245':"D"}

    '''
    The sql below creates the table below:
    pkt_in    pkt_out    node    next_hop    transformer                condition
    --------  ---------  ------  ----------  ---------------------      --------------------------------------------------------
    i_1       i_1        R1      R2                                     ['i_1 == #10*01*']
    i_1       i_1        R1      R3                                     ['And(i_1 == #1*****, i_1 != #10*01*)']
    i_1       i_1        R2      B                                      ['i_1 == #10****']
    i_1       i_1        R3      D                                      ['i_1 == #***1**']
    i_1       i_1        R3      R2          ['i_1 == #*0****']         ['And(i_1 == #1*****, i_1 != #***1**)']
    '''
    sql = "insert into F_nod values ('-16','-16', 10, 20, '{}','{\"i_1 == #10*01*\"}'),('-16','-16', 10, 30, '{}','{\"And(i_1 != #10*01*, i_1 == #1*****)\"}'),('-16','-16', 20, 123, '{}','{\"i_1 == #10****\"}'),('-16','-16', 30, 245, '{}','{\"i_1 == #***1**\"}'),('-16','-16', 30, 20, '{\"i_1 == #*0****\"}','{\"And(i_1 != #***1**, i_1 == #1*****\"}')"

    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()

    program_semi.execute_semi_naive(conn)
    conn.commit()
    printTable("R_ordering", database, nodeMapping)
    printTable("F_nod", database, nodeMapping)
    
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

def replaceVal(val, mapping):
    if val in mapping:
        return mapping[val]
    elif str(val) in mapping:
        return mapping[str(val)]
    # elif type(val) == str:
    #     conditions = ConditionTree(val)
    #     return conditions.toString(mode = "Replace String", replacementDict = mapping)
    else:
        return val
    
if __name__ == "__main__":
    BDD_example1()
    # DoC_example1()
    # EC_example1()
    # EC_example2()