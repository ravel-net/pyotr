"""
This is for generate policy data 
"""
import sys
from os.path import dirname, abspath
import os.path
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
print(root)
import psycopg2
from psycopg2.extras import execute_values
import databaseconfig as cfg
from Core.Datalog.program import DT_Program
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
from tabulate import tabulate
from copy import deepcopy
from time import time
from utils import parsing_utils
import random
import ipaddress

# IMPORTANT NOTE: TERNARY BIT VECTORS MUST START WITH #

DIFF = 10000000 # difference in the mapping of input and output variables (e.g. i1 = -1 => o1 = -DIFF-1)

DATABASE = cfg.postgres['db']
HOST = cfg.postgres['host']
USER = cfg.postgres['user']
PASSWORD = cfg.postgres['password']

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

def initializeDatabase(nodes, numRules, indexing_on, topology, cVarMapping):
    cvars = {}
    # for i in range(1,33):
    # for i in range(1,49):
    for i in range(numRules):
    # for i in nodes:
        cvars["i_"+str(i)] = "pkt_in" 
        cvars["o_"+str(i)] = "pkt_out" 

    R = DT_Table(name="R_nod", columns={"pkt_in":"bit_faure", "pkt_out":"bit_faure", "source":"integer","path":"integer[]","last_node":"integer","condition":"text[]"}, cvars=cvars, domain={"source":nodes,"last_node":nodes})

    F = DT_Table(name="F_"+topology, columns={"pkt_in":"bit_faure", "pkt_out":"bit_faure", "node":"integer", "next_hop":"integer","condition":"text[]"}, cvars=cvars, domain={"next_hop":nodes,"node":nodes})    

    database = DT_Database(tables=[F,R], cVarMapping=cVarMapping)
    R.delete(conn)
    R.initiateTable(conn)
    F.delete(conn)
    F.initiateTable(conn)

    if not indexing_on:
        F.deleteAllIndexes(conn)
        R.deleteAllIndexes(conn)
    conn.commit()

    return database

def getMapping(nodes):
    nodeIntMapping = {}
    nodeIntMappingReverse = {}
    i = 1
    for node in nodes:
        nodeIntMapping[node] = i+100
        nodeIntMappingReverse[i+100] = node
        i += 1
    return nodeIntMapping, nodeIntMappingReverse

# do IP formatting here
def getIP(ip, prefix):
    if "." in ip:
        if "'" not in ip:
            return "'"+ip+"/"+prefix+"'"
        else:
            return ip+"/"+prefix
        ipAddress = IPv4Address(ip)
        # ipAddressPrefix = IPv4Network(str(ipAddress) + "/" + prefix)
        return int(ipAddress)
    else:
        ipAddress = ipaddress.ip_address(int(ip)) # I2 dataset has direct IP addresses as int
        return "'{}/{}'".format(str(ipAddress), prefix)

def getOutputCondition(node, cvar, graph, nodeIntMapping):
    next_hops = []
    for next_hop in graph[node]:
        next_hops.append(str(nodeIntMapping[next_hop]))
    return "'{\"" + cvar + " == {" + ",".join(next_hops) + "}\"}'"
    # return "'{\"Or(" + ",".join(possibleOutputs) + ")\"}'"

def storeTable(tableName, inputs):
    cursor = conn.cursor()
    # cursor.execute("INSERT INTO {} VALUES {}".format(tableName, ",".join(inputs)))
    jump = 10000000
    startPoint = 0

    while startPoint+jump < len(inputs):
        cursor.execute("INSERT INTO {} VALUES {}".format(tableName, ",".join(inputs[startPoint:startPoint+jump])))
        print("adding {} to {}".format(startPoint, startPoint+jump))
        startPoint += jump
    if len(inputs) > startPoint:
        cursor.execute("INSERT INTO {} VALUES {}".format(tableName, ",".join(inputs[startPoint:])))
    conn.commit()

def runDatalog(db, nodeIntMappingReverse, nodeIntMapping, sourceNode = "atla", header = '1', simplification_on = True, F_name = "F"):
    source = nodeIntMapping[sourceNode]

    p1 = "R({header}, {source}, n, [{source}, n], {source}, n) :- {F_name}({header}, {source}, n)[n != {source}]".format(source=source, header=header, F_name=F_name)

    # p2 = "V({header}, p) :- R({header}, {source}, n2, p, second_laster, last_node), {F_name}({header}, n2, n)[n == p]\nR({header}, {source}, n, p || [n], last_node, n) :- R({header}, {source}, n2, p, second_laster, last_node), {F_name}({header}, n2, n)[n != second_laster]".format(source=source, header=header, F_name=F_name)
    # p2 = "R({header}, {source}, n, p || [n], last_node, n) :- R({header}, {source}, n2, p, second_laster, last_node), {F_name}({header}, n2, n)[n != second_laster]".format(source=source, header=header, F_name=F_name)
    p2 = "R({header}, {source}, n, p || [n], last_node, n) :- R({header}, {source}, n2, p, second_laster, last_node), {F_name}({header}, n2, n)[n != p]".format(source=source, header=header, F_name=F_name)
    # p2 = "V({header}, p) :- R({header}, {source}, n2, p, second_laster,last_node), F({header}, n2, n)[And(n == p, n != second_laster)]".format(source=source, header=header)
    program1 = DT_Program(p1, database=db, optimizations={"simplification_on":simplification_on})
    program2 = DT_Program(p2, database=db, optimizations={"simplification_on":simplification_on})
    start = time()
    program1.executeonce(conn)
    # program2.executeonce(conn)
    # printTable('F_I2', db, nodeIntMappingReverse)
    # input()
    # printTable('R', db, nodeIntMappingReverse)
    # input()
    # program2.executeonce(conn)
    # printTable('R', db, nodeIntMappingReverse)
    # input()
    # program2.executeonce(conn)
    # printTable('R', db, nodeIntMappingReverse)
    # input()
    # program2.executeonce(conn)
    # printTable('R', db, nodeIntMappingReverse)
    # input()
    # program2.executeonce(conn)
    # printTable('R', db, nodeIntMappingReverse)
    # input()
    program2.execute(conn, violationTables=[db.getTable("V")])
    end = time()
    conn.commit()
    # print("Total Time =", end-start)
    printTable('V', db, nodeIntMappingReverse)
    # program1.reasoning_tool.simplification("R", conn)
    return (end-start)  

def getLinks(topology="Stanford", backbonefile="backbone_topology.tf"):
    try:
        lines = []
        directory = topology+"_tf"
        with open(directory+"/"+backbonefile) as f:
            lines = f.readlines()
    except:
        print("Could not open input file {}. Exiting".format(backbonefile))
        exit()
    finally:
        links = {}
        for line in lines[2:]:
            node1 = line.split("$")[1][1:-1].strip()
            node2 = line.split("$")[7][1:-1].strip()
            if node1 not in links:
                links[node1] = []
            links[node1].append(node2)
            if node2 not in links:
                links[node2] = []
            links[node2].append(node1)
        return links

def runDatalogSimple(db, topology = "Stanford"):
    # p1 = "R_nod(pkt_in, pkt_out, 1500007, [n], n) :- F_{}(pkt_in, pkt_out, 1500007, n)[n != 1500007]".format(topology)
    p1 = "R_nod(pkt_in, pkt_out, 1500007, [n], n) :- F_{}(pkt_in, pkt_out, 1500007, n)[n != 1500007],(pkt_in == #xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx10101100000110110000101000100xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx)".format(topology)
    # p1 = "R_nod(pkt_in, pkt_out, S, [n], n) :- F_{}(pkt_in, pkt_out, S, n)[n != S],(pkt_in == #xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx0000000000000010)".format(topology)
    # p2 = "R_nod(pkt_in, new_pktout, S, p || [n2], n2) :- R_nod(pkt_in, pkt_out, S, p, n)[n2 != p], F_Stanford(pkt_out, new_pktout, n, n2)"
    p2 = "R_nod(pkt_in, new_pktout, 1500007, p || [n2], n2) :- R_nod(pkt_in, pkt_out, 1500007, p, n)[n2 != p], F_Stanford(pkt_out, new_pktout, n, n2)"

    program1 = DT_Program(p1, database=db, optimizations={"simplification_on":True}, bits = 128)
    program2 = DT_Program(p2, database=db, optimizations={"simplification_on":True}, bits = 128)
    program_naive = DT_Program(p1+"\n"+p2, database=db, optimizations={"simplification_on":True}, bits = 128, reasoning_engine="DoCSolver")
    conn.commit()

    start = time()
    # program_naive.simplifyInitial(conn=conn, target_table="F_Stanford")
    # program1.executeonce(conn)
    # conn.commit()
    # program2.execute(conn)
    program_naive.execute_semi_naive(conn)
    end = time()
    conn.commit()
    print("Total Time =", end-start)
    # db.getTable("R_nod").printTable(conn=conn, cVarMapping=db.cVarMapping)
    # program1.reasoning_tool.simplification("R", conn)
    return (end-start)  

def getTFRule(line, ruleNo, cVarMapping, links):
    separatedLine = line.split("$")
    action = separatedLine[0]
    in_ports = []
    in_ports_str = separatedLine[1][1:-1].strip().split(",")
    for port in in_ports_str:
        in_ports.append(port.strip())
    match = separatedLine[2]
    mask = separatedLine[3]
    rewrite = separatedLine[4]
    inverse_match = separatedLine[5]
    inverse_rewrite = separatedLine[6]
    out_ports = []
    out_ports_str = separatedLine[7][1:-1].strip().split(",")
    for port in out_ports_str:
        if port == "":
            continue
        port = port.strip()
        if port in links:
            for outer_port in links[port]:
                out_ports.append(outer_port)
        else:
            out_ports.append(port)

    not_rules = {}
    affected_by = separatedLine[8].strip().split(";")
    if len(affected_by) > 1:
        affected_by = affected_by[1:]
    i = 0
    while i < len(affected_by)-1:
        affected_node_str = affected_by[i+1].split("]")[0][1:].split(",")
        affected_node = []
        for a_node in affected_node_str:
            affected_node.append(a_node.strip())
        for a_node in affected_node:
            if a_node not in in_ports:
                print("Not condition found for node {} even though the in_ports are {}. Exiting".format(a_node, in_ports))
                print(line)
                exit()
            if a_node not in not_rules:
                not_rules[a_node] = []
            not_rules[a_node].append(affected_by[i])
        i += 2

    newRules = []
    newNodes = []
    if action != "fwd" and action != "rw":
        print("Unknown action {} found. Exiting".format(action))
        exit()
    if len(in_ports) == 0: # There must be a input port!
        print("No in port found. Exiting")
        exit()
    if len(out_ports) == 0: # this is for dropping packets. We forward dropped packets to port -1
        out_ports.append("-1")
        newNodes.append("-1")
    for in_port in in_ports:
        nodeNum = int(int(in_port)/100000)
        if int(in_port) % 100000 == 0:
            nodeNum += 16
        elif in_port in links:
            nodeNum += 32
        if in_port not in newNodes:
            newNodes.append(in_port)
        for out_port in out_ports:
            if out_port not in newNodes:
                newNodes.append(out_port)
            i_var = "i_"+str(ruleNo)
            o_var = "o_"+str(ruleNo)
            i_var_numeric = str(-1*ruleNo-5)
            o_var_numeric = str(-1*DIFF-ruleNo-5)
            # i_var = "i"+str(in_port)
            # o_var = "o"+str(in_port)
            # i_var_numeric = str(-1*int(in_port)-5)
            # o_var_numeric = str(-1*DIFF-int(in_port)-5)
            # i_var = "i_"+str(nodeNum)
            # o_var = "o_"+str(nodeNum)
            # i_var_numeric = str(-1*nodeNum-5)
            # o_var_numeric = str(-1*DIFF-nodeNum-5)
            if i_var_numeric in cVarMapping and cVarMapping[i_var_numeric] != i_var:
                print("Conflicting mapping of input numeric {} found: {} and {}. Exiting".format(i_var_numeric, i_var, cVarMapping[i_var_numeric]))
                exit()
            if o_var_numeric in cVarMapping and cVarMapping[o_var_numeric] != o_var:
                print("Conflicting mapping of input numeric {} found: {} and {}. Exiting".format(o_var_numeric, o_var,  cVarMapping[o_var_numeric]))
                exit()
            cVarMapping[i_var_numeric] = i_var
            cVarMapping[o_var_numeric] = o_var
            condition_arr = []
            condition_arr.append("{i_var} == #{match}".format(i_var=i_var, match=match))
            if in_port in not_rules:
                for tbv in not_rules[in_port]:
                    condition_arr.append("{i_var} != #{tbv}".format(i_var=i_var, tbv=tbv))

            if action == "rw":
                condition_arr.append("{o_var} == #{inverse_match}".format(o_var=o_var, inverse_match=inverse_match))
            else:
                condition_arr.append("{o_var} == {i_var}".format(o_var=o_var, i_var=i_var))
            condition = "'{\"And(" + ", ".join(condition_arr) + ")\"}'"
            newRules.append("('{i_var_numeric}','{o_var_numeric}',{in_port},{out_port},{condition})".format(i_var_numeric=i_var_numeric,o_var_numeric=o_var_numeric,in_port=in_port,out_port=out_port,condition=condition))
            ruleNo += 1
    return newRules, newNodes

def initializeForwardingTable(topology="Stanford", links={}):
    nodes = []
    directory = topology+"_tf"
    indexing_on = True
    rules = []
    cVarMapping = {}
    for file in os.scandir(directory):
        input_file = file.path
        lines = []
        if ".tf" not in input_file or "backbone" in input_file:
            continue
        try:
            with open(input_file) as f:
                lines = f.readlines()
        except:
            print("Could not open input file {}. Exiting".format(input_file))
            exit()
        finally:
            ruleNo = 0
            for line in lines[2:]: # skipping first two lines
                newRules, newNodes = getTFRule(line, ruleNo, cVarMapping, links)
                ruleNo += len(newRules)
                rules += newRules
                for node in newNodes:
                    if node not in nodes:
                        nodes.append(node)
    print("Number of rules", len(rules))
    print("Number of nodes", len(nodes))
    if len(rules) >= DIFF:
        print("Please increase the difference between the mapping of input and output variables. Current difference is {} whereas the number of rules are {}. Exiting".format(DIFF, len(rules)))
        exit()
    db = initializeDatabase(nodes=nodes, numRules=len(rules), indexing_on=indexing_on, topology=topology, cVarMapping=cVarMapping)
    storeTable(tableName = "F_"+topology, inputs=rules)
    F_table = db.getTable("F_"+topology)
    conn.commit()
    print("Added rules to F_"+topology)
    if indexing_on:
        F_table.enableIndexing(conn, "node")
        F_table.enableIndexing(conn, "next_hop")
    return db
    # timeTaken = runDatalog(db=db, nodeIntMappingReverse=nodeIntMappingReverse, nodeIntMapping=nodeIntMapping, sourceNode=source, header=header, simplification_on=simplification_on, F_name="F_"+topology)
    # time_taken_arr.append(timeTaken)

if __name__ == '__main__':
    links = getLinks(topology="Stanford", backbonefile="backbone_topology.tf")
    db = initializeForwardingTable(topology="Stanford", links=links)
    runDatalogSimple(db=db, topology="Stanford")
    # if len(sys.argv) < 3 or (sys.argv[1] != "verify" and sys.argv[1] != "generate"):
    #     print("Program requires at least 1 parameter with the first parameter either 'verify' or 'generate'. Exiting")
    #     exit()

    # if sys.argv[1] == "verify":
    #     verify(sys.argv[2:])
    # else:
    #     generate(sys.argv[2:])
# Loop
# python3 flash_experiments.py airtel s14-5 1 True False airtel-small.csv,airtel-cleaned.csv s15-5 all s9-7 all s15-1 all



# Generate
#  python3 flash_experiments.py generate L2_112_48 L2_112_48-10-random-1 10 random random _ random 1

# Verify
# python3 flash_experiments.py verify L2_112_48 inputs/L2_112_48-10-random-0 True True _


# Correctness test
# python3 flash_experiments.py verify I2 inputs/I2-loop.txt True True trace-loop-hous.txt