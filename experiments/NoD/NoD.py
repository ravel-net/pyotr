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
import time
from utils import parsing_utils
import random
import ipaddress
import logging

# IMPORTANT NOTE: TERNARY BIT VECTORS MUST START WITH #

DIFF = 10000000 # difference in the mapping of input and output variables (e.g. i1 = -1 => o1 = -DIFF-1)

DATABASE = cfg.postgres['db']
HOST = cfg.postgres['host']
USER = cfg.postgres['user']
PASSWORD = cfg.postgres['password']

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

def initializeDatabase(nodes, numRules, indexing_on, topology, cVarMapping, engine="bdd"):
    cvars = {}
    if engine == "bdd":
        cvars["i_1"] = "pkt_in"
        cvars["i_1"] = "pkt_out"
        F = DT_Table(name="F_"+topology, columns={"pkt_in":"bit_faure", "pkt_out":"bit_faure", "node":"integer", "next_hop":"integer","transformer":"text[]","condition":"text[]"}, cvars=cvars, domain={"next_hop":nodes,"node":nodes})   
    elif engine == "DoCSolver":
        for i in range(numRules):
            cvars["i_"+str(i)] = "pkt_in" 
            cvars["o_"+str(i)] = "pkt_out" 
        F = DT_Table(name="F_"+topology, columns={"pkt_in":"bit_faure", "pkt_out":"bit_faure", "node":"integer", "next_hop":"integer","condition":"text[]"}, cvars=cvars, domain={"next_hop":nodes,"node":nodes})    


    R = DT_Table(name="R_nod", columns={"pkt_in":"bit_faure", "pkt_out":"bit_faure", "source":"integer","path":"integer[]","last_node":"integer","condition":"text[]"}, cvars=cvars, domain={"source":nodes,"last_node":nodes})


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

# p1 = "R_nod(pkt_in, pkt_out, 1500007, [n], n) :- F_{}(pkt_in, pkt_out, 1500007, n)[n != 1500007]".format(topology)
# p1 = "R_nod(pkt_in, pkt_out, 1100004, [n], n) :- F_{}(pkt_in, pkt_out, 1100004, n)[n != 1100004]".format(topology)#xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx0000000000000010)".format(topology)
# p2 = "R_nod(pkt_in, new_pktout, S, p || [n2], n2) :- R_nod(pkt_in, pkt_out, S, p, n)[n2 != p], F_Stanford(pkt_out, new_pktout, n, n2)"
def runDatalogSimple(db, topology = "Stanford", sourceNode="1500007", engine="bdd"):
    # p1 = "R_nod(pkt_in, pkt_out, {sourceNode}, [n], n) :- F_Stanford(pkt_in, pkt_out, {sourceNode}, n)[n != {sourceNode}],(pkt_in == #xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx01001010)".format(sourceNode=sourceNode)
    p1 = "R_nod(pkt_in, pkt_out, {sourceNode}, [n], n) :- F_Stanford(pkt_in, pkt_out, {sourceNode}, n)[n != {sourceNode}],(pkt_in == #xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx)".format(sourceNode=sourceNode)
    p2 = "R_nod(pkt_in, new_pktout, {sourceNode}, p || [n2], n2) :- R_nod(pkt_in, pkt_out, {sourceNode}, p, n)[n2 != p], F_Stanford(pkt_out, new_pktout, n, n2)".format(sourceNode=sourceNode)

    program_naive = DT_Program(p1+"\n"+p2, database=db, optimizations={"simplification_on":True}, bits = 128, reasoning_engine=engine)
    conn.commit()

    start = time.time()
    # program_naive.simplifyInitial(conn=conn, target_table="F_Stanford")
    # program1.executeonce(conn)
    # conn.commit()
    # program2.execute(conn)
    iterationEndMapping = program_naive.execute_semi_naive(conn)
    end = time.time()
    conn.commit()
    if engine == "bdd":
        program_naive.reasoning_tool.quit()
    print("Total Time =", end-start)
    # db.getTable("R_nod").printTable(conn=conn, cVarMapping=db.cVarMapping)
    # program1.reasoning_tool.simplification("R", conn)
    length = iterationEndMapping["R_nod"].split("_")[2]
    return length  

# Gets the input match and the output and returns the bits that were rewritten
def getRewriteBits(match, inverse_match):
    numBits = len(match)
    i = 0 
    answer = ""
    while i < numBits:
        matchBit = match[i]
        inverseBit = inverse_match[i]
        if matchBit != inverseBit:
            answer += inverseBit
        else:
            answer += 'x'
        i += 1
    return answer


def getTFRule(line, ruleNo, cVarMapping, links, engine="bdd"):
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
        if engine == "bdd":
            for out_port in out_ports:
                if out_port not in newNodes:
                    newNodes.append(out_port)
                i_var = "i_1"
                i_var_numeric = str(-1*1-5)
                if i_var_numeric in cVarMapping and cVarMapping[i_var_numeric] != i_var:
                    print("Conflicting mapping of input numeric {} found: {} and {}. Exiting".format(i_var_numeric, i_var, cVarMapping[i_var_numeric]))
                    exit()
                cVarMapping[i_var_numeric] = i_var
                condition_arr = []
                transformer_arr = []
                condition_arr.append("{i_var} == #{match}".format(i_var=i_var, match=match))
                if in_port in not_rules:
                    for tbv in not_rules[in_port]:
                        condition_arr.append("{i_var} != #{tbv}".format(i_var=i_var, tbv=tbv))
            
                if action == "rw":
                    rewriteBits = getRewriteBits(match, inverse_match)
                    transformer_arr.append("{i_var} == #{rewriteBits}".format(i_var=i_var, rewriteBits=rewriteBits))

                condition = "'{\"And(" + ", ".join(condition_arr) + ")\"}'" 
                if len(transformer_arr) == 1:
                    transformer =  '\'{\"' + transformer_arr[0] + "\"}\'"
                else:
                    transformer = "'{}'"
                newRules.append("('{i_var_numeric}','{i_var_numeric}',{in_port},{out_port},{transformer},{condition})".format(i_var_numeric=i_var_numeric,in_port=in_port,out_port=out_port,condition=condition, transformer=transformer))
                ruleNo += 1
        elif engine == "DoCSolver":
            for out_port in out_ports:
                if out_port not in newNodes:
                    newNodes.append(out_port)
                i_var = "i_"+str(ruleNo)
                o_var = "o_"+str(ruleNo)
                i_var_numeric = str(-1*ruleNo-5)
                o_var_numeric = str(-1*DIFF-ruleNo-5)
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

def initializeForwardingTable(topology="Stanford", links={}, randomRuleIndex=[], engine="bdd"):
    nodes = []
    directory = topology+"_tf"
    indexing_on = False
    rules = []
    cVarMapping = {}
    allFiles = []
    pickedFiles = []
    numPicks = 0
    for file in os.listdir(directory):
        if ".tf" not in file or "backbone" in file:
            continue
        allFiles.append(file)
    allFiles.sort()
    for file in allFiles:
        lines = []
        if ".tf" not in file or "backbone" in file:
            continue
        input_file = directory + "/" + file
        try:
            with open(input_file) as f:
                lines = f.readlines()
        except:
            print("Could not open input file {}. Exiting".format(input_file))
            exit()
        finally:
            if numPicks == size:
                break
            pickedFiles.append(file)
            numPicks += 1
            ruleNo = 0
            for line in lines[2:]: # skipping first two lines
                newRules, newNodes = getTFRule(line, ruleNo, cVarMapping, links, engine=engine)
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

    newRules = []
    for i in randomRuleIndex:
        newRules.append(rules[i])
    pickedNodes = []
    for rule in newRules:
        pickedNodes.append(rule.split(",")[2].strip())

    db = initializeDatabase(nodes=nodes, numRules=len(newRules), indexing_on=indexing_on, topology=topology, cVarMapping=cVarMapping, engine=engine)
    storeTable(tableName = "F_"+topology, inputs=newRules)
    F_table = db.getTable("F_"+topology)
    conn.commit()
    print("Added rules to F_"+topology)
    if indexing_on:
        F_table.enableIndexing(conn, "node")
        F_table.enableIndexing(conn, "next_hop")
    return db, pickedNodes, pickedFiles
    # timeTaken = runDatalog(db=db, nodeIntMappingReverse=nodeIntMappingReverse, nodeIntMapping=nodeIntMapping, sourceNode=source, header=header, simplification_on=simplification_on, F_name="F_"+topology)
    # time_taken_arr.append(timeTaken)
def analyze(size, pathlength, filename="program.log", outputfile="LoRa.dat"):
    sums = {}
    with open(filename) as f:
        lines = f.readlines()
        for line in lines:
            if "Time" in line:
                data = line.split()
                function = data[1]
                time = float(data[-1])
                if function not in sums:
                    sums[function] = []
                sums[function].append(time)

    with open(outputfile,"a") as f:
        executeTime = sum(sums["semi_executeTime"])
        dbTime = sum(sums["db_engine"])
        reasoningTime = sum(sums["reasoning_engine"])
        executeTimeRemaining = executeTime-dbTime-reasoningTime
        if executeTimeRemaining < 0:
            return -1
        f.write("{}\t{}\t{}\t{}\t{}\n".format(str(size), str(dbTime), str(reasoningTime), str(executeTimeRemaining), str(pathlength)))
    return 0

if __name__ == '__main__':
    engines = ["bdd", "DoCSolver"]
    # engines = ["bdd"]
    logfile = "program.log"
    connectedNodes = []
    numRules = 17180
    links = getLinks(topology="Stanford", backbonefile="backbone_topology.tf")
    for node in links:
        connectedNodes.append(node)
    size = int(sys.argv[1]) # take input
    print(size)
    randomRuleIndex = random.sample(range(0,numRules), size)
    if size == numRules:
        randomRuleIndex = range(0,numRules)
    db, nodes, _ = initializeForwardingTable(topology="Stanford", links=links, randomRuleIndex=randomRuleIndex, engine="bdd")
    pickedNode = ""
    while pickedNode == "":
        pickedNode = random.sample(nodes, 1)[0]
        if pickedNode not in connectedNodes:
            pickedNode = ""
    db.delete(conn)  

    for engine in engines:
        db, _, _ = initializeForwardingTable(topology="Stanford", links=links, randomRuleIndex=randomRuleIndex, engine=engine)
        outputFile = engine+"_"+str(size)+".txt"
        # with open(outputFile,"a") as f:
        #     f.write("Size\tDB\tReasoning\tSystem\n")
        # runDatalogSimple(db=db, topology="Stanford", sourceNode=sourceNode, engine=engine)
        pathlength = runDatalogSimple(db=db, topology="Stanford", sourceNode=pickedNode, engine=engine)
        db.delete(conn)
        logging.shutdown()
        returnVal = analyze(size, pathlength, logfile, outputFile)
        time.sleep(2)
        if returnVal < 0 or pathlength == 0:
            os.remove(logfile)
            break
        os.remove(logfile)

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