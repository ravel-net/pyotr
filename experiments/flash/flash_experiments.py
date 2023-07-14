"""
This is for generate policy data 
"""
import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
import psycopg2
from psycopg2.extras import execute_values
import databaseconfig as cfg
from Core.Datalog.program import DT_Program
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
from tabulate import tabulate
from ipaddress import IPv4Network, IPv4Address
from copy import deepcopy

DATABASE = cfg.postgres['db']
HOST = cfg.postgres['host']
USER = cfg.postgres['user']
PASSWORD = cfg.postgres['password']

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

def loadTopology(topologyFile):
    nodes = []
    portMapping = {}
    graph = {}
    with open(topologyFile) as f:
        lines = f.readlines()
        for line in lines:
            splitLine = line.split(",")
            node1 = splitLine[0].strip()
            port1 = splitLine[1].strip()
            node2 = splitLine[2].strip()
            port2 = splitLine[3].strip()
            if node1 not in nodes:
                nodes.append(node1)
                graph[node1] = []
            if node2 not in nodes:
                nodes.append(node2)
                graph[node2] = []

            if node1 not in graph[node2]:
                graph[node2].append(node1)
            if node2 not in graph[node1]:
                graph[node1].append(node2)

            portName1 = node1+"_"+port1
            portName2 = node2+"_"+port2

            if portName1 in portMapping and portMapping[portName1] != node2:
                print("Same port {} used for different next hops: {} and {}. Exiting".format(portName1, node2, portMapping[portName1]))
                exit()
            if portName2 in portMapping and portMapping[portName2] != node1:
                print("Same port {} used for different next hops: {} and {}. Exiting".format(portName2, node1, portMapping[portName2]))                
                exit()
            portMapping[portName1] = node2
            portMapping[portName2] = node1
    return portMapping, graph, nodes
            
def initializeDatabases(nodes, nodesToIgnore, nodeIntMapping):
    cvars = {}
    for node, prefixes in nodesToIgnore.items():
        if type(prefixes) == str and prefixes == "all":
            cvars[node+"_header"] = "header" #cvar name is node_header e.g. sans_header
            cvars[node+"_next"] = "next_hop" #cvar name is node_header e.g. sans_header
        else:
            for prefix in prefixes:
                cvars[node+"_"+str(prefix)] = "next_hop" # e.g. sans_691538

    allowedNodes = []
    for node in nodeIntMapping:
        intRep = nodeIntMapping[node]
        if intRep not in allowedNodes:
            allowedNodes.append(intRep)
    
    R = DT_Table(name="R", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","second_laster":"integer_faure","last_node":"integer_faure","condition":"text[]"}, cvars={"p":"path"}, domain={"next_hop":allowedNodes,"node":allowedNodes,"second_laster":allowedNodes})

    V = DT_Table(name="V", columns={"header":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"}, domain={"next_hop":allowedNodes,"node":allowedNodes,"second_laster":allowedNodes})

    F = DT_Table(name="F", columns={"header":"integer_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars=cvars, domain={"next_hop":allowedNodes,"node":allowedNodes})

    mapping_index = -1
    cvarMapping = {}
    for cvar in cvarMapping:
        cvarMapping[mapping_index] = cvar
        mapping_index -= 1

    database = DT_Database(tables=[F,R,V], cVarMapping=cvarMapping)
    database.initiateDB(conn)
    conn.commit()

    return database

def getMapping(nodes):
    nodeIntMapping = {}
    nodeIntMappingReverse = {}
    i = 1
    for node in nodes:
        nodeIntMapping[node] = i*100
        nodeIntMappingReverse[i*100] = node
        i += 1
    return nodeIntMapping, nodeIntMappingReverse

# do IP formatting here
def getIP(ip, prefix):
    ipAddress = IPv4Address(int(ip))
    ipAddressPrefix = IPv4Network(str(ipAddress) + "/" + prefix)
    return int(ip)

def getOutputCondition(node, cvar, graph, nodeIntMapping):
    possibleOutputs = []
    for next_hop in graph[node]:
        possibleOutputs.append(cvar + " == " + str(nodeIntMapping[next_hop]))
    return "'{\"Or(" + ",".join(possibleOutputs) + ")\"}'"

def storeTable(tableName, inputs):
    cursor = conn.cursor()
    cursor.execute("INSERT INTO {} VALUES {}".format(tableName, ",".join(inputs)))
    conn.commit()

def addFW(dataset, nodesToIgnore, portMapping, graph, nodeIntMapping, db):
    inputs = [] # list of inputs of the form [(header, source, next_hop, condition),...]
    with open(dataset) as f:
        lines = f.readlines()
        for line in lines:
            splitLine = line.split(" ")
            isAdd = splitLine[0].strip()
            delay = splitLine[1].strip()
            epoch = splitLine[2].strip()
            node = splitLine[3].strip()
            ip = splitLine[4].strip()
            prefix = splitLine[5].strip()
            port = splitLine[6].strip()
            isEnd = splitLine[7].strip()
            intIP = getIP(ip, prefix)

            if node in nodesToIgnore:
                prefixes = nodesToIgnore[node]
                if type(prefixes) == str and prefixes == "all":
                    condition = getOutputCondition(node=node, cvar=node+"_next", graph=graph, nodeIntMapping=nodeIntMapping)
                    header_mapped = db.cVarMappingReverse[node+"_header"]
                    next_hop_mapped = db.cVarMappingReverse[node+"_next"]
                    input = "({},{},{},{})".format(header_mapped, nodeIntMapping[node], next_hop_mapped, condition)
                    inputs.append(input)
                    continue
                elif intIP in prefixes:
                    condition = getOutputCondition(node=node, cvar=node+"_"+str(intIP), graph=graph, nodeIntMapping=nodeIntMapping)
                    next_hop_mapped = db.cVarMappingReverse[node+"_"+str(intIP)]
                    input = "({},{},{},{})".format(intIP, nodeIntMapping[node], next_hop_mapped, condition)
                    inputs.append(input)
                    continue
            
            condition = "'{}'"
            if node+"_"+port not in portMapping:
                print("skipping")
                continue
            next_hop_node = portMapping[node+"_"+port]
            input = "({},{},{},{})".format(intIP, nodeIntMapping[node], nodeIntMapping[next_hop_node], condition)
            inputs.append(input)
    
    storeTable("F", inputs)

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
def printTable(tableName, db, nodeIntMappingReverse):
    cursor = conn.cursor()
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
    print(tabulate(newTable, headers=headerInArray))

def runDatalog(db, nodeIntMappingReverse, nodeIntMapping):
    source = nodeIntMapping["atla"]
    header = "X"
    
    p1 = "R({header}, {source}, n, [{source}, n], {source}, n) :- F({header}, {source}, n)[n != {source}]\nV({header}, p) :- R({header}, {source}, n2, p, second_laster,last_node), F({header}, n2, n)[And(n == p, n != second_laster)]\nR({header}, {source}, n, p || [n], last_node, n) :- R({header}, {source}, n2, p, second_laster, last_node), F({header}, n2, n)[n != second_laster]".format(source=source, header=header)
    program1 = DT_Program(p1, database=db, optimizations={"simplification_on":True})
    # program1.executeonce(conn)
    # printTable("R",db,nodeIntMappingReverse)
    # input()
    # program1.executeonce(conn)
    # printTable("R",db,nodeIntMappingReverse)
    # input()
    # program1.executeonce(conn)
    # printTable("R",db,nodeIntMappingReverse)
    # input()
    # program1.executeonce(conn)
    # printTable("R",db,nodeIntMappingReverse)
    # input()
    # program1.execute(conn, violationTables=[db.getTable("V")])
    conn.commit()

# python3 flash_experiments.py topology dataset1,dataset2,dataset3,... nodeIgnore1 [all/list of prefixes] nodeIgnore2 [all/list of prefixes]
if __name__ == '__main__':
    if len(sys.argv) < 3:
        print("Program requires at least 2 parameters (topology and at least 1 dataset). Usage: python3 flash_experiments.py topology dataset1,dataset2,dataset3,... nodeIgnore1 [all/list of prefixes] nodeIgnore2 [all/list of prefixes]")
        exit()
    topologyFile = sys.argv[1]
    datasetFiles = sys.argv[2].split(',')
    nodesToIgnore = {} #key is node to ignore, value is either all or a list of prefixes to ignore
    i = 3
    while i < len(sys.argv):
        node = sys.argv[i]
        prefixes = sys.argv[i+1].split(",")
        if prefixes[0] == "all":
            nodesToIgnore[node] = "all"
        else:
            prefixList = []
            for prefix in prefixes:
                prefixList.append(int(prefix))
            nodesToIgnore[node] = prefixList
        i += 2
    # initialize databases
    # load topology to get port to node mapping, possible next hops for all nodes, nodes list
    portMapping, graph, nodes = loadTopology(topologyFile)
    # print(portMapping)
    print(graph)
    # print(nodesToIgnore)
    # print(nodes)
    nodeIntMapping, nodeIntMappingReverse = getMapping(nodes) # each node is represented by an integer
    db = initializeDatabases(nodes, nodesToIgnore, nodeIntMapping) # cvarmapping is int to 
    # for loop over databases with nodesToIgnore, ports mapping, and next hops as arguments
    for dataset in datasetFiles:
        addFW(dataset, nodesToIgnore, portMapping, graph, nodeIntMapping, db)

    runDatalog(db, nodeIntMappingReverse, nodeIntMapping)
    printTable("V", db, nodeIntMappingReverse)
    # run datalog program
