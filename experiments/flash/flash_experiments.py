"""
This is for generate policy data 
"""
import sys
from os.path import dirname, abspath
import os.path
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
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



DATABASE = cfg.postgres['db']
HOST = cfg.postgres['host']
USER = cfg.postgres['user']
PASSWORD = cfg.postgres['password']

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

# reads Airtel.csv and generates the topology. We treat each port as a separate node
def createAirtelTopo(topologyFile, airtelDatasetName = "airtel/airtel.csv"):
    try:
        f = open(airtelDatasetName, 'r')
        lines = f.readlines()
    except:
        print("File {} not found for creating airtel topo. Exiting".format(airtelDatasetName))
        exit()
    finally:
        nodes = []
        graph = {}
        for line in lines:
            splitLine = line.split(",")
            node1 = splitLine[1].strip()
            node2 = splitLine[2].strip()
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

        with open(topologyFile, 'w') as topo:
            for node1 in graph:
                for node2 in graph[node1]:
                    topo.write("{},{},{},{}\n".format(node1,node2,node2,node1))

def loadTopology(topology):
    nodes = []
    portMapping = {}
    graph = {}
    topologyFile = "{}/{}_Topo".format(topology, topology)
    if topology == "airtel" and not os.path.isfile(topologyFile):
        createAirtelTopo(topologyFile)
    try:
        f = open(topologyFile, 'r')
        lines = f.readlines()
    except:
        print("File {} not found for loading topology. Exiting".format(topologyFile))
        exit()
    finally:
        for line in lines:
            if len(line) < 2: #empty space
                continue
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

def initializeDatabases(nodes, nodesToIgnore, nodeIntMapping, indexing_on):
    cvars = {}
    for node, prefixes in nodesToIgnore.items():
        if type(prefixes) == str and prefixes == "all":
            cvars[node+"_header"] = "header" #cvar name is node_header e.g. sans_header
            cvars[node+"_next"] = "next_hop" #cvar name is node_header e.g. sans_header
        else:
            for prefix in prefixes:
                cvars[node+"_"+str(prefix).replace(".","")] = "next_hop" # e.g. sans_691538
    allowedNodes = []
    for node in nodeIntMapping:
        intRep = nodeIntMapping[node]
        if intRep not in allowedNodes:
            allowedNodes.append(intRep)
    
    # R = DT_Table(name="R", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","second_laster":"integer_faure","last_node":"integer_faure","condition":"text[]"}, cvars={"p":"path"}, domain={"next_hop":allowedNodes,"node":allowedNodes,"second_laster":allowedNodes})
    R = DT_Table(name="R", columns={"header":"inet_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","second_laster":"integer","last_node":"integer","condition":"text[]"}, cvars={"p":"path"}, domain={"next_hop":allowedNodes,"node":allowedNodes,"second_laster":allowedNodes})

    V = DT_Table(name="V", columns={"header":"inet_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"}, domain={"next_hop":allowedNodes,"node":allowedNodes,"second_laster":allowedNodes})

    F = DT_Table(name="F", columns={"header":"inet_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars=cvars, domain={"next_hop":allowedNodes,"node":allowedNodes})

    # mapping_index = -200
    # cvarMapping = {}
    # for cvar in cvars:
    #     cvarMapping[str(mapping_index)] = cvar
    #     mapping_index -= 1

    # database = DT_Database(tables=[F,R,V], cVarMapping=cvarMapping)
    database = DT_Database(tables=[F,R,V])
    # R.delete(conn)
    # R.initiateTable(conn)
    # V.delete(conn)
    # V.initiateTable(conn)
    database.delete(conn)
    database.initiateDB(conn)

    if indexing_on:
        F.enableIndexing(conn, "header", using="gist")
        F.enableIndexing(conn, "node")
        F.enableIndexing(conn, "next_hop")
        R.enableIndexing(conn, "header", using="gist")
        R.enableIndexing(conn, "dest")
        R.enableIndexing(conn, "source")
        R.enableIndexing(conn, "second_laster")
        R.enableIndexing(conn, "last_node")
        R.enableIndexing(conn, "path", using="GIN")
    else:
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
        return "'"+ip+"/"+prefix+"'"
        ipAddress = IPv4Address(ip)
        # ipAddressPrefix = IPv4Network(str(ipAddress) + "/" + prefix)
        return int(ipAddress)
    else:
        ipAddress = ipaddress.ip_address(int(ip)) # I2 dataset has direct IP addresses as int
        return "'{}/{}'".format(str(ipAddress), prefix)

def getOutputCondition(node, cvar, graph, nodeIntMapping):
    possibleOutputs = []
    for next_hop in graph[node]:
        possibleOutputs.append(cvar + " == " + str(nodeIntMapping[next_hop]))
    return "'{\"Or(" + ",".join(possibleOutputs) + ")\"}'"

def storeTable(tableName, inputs):
    cursor = conn.cursor()
    cursor.execute("INSERT INTO {} VALUES {}".format(tableName, ",".join(inputs)))
    conn.commit()

# takes into account deletions of prefixes
# does not take longest prefix matching into account
def cleanAirtelDataset(topology='airtel',datasetName='airtel.csv'):
    dataset = "{}/{}".format(topology, datasetName)
    with open(dataset) as f:
        lines = f.readlines()
        insertions = {} 
        for line in lines:
            splitLine = line.split(",")
            node = splitLine[1].strip()
            ipPart = splitLine[0].strip().split("/")
            updateType = ipPart[0][0]
            ip = ipPart[0][1:] # ignoring the '+' or '-' sign
            prefix = ipPart[1]
            port = splitLine[2].strip()
            intIP = getIP(ip, prefix)
            updateName = str(intIP)+"_"+node
            if updateType == "+":
                insertions[updateName] = [port, line]
            elif updateType == '-' and updateName in insertions:
                if len(insertions[updateName]) == 2 and insertions[updateName][0] == port:
                    del insertions[updateName]
    with open("airtel_airtel-cleaned.csv",'w') as f:
        for update in insertions:
            f.write(insertions[update][1] + "\n")


def addFW(dataset, nodesToIgnore, portMapping, graph, nodeIntMapping, db, topology):
    inputs = [] # list of inputs of the form [(header, source, next_hop, condition),...]
    for node in nodesToIgnore:
        prefixes = nodesToIgnore[node]
        if type(prefixes) == str and prefixes == "all":
            condition = getOutputCondition(node=node, cvar=node+"_next", graph=graph, nodeIntMapping=nodeIntMapping)
            header_mapped = db.cVarMappingReverse[node+"_header"]
            next_hop_mapped = db.cVarMappingReverse[node+"_next"]
            input = "({},{},{},{})".format(header_mapped, nodeIntMapping[node], next_hop_mapped, condition)
            inputs.append(input)
        else:
            for pref in prefixes:
                if "'" in pref:
                    mappingIP = pref[1:-1].replace(".","")
                else:
                    mappingIP = pref.replace(".","")
                    pref = "'"+pref+"'"
                condition = getOutputCondition(node=node, cvar=node+"_"+mappingIP, graph=graph, nodeIntMapping=nodeIntMapping)
                next_hop_mapped = db.cVarMappingReverse[node+"_"+mappingIP]
                input = "({},{},{},{})".format(pref, nodeIntMapping[node], next_hop_mapped, condition)
                inputs.append(input)

    if "/" not in dataset: # files should be in folders
        dataset = "{}/{}".format(topology, dataset)
    with open(dataset) as f:
        lines = f.readlines()
        for line in lines:
            if topology == "I2":
                splitLine = line.split(" ")
                if len(splitLine) == 4: # I2 normal dataset
                    node = dataset.split("/")[1][:-9]
                    ip = splitLine[1].strip()
                    prefix = splitLine[2].strip()
                    port = splitLine[3].strip().split(".")[0]
                else:
                    isAdd = splitLine[0].strip()
                    delay = splitLine[1].strip()
                    epoch = splitLine[2].strip()
                    node = splitLine[3].strip()
                    ip = splitLine[4].strip()
                    prefix = splitLine[5].strip()
                    port = splitLine[6].strip()
                    isEnd = splitLine[7].strip()
            elif topology == "airtel":
                splitLine = line.split(",")
                node = splitLine[1].strip()
                ipPart = splitLine[0].strip().split("/")
                updateType = ipPart[0][0]
                ip = ipPart[0][1:] # ignoring the '+' or '-' sign
                prefix = ipPart[1]
                port = splitLine[2].strip()
                if updateType != "+":
                    # print("Unknown update type encountered for line: {}".format(line))
                    continue

            intIP = getIP(ip, prefix)
            if node in nodesToIgnore:
                continue
            
            condition = "'{}'"
            if node+"_"+port not in portMapping:
                continue
            next_hop_node = portMapping[node+"_"+port]
            input = "({},{},{},{})".format(intIP, nodeIntMapping[node], nodeIntMapping[next_hop_node], condition)
            inputs.append(input)
    print("Storing table of size {} to F".format(len(inputs)))
    start = time()
    storeTable("F", inputs)
    end = time()
    print("Storing took {} seconds".format(end-start))

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

def runDatalog(db, nodeIntMappingReverse, nodeIntMapping, sourceNode = "atla", header = '1', simplification_on = True):
    source = nodeIntMapping[sourceNode]

    p1 = "R({header}, {source}, n, [{source}, n], {source}, n) :- F({header}, {source}, n)[n != {source}]".format(source=source, header=header)

    p2 = "V({header}, p) :- R({header}, {source}, n2, p, second_laster,last_node), F({header}, n2, n)[And(n == p, n != second_laster)]\nR({header}, {source}, n, p || [n], last_node, n) :- R({header}, {source}, n2, p, second_laster, last_node), F({header}, n2, n)[n != second_laster]".format(source=source, header=header)
    # p1 = "V({header}, p) :- R({header}, {source}, n2, p, second_laster,last_node), F({header}, n2, n)[And(n == p, n != second_laster)]".format(source=source, header=header)
    program1 = DT_Program(p1, database=db, optimizations={"simplification_on":simplification_on})
    program2 = DT_Program(p2, database=db, optimizations={"simplification_on":simplification_on})
    start = time()
    program1.executeonce(conn)
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
    # program2.executeonce(conn)
    # printTable('R', db, nodeIntMappingReverse)
    # input()
    program2.execute(conn, violationTables=[db.getTable("V")])
    end = time()
    conn.commit()
    print("Total Time =", end-start)
    return (end-start)

if __name__ == '__main__':
    runs = 1
    # cleanAirtelDataset()
    # exit()

    if len(sys.argv) < 7:
        print("Program requires at least 6 parameters ([airtel/I2] [source_node] [header/X] [indexing_on] [simplification_on] and at least 1 dataset). Usage: python3 flash_experiments.py I2 atla 1 True False dataset1,dataset2,dataset3,... hous all kans 1,2833844992,5")
        exit()

    topology = sys.argv[1]
    sourceNodeStr = sys.argv[2]
    headerStr = sys.argv[3] # can be an ip as an int or a variable X (which represents all headers)
    indexing_on = (sys.argv[4].lower() == "true")
    simplification_on = (sys.argv[5].lower() == "true")
    datasetFiles = sys.argv[6].split(',')
    nodesToIgnore = {} # key is node to ignore, value is either all or a list of prefixes to ignore

    i = 7
    nodesToIgnoreArr = []
    randomNodeIgnore = False
    while i < len(sys.argv) - 1:
        node = sys.argv[i]
        string = node+"-"
        prefixes = sys.argv[i+1].split(",")
        if prefixes[0] == "all":
            nodesToIgnore[node] = "all"
            string += "all"
        else:
            string += "["
            prefixList = []
            for prefix in prefixes:
                if parsing_utils.isIP(prefix):
                    prefixList.append(prefix)
                else:
                    prefixList.append(int(prefix))
                string += prefix+","
            string = string[:-1] + "]"
            nodesToIgnore[node] = prefixList
        i += 2
        nodesToIgnoreArr.append(string)
    
    if len(sys.argv) == 8 and sys.argv[7] == "random":
        randomNodeIgnore = True

    portMapping, graph, nodes = loadTopology(topology) # load topology to get port to node mapping, possible next hops for all nodes, nodes list

    time_taken_arr = []
    for run in range(runs):
        source = sourceNodeStr
        if sourceNodeStr.lower() == 'random':
            source = random.choice(nodes)
            if randomNodeIgnore:
                nodesToIgnore = {}
                nodesToIgnore[source] = "all"

        nodeIntMapping, nodeIntMappingReverse = getMapping(nodes) # each node is represented by an integer

        db = initializeDatabases(nodes=nodes, nodesToIgnore=nodesToIgnore, nodeIntMapping=nodeIntMapping, indexing_on=indexing_on) # cvarmapping is int to string

        for dataset in datasetFiles:
            addFW(dataset, nodesToIgnore, portMapping, graph, nodeIntMapping, db, topology)
        input()
        header = headerStr
        if headerStr.lower() == 'random':
            header = db.getTable('F').getRandomTuple(conn = conn, colmName = 'header')
        if parsing_utils.isIP(header):
            header = header.split("/")[0]+"/"+"32"
        timeTaken = runDatalog(db=db, nodeIntMappingReverse=nodeIntMappingReverse, nodeIntMapping=nodeIntMapping, sourceNode=source, header=header, simplification_on=simplification_on)
        time_taken_arr.append(timeTaken)

        logFileName = "flash_experiment.log"
        if not os.path.isfile(logFileName):
            with open(logFileName, 'w') as f:
                f.write("TOPOLOGY\tSOURCE\tHEADER\tINDEXING_ON\tSIMPLIFICATION_ON\tDATASETS\tNODES_TO_IGNORE\tTIME_TAKEN\n")

        with open(logFileName, 'a') as f:
            if len(nodesToIgnoreArr) == 0:
                f.write("{}\t{}\t{}\t{}\t{}\t{}\tNONE\t{}\n".format(topology,source,header,str(indexing_on),str(simplification_on),datasetFiles,str(timeTaken)))
            else:
                f.write("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n".format(topology,source,header,str(indexing_on),str(simplification_on),datasetFiles, nodesToIgnoreArr, str(timeTaken)))
        
        # printTable("V", db, nodeIntMappingReverse)
        # printTable("V", db, nodeIntMappingReverse)
        db.getTable("R").deleteAllTuples(conn)
        db.getTable("V").deleteAllTuples(conn)
        db.getTable("F").deleteAllTuples(conn)
        conn.commit()

    print()
    print("Average time taken: {}".format(sum(time_taken_arr)/len(time_taken_arr)))
    print(time_taken_arr)

# Loop
# python3 flash_experiments.py airtel s14-5 1 True False airtel-small.csv,airtel-cleaned.csv s15-5 all s9-7 all s15-1 all
