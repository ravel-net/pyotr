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

# Adds link between two nodes
def addLink(graph, node1, node2):
    if node1 not in graph:
        graph[node1] = []
    if node2 not in graph:
        graph[node2] = []
    graph[node1].append(node2)
    graph[node2].append(node1)

def createL2Topology(npods = 112, rswPerPod = 48):
    nodes = {} # make sure the random source is always rsw
    portMapping = {}
    graph = {}
    sswPerSpine = rswPerPod # assumtion from the flash codebase
    fswPerPod = 4 # assumtion from the flash codebase
    numSpines = fswPerPod # assumtion from the flash codebase

    # Add devices
    nodes["ssw"] = []
    nodes["rsw"] = []
    nodes["fsw"] = []
    for iPod in range(npods):
        # 112*48 rsw ipod devices
        for j in range(rswPerPod):
            device = "rsw-" + str(iPod) + "-" + str(j)
            nodes["rsw"].append(device)

        # 112*4 fsw ipod devices
        for j in range(sswPerSpine):
            device = "fsw-" + str(iPod) + "-" + str(j)
            nodes["fsw"].append(device)

    # 4 spines with 48 ssw spine devices each. 4 * 48
    for iSpine in range(numSpines):
        for j in range(sswPerSpine):
            device = "ssw-" + str(iSpine) + "-" + str(j)
            nodes["ssw"].append(device)

    # Add links
    for iPod in range(npods):
        for iFsw in range(fswPerPod):
            fsw = "fsw-" + str(iPod) + "-" + str(iFsw)

            # # down links
            # # each of 4 FSW ipod devices in an ipod connected to each of 48 rsw devices
            for iRsw in range(rswPerPod):
                rsw = "rsw-" + str(iPod) + "-" + str(iRsw)
                addLink(graph, rsw, fsw)
                portMapping[rsw+"_"+fsw] = fsw
                portMapping[fsw+"_"+rsw] = rsw

            # # up links
            # # each of 4 FSW ipod devices in an ipod connected to each of 48 spine pods. In the spine, each ssw device is connected to one spine device
            for iSsw in range(sswPerSpine):
                ssw = "ssw-" + str(iFsw) + "-" + str(iSsw)
                addLink(graph, ssw, fsw)
                portMapping[ssw+"_"+fsw] = fsw
                portMapping[fsw+"_"+ssw] = ssw
    return portMapping, graph, nodes


def loadTopology(topology):
    nodes = []
    portMapping = {}
    graph = {}
    topologyFile = "{}/{}_Topo".format(topology, topology)
    if topology == "airtel" and not os.path.isfile(topologyFile):
        createAirtelTopo(topologyFile)
    if "L2" in topology:
        npods = int(topology.split("_")[1])
        rswPerPod = int(topology.split("_")[2])
        return createL2Topology(npods, rswPerPod)
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

def initializeDatabases(nodesToIgnore, nodeIntMapping, indexing_on, topology):
    cvars = {}
    F_name = "F_"+topology
    for node, prefixes in nodesToIgnore.items():
        if type(prefixes) == str and "all" in prefixes:
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

    V = DT_Table(name="V", columns={"header":"inet_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"})

    F = DT_Table(name=F_name, columns={"header":"inet_faure", "node":"integer", "next_hop":"integer_faure","condition":"text[]"}, cvars=cvars, domain={"next_hop":allowedNodes,"node":allowedNodes})

    # mapping_index = -200
    # cvarMapping = {}
    # for cvar in cvars:
    #     cvarMapping[str(mapping_index)] = cvar
    #     mapping_index -= 1

    # database = DT_Database(tables=[F,R,V], cVarMapping=cvarMapping)
    database = DT_Database(tables=[F,R,V])
    R.delete(conn)
    R.initiateTable(conn)
    V.delete(conn)
    V.initiateTable(conn)
    # database.delete(conn)
    F.delete(conn)
    F.initiateTable(conn)

    # if not indexing_on:
    #     F.deleteAllIndexes(conn)
    #     R.deleteAllIndexes(conn)
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

# Given a line from a forwarding table, parses
def getForwardingInformationLine(topology, dataset, line):
    if topology == "I2":
        splitLine = line.split(" ")
        if len(splitLine) == 4: # I2 normal dataset
            node = dataset.split("/")[1][:-9]
            ip = splitLine[1].strip()
            prefix = splitLine[2].strip()
            port = splitLine[3].strip().split(".")[0]
            updateType = "+"
        else:
            updateType = splitLine[0].strip()
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
    return node, ip, prefix, port, updateType

def getForwardingInformation(topology, datasets, portMapping, nodeIntMapping):
    fwdTable = []
    if "L2" in topology:
        npods = int(topology.split("_")[1])
        rswPerPod = int(topology.split("_")[2])
        return getForwardingInformationL2(npods, rswPerPod)
    else:
        for dataset in datasets:
            if "/" not in dataset: # files should be in folders
                dataset = "{}/{}".format(topology, dataset)
            with open(dataset) as f:
                lines = f.readlines()
                for line in lines:
                    node, ip, prefix, port, updateType = getForwardingInformationLine(topology, dataset, line)
                    if updateType != "+":
                        # print("Unknown update type encountered for line: {}".format(line))
                        continue
                    intIP = getIP(ip, prefix)
                    if node+"_"+port not in portMapping:
                        continue
                    next_hop_node = portMapping[node+"_"+port]
                    fwdTable.append((intIP, node, next_hop_node))
        return fwdTable

def addUnknownInfo(nodesToIgnore, graph, nodeIntMapping, db, topology):
    inputs = []
    F_table = db.getTable("F_"+topology)
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
    storeTable(F_table.name, inputs)

def addFW(nodeIntMapping, db, topology, sourceHeaderPairs, path):
    inputs = [] # list of inputs of the form [(header, source, next_hop, condition),...]
    F_table = db.getTable("F_"+topology)
    condition = "'{}'"
    for source, header in sourceHeaderPairs:
        if "/" in header:
            header = header.split("/")[0]
        # for node in nodesInvolved:
        i = 0
        while i < len(path)-1:
            node = path[i]
            next_hop = path[i+1]
            if next_hop == None:
                break
            input = "({},{},{},{})".format("'"+header+"/32'",nodeIntMapping[node],nodeIntMapping[next_hop],condition)
            inputs.append(input)
            i += 1
    print("Storing table of size {} to F".format(len(inputs)))
    start = time()
    storeTable(F_table.name, inputs)
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
    conn.commit()
    cursor = conn.cursor()
    cursor.execute("SELECT * from {}".format(tableName))
    table = cursor.fetchall()
    conn.commit()
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
    return (end-start)

# Given a string like "house all kans 1,1231231,5", it returns the dictionary nodes to ignore
def getNodesToIgnore(nodesIgnoreList):
    nodesToIgnore = {}
    nodesToIgnoreArr = []
    i = 0
    while i < len(nodesIgnoreList) - 1:
        node = nodesIgnoreList[i]
        if node == "random":
            numRandoms = int(nodesIgnoreList[i+1])
            nodesToIgnore[node] = numRandoms
            return nodesToIgnore, []
        string = node+"-"
        prefixes = nodesIgnoreList[i+1].split(",")
        if "all" in prefixes[0]:
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
    return nodesToIgnore, nodesToIgnoreArr   

# Returns forwarding graph
def getForwardingInformationL2(npods = 112, rswPerPod = 48, mode = "shortest"):
    if mode != "shortest":
        print("Mode {} is not supported".format(mode))
        exit()
    sswPerSpine = rswPerPod # assumtion from the flash codebase
    fswPerPod = 4 # assumtion from the flash codebase
    numSpines = fswPerPod # assumtion from the flash codebase
    data = []
    ## create rules
    # first 8 bits is pod id, next 8 bit is index of rsw in pod
    for iPod in range(npods):
        for iRsw in range(rswPerPod):
            rsw = "rsw-" + str(iPod) + "-" + str(iRsw)
            for jPod in range(npods):
                for jRsw in range(rswPerPod):
                    dstrsw = "rsw-" + str(jPod) + "-" + str(jRsw)
                    dstip = ipaddress.ip_address((jPod << 24) + ((jRsw + 1) << 16))
                    if (iPod == jPod and iRsw == jRsw): 
                        continue
                    else:
                        dstfsw = "fsw-" + str(iPod) + "-" + str((48 * jPod + jRsw) % 4)
                    rule = (str(dstip), rsw, dstfsw)
                    data.append(rule)
        for iSpine in range(numSpines):
            fsw = "fsw-" + str(iPod) + "-" + str(iSpine)
            for jPod in range(npods):
                for jRsw in range(rswPerPod):
                    dstrsw = "rsw-" + str(jPod) + "-" + str(jRsw)
                    dstip = ipaddress.ip_address((jPod << 24) + ((jRsw + 1) << 16))
                    if (jPod == iPod): # intra pod
                        rule = (str(dstip), fsw, dstrsw)
                    else:
                        dstssw = "ssw-" + str(iSpine) + "-" + str((48 * jPod + jRsw) % 48)
                        rule = (str(dstip), fsw, dstssw)
                    data.append(rule)

    for iSpine in range(numSpines):
        for iSsw in range(sswPerSpine):
            ssw = "ssw-" + str(iSpine) + "-" + str(iSsw)
            for k in range(npods):
                for l in range(rswPerPod):
                    dstip = ipaddress.ip_address((k << 24) + ((l + 1) << 16))
                    dstfsw = "fsw-" + str(k) + "-" + str(iSpine)
                    rule = (str(dstip), ssw, dstfsw)
                    data.append(rule)

    return data

def loadFiles(topology, datasetFiles, portMapping):
    data = []
    if "L2" in topology:
        npods = int(topology.split("_")[1])
        rswPerPod = int(topology.split("_")[2])
        return getForwardingInformationL2(npods, rswPerPod)
    else:
        for dataset in datasetFiles:
            if "/" not in dataset: # files should be in folders
                dataset = "{}/{}".format(topology, dataset)
            with open(dataset) as f:
                lines = f.readlines()
                for line in lines:
                    node, ip, prefix, port, updateType = getForwardingInformationLine(topology, dataset, line)
                    if updateType != "+":
                        # print("Unknown update type encountered for line: {}".format(line))
                        continue
                    intIP = getIP(ip, prefix)
                    if node+"_"+port not in portMapping:
                        continue
                    data.append((intIP, node, portMapping[node+"_"+port]))
        return {}, data

def getNextHop(node, header, data):
    if "/" in header:
        header = header.split("/")[0]
    header = header.replace("'","")
    for entry in data:
        header_entry, node_entry, next_hop_entry = entry
        header_entry = header_entry.replace("'","")
        if node == node_entry and ipaddress.ip_address(header) in ipaddress.ip_network(header_entry):
            return next_hop_entry
    return None

# Calculates path from source to header
def getPath(source, header, data):
    path = [source]
    next_hop = getNextHop(source, header, data)
    while next_hop != None:
        path.append(next_hop)
        next_hop = getNextHop(next_hop, header, data)
    return path

def getRandomHeader(data):
    random_item = random.choice(data)
    return random_item[0]

def verify(arguments):
    if len(arguments) < 5:
        print("Program requires 6 parameters ([verify] [Topology:airtel/I2] [input_file] [indexing_on] [simplification_on] [datasetFiles]). Usage: python3 flash_experiments.py I2 loop.txt True False dataset1,dataset2,dataset3")
        exit()

    topology = arguments[0]
    input_file = arguments[1]
    indexing_on = (arguments[2].lower() == "true")
    simplification_on = (arguments[3].lower() == "true")
    datasetFiles = arguments[4].split(',')

    try:
        lines = []
        with open(input_file) as f:
            lines = f.readlines()
    except:
        print("Could not open input file {}. Exiting".format(input_file))
        exit()
    finally:
        time_taken_arr = []
        portMapping, graph, nodes = loadTopology(topology) # load topology to get port to node mapping, possible next hops for all nodes, nodes list  
        if "L2" in topology:
            allNodes = []
            for nodeType in nodes:
                for node in nodes[nodeType]:
                    allNodes.append(node)
            nodeIntMapping, nodeIntMappingReverse = getMapping(allNodes) # each node is represented by an integer
            # fwdTable = getForwardingInformation(topology=topology, datasets=[], portMapping=portMapping, nodeIntMapping=nodeIntMapping)
        else:
            nodeIntMapping, nodeIntMappingReverse = getMapping(nodes) # each node is represented by an integer
            # fwdTable = getForwardingInformation(topology=topology, datasets=datasetFiles, portMapping=portMapping, nodeIntMapping=nodeIntMapping)

        for line in lines:
            lineSplit = line.split(" ")
            source = lineSplit[0].strip()
            header = lineSplit[1].strip() # can be an ip as an int or a variable X (which represents all headers)
            path = lineSplit[2].strip().split(",")
            nodesToIgnore = {} # key is node to ignore, value is either all or a list of prefixes to ignore

            nodesToIgnore, nodesToIgnoreArr = getNodesToIgnore(lineSplit[3:])
            
            db = initializeDatabases(nodesToIgnore=nodesToIgnore, nodeIntMapping=nodeIntMapping, indexing_on=indexing_on, topology=topology) # cvarmapping is int to string

            sourceHeaderPairs = [(source, header)]
            addFW(nodeIntMapping=nodeIntMapping, db=db, topology=topology, sourceHeaderPairs=sourceHeaderPairs, path=path)
            addUnknownInfo(nodesToIgnore, graph, nodeIntMapping, db, topology)
            F_table = db.getTable("F_"+topology)
            if indexing_on:
                F_table.enableIndexing(conn, "header", using="gist")
                F_table.enableIndexing(conn, "node")
                F_table.enableIndexing(conn, "next_hop")
                # R.enableIndexing(conn, "header", using="gist")
                # R.enableIndexing(conn, "dest")
                # R.enableIndexing(conn, "source")
                # R.enableIndexing(conn, "second_laster")
                # R.enableIndexing(conn, "last_node")
                # R.enableIndexing(conn, "path", using="GIN")
            timeTaken = runDatalog(db=db, nodeIntMappingReverse=nodeIntMappingReverse, nodeIntMapping=nodeIntMapping, sourceNode=source, header=header, simplification_on=simplification_on, F_name="F_"+topology)

            time_taken_arr.append(timeTaken)

            if "/" in input_file:
                output_file = input_file.split("/")[1].replace(".txt","")
            else:
                output_file = input_file.replace(".txt","")
            logFileName = "output/{}-{}-{}.log".format(output_file, str(indexing_on), str(simplification_on))
            if not os.path.isfile(logFileName):
                with open(logFileName, 'w') as f:
                    f.write("TOPOLOGY\tSOURCE\tHEADER\tINDEXING_ON\tSIMPLIFICATION_ON\tDATASETS\tNODES_TO_IGNORE\tTIME_TAKEN\n")

            with open(logFileName, 'a') as f:
                if len(nodesToIgnoreArr) == 0:
                    f.write("{}\t{}\t{}\t{}\t{}\t{}\tNONE\t{}\n".format(topology,source,header,str(indexing_on),str(simplification_on),datasetFiles,str(timeTaken)))
                else:
                    f.write("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n".format(topology,source,header,str(indexing_on),str(simplification_on),datasetFiles, nodesToIgnoreArr, str(timeTaken)))

            db.getTable("R").deleteAllTuples(conn)
            db.getTable("V").deleteAllTuples(conn)
            F_table.deleteAllTuples(conn)
            # F_table.deleteAllCVarRows(conn)
            conn.commit()

        print()
        print("Average time taken: {}".format(sum(time_taken_arr)/len(time_taken_arr)))
        print(time_taken_arr)   

def generate(arguments):
    if len(arguments) < 6:
        print("Program requires at least 7 parameters with an optional parameter for nodes to consider unknown ([generate] [topology:I2/airtel/L2-pods-fswPerPod] [output_filename] [number of runs] [source] [header] [datasetFiles]). Usage: python3 flash_experiments.py generate random random dataset1,dataset2,dataset3 random")
        exit()

    topology = arguments[0]
    output_filename = arguments[1]
    numRuns = int(arguments[2])
    sourceNodeStr = arguments[3]
    headerStr = arguments[4]
    datasetFiles = arguments[5].split(',')
    nodesToIgnoreOld, _ = getNodesToIgnore(arguments[6:])
    source = sourceNodeStr
    header = headerStr

    portMapping, graph, nodes = loadTopology(topology) # load topology to get port to node mapping, possible next hops for all nodes, nodes list
    data = loadFiles(topology, datasetFiles, portMapping)
    nodesToIgnore = nodesToIgnoreOld
    run = 0
    with open(output_filename,"w") as f:
        while run < numRuns:
            print(run)
            if sourceNodeStr.lower() == 'random':
                if "L2" in topology:
                    source = random.choice(nodes["rsw"]) # we only consider rsw to be the source in L2 Topology
                else:
                    source = random.choice(nodes)
            if headerStr.lower() == 'random':
                header = getRandomHeader(data)
            header = header.replace("'","")
            if parsing_utils.isIP(header):
                header = header.split("/")[0]+"/"+"32"
            path = getPath(source, header, data)
            if "random" in nodesToIgnoreOld:
                numRandomNodes = nodesToIgnoreOld["random"]
                if len(path) <= numRandomNodes:
                    continue
                nodesToIgnore = random.sample(path[:-1], numRandomNodes)
            pathStr = ",".join(path)
            f.write("{} {} {}".format(source, header, pathStr))
            for node in nodesToIgnore:
                f.write(" {} all".format(node))
            if run != numRuns-1:
                f.write("\n")
            run += 1

if __name__ == '__main__':
    # cleanAirtelDataset()
    # exit()

    if len(sys.argv) < 3 or (sys.argv[1] != "verify" and sys.argv[1] != "generate"):
        print("Program requires at least 1 parameter with the first parameter either 'verify' or 'generate'. Exiting")
        exit()

    if sys.argv[1] == "verify":
        verify(sys.argv[2:])
    else:
        generate(sys.argv[2:])
# Loop
# python3 flash_experiments.py airtel s14-5 1 True False airtel-small.csv,airtel-cleaned.csv s15-5 all s9-7 all s15-1 all



# Generate
#  python3 flash_experiments.py generate L2_112_48 L2_112_48-10-random-1 10 random random _ random 1

# Verify
# python3 flash_experiments.py verify L2_112_48 inputs/L2_112_48-10-random-0 True True _


# Correctness test
# python3 flash_experiments.py verify I2 inputs/I2-loop.txt True True trace-loop-hous.txt