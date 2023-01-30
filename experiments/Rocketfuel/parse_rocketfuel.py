import sys
from os.path import dirname, abspath
import os
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)
from igraph import *
from Core.Homomorphism.Datalog.program import DT_Program
import time
from copy import deepcopy
import itertools
from statistics import mean, stdev
import random 

class RocketfuelPoPTopo:
    """
    A class used to represent a rocketfuel AS PoP-level topology.

    Attributes
    ----------
    numVertices : int
        the number of vertices of a given AS PoP topology
    ASes : string[]
        list of ASes (including itself) in the PoP topology
    links : (string, string)
        list of all links in the topology


    Methods
    -------
    calculatePaths(src, dest)
        returns the paths between a source and destinations. Currently, paths are simple paths
    """

    def __init__(self, AS = "1"):
        self.AS = AS
        self.accessNodes = []
        self.access_links = []
        self.accessLocations = {}
        self.accessGraph = Graph()
        self.nodeMappingsAccess = {}

        self.POPGraph = Graph()
        self.POP_links = []
        self.nodesSelfPOP = []
        self.nodesAllPOP = []
        self.egressNodes = []
        self.ingressNodes = []
        self.nodeMappingsPOP = {}
        self.reverseNodeMappingsPOP = {}
        self.directedPOPGraph = Graph()
        self.directed_links = []
        self.hasNodes = True
        self.add_POP_links()
        if self.hasNodes:
            self.populatePOPGraph()
        

    def add_access_links(self):
        pathISPMap = os.path.join(os.getcwd(), "ISP-Maps")
        pathASLinks = os.path.join(pathISPMap, "{}.r1.cch".format(self.AS))
        with open(pathASLinks) as f:
            lines = f.readlines()
            for line in lines:
                currLine = line.split()
                if (currLine[0].isdigit()):
                    src = currLine[0]
                    location = currLine[1]
                    if currLine[3] != "bb" and ("," in location):
                        location = location.split(",")[0]
                        location = location.split("-")[0][1:]
                        location = location.replace("+"," ")
                        if location not in self.accessLocations:
                            self.accessLocations[location] = []
                        self.accessLocations[location].append(src)
                    if (src not in self.accessNodes):
                        self.accessNodes.append(src)
                    for cols in currLine:
                        if cols[0] == "<":
                            dst = cols[1:-1]
                            if (dst not in self.accessNodes):
                                self.accessNodes.append(dst)
                            if ((src,dst) not in self.access_links and (dst,src) not in self.access_links):
                                self.access_links.append((src,dst))

    def drawPoPGraph(self):
        layout = self.POPGraph.layout("kk")
        pl = Plot()
        pl.add(self.POPGraph, layout=layout)
        pl._windows_hacks=True
        pl.show()

    def drawAccessGraph(self):
        layout = self.accessGraph.layout("kk")
        pl = Plot()
        pl.add(self.accessGraph, layout=layout)
        pl._windows_hacks=True
        pl.show()

    # def addIngress(self, ingressAS):
    def populateNodeMapping(self, isPoP):
        currRange = len(self.nodesAllPOP)
        if not isPoP:
            currRange = len(self.accessNodes)
        for i in range(currRange):
            l1 = "a"
            l2 = "a"
            l3 = "a"
            leftover = i
            if (leftover >= 26*26):
                currLetter = (int) (leftover/(26*26))
                l1 = chr(ord(l1)+currLetter)
                leftover = leftover % (26*26)
            if (leftover >= 26):
                currLetter = (int) (leftover/(26))
                l2 = chr(ord(l2)+currLetter)
                leftover = leftover % (26)
            if (leftover < 26):
                currLetter = leftover
                l3 = chr(ord(l3)+currLetter)
            if isPoP:
                # self.nodeMappingsPOP[i] = l1+l2+l3
                self.nodeMappingsPOP[i] = l3#+l2+l3
            else:
                self.nodeMappingsAccess[i] = l1+l2+l3

        for key in self.nodeMappingsPOP:
            value = self.nodeMappingsPOP[key]
            self.reverseNodeMappingsPOP[value] = key


    def populateAccessGraph(self):
        numNodes = len(self.accessNodes)
        self.accessGraph.add_vertices(numNodes)
        for link in self.access_links:
            src = self.accessNodes.index(link[0])
            dst = self.accessNodes.index(link[1])
            self.accessGraph.add_edges([(src,dst)])
        self.populateNodeMapping()

    def populatePOPGraph(self):
        self.POPGraph = Graph()
        self.POPGraph.add_vertices(len(self.nodesAllPOP))
        for link in self.POP_links:
            src = self.nodesAllPOP.index(link[0])
            dst = self.nodesAllPOP.index(link[1])
            self.POPGraph.add_edges([(src,dst)])

    # adds the AS's pop links
    def add_POP_links(self):
        path = os.path.join(os.getcwd(), "AS-links")
        path = os.path.join(path, "{}:{}".format(self.AS, self.AS))
        path = os.path.join(path, "edges")
        if not os.path.isfile(path):
            self.hasNodes = False
            return
        with open(path) as file:
            edges = file.readlines()
            for edge in edges:
                edgeSplit = edge.strip("\n").split(" -> ")
                srcAS = edgeSplit[0].strip()
                secondSplit = edgeSplit[1].split(",")

                if (len(secondSplit) > 1):
                    dst = secondSplit[0]+", "+secondSplit[1][:3].strip()
                else: # corner case of hongkong
                    dst = secondSplit[0].split()[0]+" "+secondSplit[0].split()[1]

                # weight = int(secondSplit[1][4:])
                if srcAS not in self.nodesSelfPOP:
                    self.nodesSelfPOP.append(srcAS)
                if srcAS not in self.nodesAllPOP:
                    self.nodesAllPOP.append(srcAS)                
                if dst not in self.nodesSelfPOP:
                    self.nodesSelfPOP.append(dst)
                if dst not in self.nodesAllPOP:
                    self.nodesAllPOP.append(dst)
                newLink = (srcAS, dst)
                newLinkReverse = (dst, srcAS)
                if newLink not in self.POP_links and newLinkReverse not in self.POP_links:
                    self.POP_links.append(newLink)

    def find_all_paths(self,graph, start, end, mode = 'OUT', maxlen = None):
        def find_all_paths_aux(adjlist, start, end, path, maxlen = None):
            path = path + [start]
            if start == end:
                return [path]
            paths = []
            if maxlen is None or len(path) <= maxlen:
                for node in adjlist[start] - set(path):
                    paths.extend(find_all_paths_aux(adjlist, node, end, path, maxlen))
            return paths
        adjlist = [set(graph.neighbors(node, mode = mode)) \
            for node in range(graph.vcount())]
        all_paths = []
        start = start if type(start) is list else [start]
        end = end if type(end) is list else [end]
        for s in start:
            for e in end:
                all_paths.extend(find_all_paths_aux(adjlist, s, e, [], maxlen))
        return all_paths

    def getDatalogRule(self, allPaths, destination, ingressNode, ingressAS, egressAS):
        rules = []
        head = "R({},{},{}) :- ".format(ingressAS, destination, egressAS)
        for path in allPaths:
            links = []
            for i,vertex in enumerate(path[:-1]):
                secondVertex = path[i+1]
                if vertex == ingressNode:
                    links.append("l({},{})".format(ingressAS, self.nodeMappingsPOP[secondVertex]))
                else:
                    links.append("l({},{})".format(self.nodeMappingsPOP[vertex], self.nodeMappingsPOP[secondVertex]))
            newRule = head + "l({},{}), A({},{})".format(self.nodeMappingsPOP[path[-1]], egressAS, destination,egressAS)
            if len(links) > 0:
                newRule = head + ",".join(links) + ", l({},{}), A({}, {})".format(self.nodeMappingsPOP[path[-1]],egressAS, destination,egressAS)
            rules.append(newRule)
        return rules

    def getShortestPaths(self):
        allPaths = []
        ingressNodePathSizes = {}
        for ingressNode in self.ingressNodes:
            src = self.nodesAllPOP.index(ingressNode)
            for eggressNode in self.egressNodes:
                if ingressNode == eggressNode:
                    allPaths += [ingressNode]
                    if src not in ingressNodePathSizes:
                        ingressNodePathSizes[src] = []
                    ingressNodePathSizes[src].append(1)
                    continue
                dst = self.nodesAllPOP.index(eggressNode)
                # directed = self.accessGraph.as_directed()
                paths = self.POPGraph.get_all_shortest_paths(src, dst)
                if len(paths) == 0:
                    continue
                if src not in ingressNodePathSizes:
                    ingressNodePathSizes[src] = []
                ingressNodePathSizes[src].append(len(paths[0]))
                allPaths += paths
        newAllPaths = []
        for path in allPaths:
            for nodeNum, node in enumerate(path[:-1]):
                link = (node, path[nodeNum+1])
                if link not in self.directed_links:
                    self.directed_links.append(link)
        self.directedPOPGraph = Graph(directed=True)
        self.directedPOPGraph.add_vertices(len(self.nodesAllPOP))
        for link in self.directed_links:
            self.directedPOPGraph.add_edges([link])
        for ingressNode in self.ingressNodes:
            for eggressNode in self.egressNodes:
                src = self.nodesAllPOP.index(ingressNode)
                dst = self.nodesAllPOP.index(eggressNode)
                for p in self.find_all_paths(self.directedPOPGraph,src,dst):
                    newAllPaths.append(p)
        finalPaths = []
        for path in newAllPaths:
            src = path[0]
            if len(path) in ingressNodePathSizes[src]:
                finalPaths.append(path)
        return finalPaths

    def convertToDatalog(self, ingressAS, egressAS):
        self.populateNodeMapping(True)
        self.reverseNodeMappingsPOP[egressAS] = egressAS
        allPaths = self.getShortestPaths()
        if len(allPaths) == 0: # can't do any computation if AS has no paths
            return []
        allLinks = []
        print(allPaths)
        for path in allPaths:
            path.insert(0, -1)
        allRules = self.getDatalogRule(allPaths=allPaths, destination="D", ingressNode=-1, ingressAS=ingressAS, egressAS=egressAS)
        return allRules

    def addGressNodes(self, targetAS, isIngress):
        path = os.path.join(os.getcwd(), "AS-links")
        if isIngress:
            path = os.path.join(path, "{}:{}".format(self.AS, targetAS))
        else:
            path = os.path.join(path, "{}:{}".format(targetAS, self.AS))
        path = os.path.join(path, "edges")
        with open(path) as file:
            edges = file.readlines()
            for edge in edges:
                edgeSplit = edge.strip("\n").split(" -> ")
                selfPOP = edgeSplit[0].strip()
                secondSplit = edgeSplit[1].split(",")
                dstPOP = ""
                if (len(secondSplit) > 1):
                    dstPOP = secondSplit[0]+", "+secondSplit[1][:3].strip()
                else: # corner case of hongkong
                    dstPOP = secondSplit[0].split()[0]+" "+secondSplit[0].split()[1]

                if not isIngress:
                    tmp = selfPOP
                    selfPOP = dstPOP
                    dstPOP = tmp

                # weight = int(secondSplit[1][4:])
                if selfPOP not in self.nodesSelfPOP or selfPOP not in self.nodesAllPOP:
                    print("Unknown node {} found in AS {}".format(selfPOP, self.AS))
                    continue

                if isIngress and selfPOP not in self.egressNodes:
                    self.ingressNodes.append(selfPOP)
                elif not isIngress and selfPOP not in self.ingressNodes:
                    self.egressNodes.append(selfPOP)

                if dstPOP not in self.nodesAllPOP:
                    self.nodesAllPOP.append(dstPOP)
                newLink = (selfPOP, dstPOP)
                newLinkReverse = (dstPOP, selfPOP)
                if newLink not in self.POP_links and newLinkReverse not in self.POP_links:
                    self.POP_links.append(newLink)
        self.populatePOPGraph()

    def convertToProgram(self, rulesArr):
        return DT_Program("\n".join(rulesArr), recursive_rules=False)

    def minimize(self, program):
        minimizedProgram = deepcopy(program)
        numRulesBefore = len(minimizedProgram._rules)
        start = time.time()
        minimizedProgram.minimize(False, True)
        end = time.time()
        numRulesAfter = len(minimizedProgram._rules)
        return minimizedProgram

    def getLinksNodes(self, rulesArray):
        links = []
        nodes = []
        for rule in rulesArray:
            for atom in rule._body:
                if atom.db["name"] == "l":
                    node1 = atom.parameters[0]
                    node2 = atom.parameters[1]
                    # if node1.isdigit() or node2.isdigit():
                    #     continue
                    if not node1.isdigit() and self.reverseNodeMappingsPOP[node1] not in nodes:
                        nodes.append(self.reverseNodeMappingsPOP[node1])
                    if not node2.isdigit() and self.reverseNodeMappingsPOP[node2] not in nodes:
                        nodes.append(self.reverseNodeMappingsPOP[node2])
                    if not node1.isdigit():
                        node1 = self.reverseNodeMappingsPOP[node1]                    
                    if not node2.isdigit():
                        node2 = self.reverseNodeMappingsPOP[node2]
                    link = (node1, node2)
                    reverseLink = (link[1],link[0])
                    # if link not in links and reverseLink in links:
                    #     print("Reverse direction link found", link)
                    if link not in links and reverseLink not in links:
                        links.append(link)
        return nodes, links

    def convertToConstants(self, program):
        for node in self.nodeMappingsPOP:
            var = self.nodeMappingsPOP[node]
            program = program.replace(var, str(node))
        return program

    # returns if rule1 is equivalent to rule2
    def isEquivalentRule(self, rule1, rule2):
        program1 = DT_Program(rule1, recursive_rules=False)
        if not program1.contains_rule(rule2):
            return False
        # program2 = DT_Program(rule2, recursive_rules=False)
        # if not program2.contains_rule(rule1):
        #     return False
        return True

    def getEquivalenceClasses(self, minimizedProgram, program):
        equivalentClasses = [] # stores the equivalent classes
        rulesToDelete = []
        for minRule in minimizedProgram._rules:
            currentRuleMatches = [minRule]
            for ruleNum, rule in enumerate(program._rules):
                if str(minRule) == str(rule): # same rule will be equivalent, no need to check
                    continue
                if self.isEquivalentRule(rule, minRule):
                    rulesToDelete.append(ruleNum)
                    currentRuleMatches.append(rule)
            equivalentClasses.append(currentRuleMatches)
        # if rulesToDelete:
        #     rulesToDelete.reverse()
        #     for rule in rulesToDelete:
        #         program.deleteRule(rule)
        return equivalentClasses

    # equivalent classes is an array of array and we want to select one from each array
    # take cartesian product of lists
    def getMinNodes(self, equivalentClasses):
        minNodes = 1000000
        minCombination = []
        for combination in itertools.product(*equivalentClasses):
            nodes, _ = self.getLinksNodes(combination) 
            if len(nodes) < minNodes:
                minCombination = deepcopy(combination)
                minNodes = len(nodes)
        strRules = []
        for rule in minCombination:
            strRules.append(str(rule))
        minProgram = DT_Program("\n".join(strRules), recursive_rules=False) 
        return minProgram

    # gets all ingress or egress nodes by looking at the ISP maps 
    def getAllgress(self,isIngress=True):
        rootpath = os.path.join(os.getcwd(), "AS-links")
        # loop over all directories
        # if directory matches selfPOP
        gressList = []
        for directory in os.listdir(rootpath):
            src,dst = directory.split(":")
            if src == dst:
                continue
            if isIngress and src != self.AS:
                continue
            elif not isIngress and dst != self.AS:
                continue
            path = os.path.join(rootpath, directory)
            path = os.path.join(path, "edges")
            atLeastOneGress = False
            with open(path) as f:
                edges = f.readlines()
                for edge in edges:
                    edgeSplit = edge.strip("\n").split(" -> ")
                    selfPOP = edgeSplit[0].strip()
                    secondSplit = edgeSplit[1].split(",")
                    dstPOP = ""
                    if (len(secondSplit) > 1):
                        dstPOP = secondSplit[0]+", "+secondSplit[1][:3].strip()
                    else: # corner case of hongkong
                        dstPOP = secondSplit[0].split()[0]+" "+secondSplit[0].split()[1]

                    if not isIngress:
                        tmp = selfPOP
                        selfPOP = dstPOP
                        dstPOP = tmp

                    # weight = int(secondSplit[1][4:])
                    if selfPOP not in self.nodesSelfPOP or selfPOP not in self.nodesAllPOP:
                        print("Unknown node {} found in AS {}".format(selfPOP, self.AS))
                        continue
                    else:
                        atLeastOneGress = True
                        break
            if atLeastOneGress:
                if isIngress:
                    gressList.append(dst)
                elif not isIngress:
                    gressList.append(src)
        return gressList


    def getAllCustomerPairs(self):
        ingressASes = self.getAllgress(isIngress=True)
        egressASes = self.getAllgress(isIngress=False)
        return ingressASes, egressASes

def getAllReductionNodes(filename, ASNum):
    with open(filename) as f:
        lines = f.readlines()
        for line in lines:
            cols = line.split("|")
            percentageNodeReduction = float(cols[13])
            with open("AS{}_reductions_all_pairs_nodes".format(ASNum), "a+") as f2:
                f2.write("{}\n".format(percentageNodeReduction))

def getAllReductionLinks(filename, ASNum):
    with open(filename) as f:
        lines = f.readlines()
        for line in lines:
            cols = line.split("|")
            percentageLinkReduction = float(cols[16])
            with open("AS{}_reductions_all_pairs_links".format(ASNum), "a+") as f2:
                f2.write("{}\n".format(percentageLinkReduction))

def getAllReductionRules(filename, ASNum):
    with open(filename) as f:
        lines = f.readlines()
        for line in lines:
            cols = line.split("|")
            percentageRuleReduction = float(cols[3])
            with open("AS{}_reductions_all_pairs_rules".format(ASNum), "a+") as f2:
                f2.write("{}\n".format(percentageRuleReduction))

def getAllMinimizationTime(filename, ASNum):
    with open(filename) as f:
        lines = f.readlines()
        for line in lines:
            cols = line.split("|")
            totalMinTime = float(cols[-1])
            with open("AS{}_minTime_all_pairs".format(ASNum), "a+") as f2:
                f2.write("{}\n".format(totalMinTime))

def topologyMinimizationAllPairs(ingressASes, egressASes, ASNum, runs = 1):
    name = "AS_{}_all_pairs".format(str(ASNum))
    # for ingress in ingressASes:
    #     for egress in egressASes:
    #         if ingress != egress:
    #             cases = [(ingress, ASNum, egress)]
    #             topologyMinimization(cases, runs, name, "a+")
    getAllReductionRules(name, ASNum)
    getAllReductionNodes(name, ASNum)
    getAllReductionLinks(name, ASNum)
    getAllMinimizationTime(name, ASNum)

def topologyMinimization(cases, runs, logFilePath, mode = "w+"):
    with open(logFilePath,mode) as f:
        if "w" in mode:
            f.write("(ingressAS,ASNum,egressAS)|numRulesBefore|numRulesAfter|percentageRuleReduction|numAtomsBefore|numAtomsAfter|percentageAtomReduction|numIngressNodesBefore|numIngressNodesAfter|numEgressNodesBefore|numEgressNodesAfter|numNodesBefore|numNodesAfter|percentageNodeReduction|numLinksBefore|numLinksAfter|percentageLinkReduction|minTime|eqTime|combTime|totalTime\n")
        for ASes in cases:
            ingressAS = ASes[0]
            ASNum = ASes[1]
            egressAS = ASes[2]
            for run in range(runs):
                AS = RocketfuelPoPTopo(ASNum)
                AS.addGressNodes(ingressAS, True)
                AS.addGressNodes(egressAS, False)
                if len(AS.ingressNodes) == 0:
                    print("No ingress nodes")
                    return False
                if len(AS.egressNodes) == 0:
                    print("No egress nodes")
                    return False
                numIngressNodesBefore = len(AS.ingressNodes)
                numEgressNodesBefore = len(AS.egressNodes)
                allRules = AS.convertToDatalog(ingressAS,egressAS) # only have ingress nodes 
                if len(allRules) == 0:
                    return
                program = AS.convertToProgram(allRules) 
                rules, atoms = program.stats()
                # program = AS.convertToProgram(allRulesDict[1])

                start = time.time()
                minimizedProgram = AS.minimize(program)
                end = time.time()
                minTime = end-start

                start = time.time()
                equivalentClasses = AS.getEquivalenceClasses(minimizedProgram, program)
                end = time.time()
                eqTime = end-start
                # possibleLinks = getMinLinks(equivalenceClasses)
                start = time.time()
                selectedLinksProgram = AS.getMinNodes(equivalentClasses)
                end = time.time()
                combTime = 0

                # print(program)
                # print("===============")
                # print(selectedLinksProgram)


                # actualProgram = AS.convertToConstants(str(minimizedProgram))
                # print(actualProgram)
                nodes, links = AS.getLinksNodes(program._rules)
                # nodes2, links2 = AS.getLinksNodes(selectedLinksProgram._rules)
                nodes2, links2 = AS.getLinksNodes(selectedLinksProgram._rules)
                numNodesBefore = len(nodes)
                numNodesAfter = len(nodes2)
                numLinksBefore = len(links)
                numLinksAfter = len(links2)

                ingressNodesAfterMinimizaion = []
                for node in AS.ingressNodes:
                    if AS.nodesAllPOP.index(node) in nodes2:
                        ingressNodesAfterMinimizaion.append(node)
                egressNodesAfterMinimizaion = []
                for node in AS.egressNodes:
                    if AS.nodesAllPOP.index(node) in nodes2:
                        egressNodesAfterMinimizaion.append(node)
                numIngressNodesAfter = len(ingressNodesAfterMinimizaion)
                numEgressNodesAfter = len(egressNodesAfterMinimizaion)
                numRulesBefore, numAtomsBefore = program.stats()
                numRulesAfter, numAtomsAfter = minimizedProgram.stats()
                print(program)
                print("==================")
                print(selectedLinksProgram)

                percentageRuleReduction = 100*(numRulesBefore-numRulesAfter)/numRulesBefore
                percentageAtomReduction = 100*(numAtomsBefore-numAtomsAfter)/numAtomsBefore
                percentageNodeReduction = 100*(numNodesBefore-numNodesAfter)/numNodesBefore
                percentageLinkReduction = 100*(numLinksBefore-numLinksAfter)/numLinksBefore

                totalTime = minTime+eqTime+combTime
                f.write("({ingressAS},{ASNum},{egressAS})|{numRulesBefore}|{numRulesAfter}|{percentageRuleReduction}|{numAtomsBefore}|{numAtomsAfter}|{percentageAtomReduction}|{numIngressNodesBefore}|{numIngressNodesAfter}|{numEgressNodesBefore}|{numEgressNodesAfter}|{numNodesBefore}|{numNodesAfter}|{percentageNodeReduction}|{numLinksBefore}|{numLinksAfter}|{percentageLinkReduction}|{minTime}|{eqTime}|{combTime}|{totalTime}\n".format(ingressAS=ingressAS,ASNum=ASNum,egressAS=egressAS,numRulesBefore=numRulesBefore,numRulesAfter=numRulesAfter,percentageRuleReduction=percentageRuleReduction,numAtomsBefore=numAtomsBefore, numAtomsAfter=numAtomsAfter,percentageAtomReduction=percentageAtomReduction,numIngressNodesBefore=numIngressNodesBefore,numIngressNodesAfter=numIngressNodesAfter,numEgressNodesBefore=numEgressNodesBefore,numEgressNodesAfter=numEgressNodesAfter,numNodesBefore=numNodesBefore,numNodesAfter=numNodesAfter,percentageNodeReduction=percentageNodeReduction,numLinksBefore=numLinksBefore,numLinksAfter=numLinksAfter,percentageLinkReduction=percentageLinkReduction,minTime=minTime,eqTime=eqTime,combTime=combTime,totalTime=totalTime))
    return True

def avgVarianceSummary(logFilePath):
    with open(logFilePath) as f:
        lines = f.readlines()
        totalTimes = []
        minTimes = []
        eqTimes = []
        combTimes = []
        for line in lines[1:]:
            cols = line.split("|")
            name = cols[0].replace(",","-")[1:-1] 
            numRulesBefore = int(cols[1]) 
            numRulesAfter = int(cols[2])
            percentageRuleReduction = double(cols[3])
            numAtomsBefore = int(cols[4])
            numAtomsAfter = int(cols[5])
            percentageAtomReduction = double(cols[6])
            numingressBefore = int(cols[7])
            numingressAfter = int(cols[8])
            numegressBefore = int(cols[9])
            numegressAfter = int(cols[10])
            numNodesBefore = int(cols[11])
            numNodesAfter = int(cols[12])
            percentageNodeReduction = double(cols[13])
            numLinksBefore = int(cols[14])
            numLinksAfter = int(cols[15])
            percentageLinkReduction = double(cols[16])

            totalTime = float((cols[-1].strip()))
            totalTimes.append(totalTime)
            combTime = float(cols[-2])
            combTimes.append(combTime)
            eqTime = float(cols[-3])
            eqTimes.append(eqTime)
            minTime = float(cols[-4])
            minTimes.append(minTime)
        with open(name+"_Summary.txt","w+") as f2:
            f2.write("Name: {}\n".format(name))
            f2.write("==================================\n")
            f2.write("numLinksBefore: {}\n".format(numLinksBefore))
            f2.write("numLinksAfter: {}\n".format(numLinksAfter))
            f2.write("percentageLinkReduction: {}\n".format(percentageLinkReduction))
            f2.write("==================================\n")
            f2.write("numNodesBefore: {}\n".format(numNodesBefore))
            f2.write("numNodesAfter: {}\n".format(numNodesAfter))
            f2.write("percentageNodeReduction: {}\n".format(percentageNodeReduction))
            f2.write("==================================\n")            
            f2.write("numRulesBefore: {}\n".format(numRulesBefore))
            f2.write("numRulesAfter: {}\n".format(numRulesAfter))
            f2.write("percentageRuleReduction: {}\n".format(percentageRuleReduction))
            f2.write("==================================\n")            
            f2.write("numAtomsBefore: {}\n".format(numAtomsBefore))
            f2.write("numAtomsAfter: {}\n".format(numAtomsAfter))
            f2.write("percentageAtomReduction: {}\n".format(percentageAtomReduction))
            f2.write("==================================\n")
            f2.write("Average Minimization Time: {} {}\n".format(mean(minTimes), stdev(minTimes)))
            f2.write("Average EqualityClasses Time: {} {}\n".format(mean(eqTimes), stdev(eqTimes)))
            f2.write("Average Combination Time: {} {}\n".format(mean(combTimes), stdev(combTimes)))
            f2.write("Average Total Time: {} {}\n".format(mean(totalTimes), stdev(totalTimes)))


def topologyMinimizationRandomPair(ASes, runs = 1, numRandomRuns = 1, logFileName = "all_pairs_minimization"):
    for currRun in range(numRandomRuns): 
        for ASNum in ASes:
            AS = RocketfuelPoPTopo(ASNum)
            if not AS.hasNodes:
                continue
            ingressASes, egressASes = AS.getAllCustomerPairs()
            rand_ingress = random.choice(egressASes)
            rand_egress = random.choice(ingressASes)
            successful = True
            if rand_ingress == rand_egress:
                successful  = False
            else:
                successful = topologyMinimization([(rand_ingress, ASNum, rand_egress)], runs, logFileName, mode = "a+")
            tries = 0
            while not successful and tries < 10:
                tries += 1
                rand_ingress = random.choice(egressASes)
                rand_egress = random.choice(ingressASes)
                successful = True
                if rand_ingress == rand_egress:
                    successful  = False
                else:
                    successful = topologyMinimization([(rand_ingress, ASNum, rand_egress)], runs, logFileName, mode = "a+")

def getAllASes():
    rootpath = os.path.join(os.getcwd(), "AS-links")
    ASes = []
    for directory in os.listdir(rootpath):
        src, dst = directory.split(":")
        if src not in ASes:
            ASes.append(src)
        if dst not in ASes:
            ASes.append(dst)
    return ASes

if __name__ == "__main__":
    # ingressAS = "4565"
    # ASNum = "9942"
    # egressAS = "4323"

    # ingressAS = "4323"
    # ASNum = "6939"
    # egressAS = "3356"

    # ingressAS = "2548"
    # ASNum = "1"
    # egressAS = "3549"        

    # ingressAS = "4565"
    # ASNum = "7911"
    # egressAS = "7018"    

    # ingressAS = "1"
    # ASNum = "6467"
    # egressAS = "701"

    # ingressAS = "4323"
    # ASNum = "7018"
    # egressAS = "1"    

    # ingressAS = "1"
    # ASNum = "3356"
    # egressAS = "6461"    

    # ingressAS = "4006"
    # ASNum = "1"
    # egressAS = "1239"

    # case = [(ingressAS,ASNum,egressAS)]
    # topologyMinimization(case,1,"AS852.txt")
    # avgVarianceSummary("AS852.txt")

    # testASes = ["6467","6939", "7911", "1"]
    testASes = ["6467","6939", "7911"]
    # testASes = ["7911"]
    for ASNum in testASes:
        AS = RocketfuelPoPTopo(ASNum)
        print(len(AS.nodesAllPOP))
        print(len(AS.POP_links))
        ingressASes, egressASes = AS.getAllCustomerPairs()
        print(len(ingressASes))
        print(len(egressASes))
        print(ingressASes)
        print(egressASes)
        # ingressASes = ingressASes[ingressASes.index("3549"):]
        # print(ingressASes)
        topologyMinimizationAllPairs(ingressASes, egressASes, ASNum)

    # ASes = getAllASes()
    # print(ASes)
    # topologyMinimizationRandomPair(ASes=ASes, runs=1, numRandomRuns = 1)
