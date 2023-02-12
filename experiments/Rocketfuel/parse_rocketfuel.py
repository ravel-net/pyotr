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
from experiments.Rocketfuel.parsePrefixesRouteView import getPrefixes, storePrefixes
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
        self.deployedMiddleBoxes = []
        self.middleBoxTypes = []
        self.deployedFirewall = {}
        self._nodesRule = {}

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

    def getDatalogRuleOld(self, allPaths, destination, ingressNode, ingressAS, egressAS):
        rules = []
        head = "R({},{},{}) :- ".format(ingressAS, destination, egressAS)
        for path in allPaths:
            links = []
            middleBoxes = {}
            non_middleboxes = []
            for i,vertex in enumerate(path[:-1]):
                secondVertex = path[i+1]
                if vertex == ingressNode:
                    links.append("l({},{})".format(ingressAS, self.nodeMappingsPOP[secondVertex]))
                else:
                    links.append("l({},{})".format(self.nodeMappingsPOP[vertex], self.nodeMappingsPOP[secondVertex]))
                if vertex in self.deployedMiddleBoxes: # if the path includes a node with a middle box in it
                    middleBoxType =  self.deployedMiddleBoxes[vertex]
                    if middleBoxType not in middleBoxes:
                        middleBoxes[middleBoxType] = []
                    middleBoxes[middleBoxType].append(str(middleBoxType) + "(" + str(self.nodeMappingsPOP[vertex]) + ")")    
                elif vertex != ingressNode and len(self.deployedMiddleBoxes) > 0:
                    non_middleboxes.append("D({})".format(str(self.nodeMappingsPOP[vertex])))

            if path[-1] in self.deployedMiddleBoxes:
                middleBoxType =  self.deployedMiddleBoxes[path[-1]]
                if middleBoxType not in middleBoxes:
                    middleBoxes[middleBoxType] = []
                middleBoxes[middleBoxType].append(str(middleBoxType) + "(" + str(self.nodeMappingsPOP[path[-1]]) + ")")    
            elif len(self.deployedMiddleBoxes) > 0:
                non_middleboxes.append("D({})".format(str(self.nodeMappingsPOP[path[-1]])))

            newRule = head + "l({},{}), A({},{})".format(self.nodeMappingsPOP[path[-1]], egressAS, destination,egressAS)
            if len(links) > 0:
                newRule = head + ",".join(links) + ", l({},{}), A({}, {})".format(self.nodeMappingsPOP[path[-1]],egressAS, destination,egressAS)
            for middleBoxType in self.middleBoxTypes:
                if middleBoxType in middleBoxes:
                    newRule += ","
                    newRule += ",".join(middleBoxes[middleBoxType])
            if len(non_middleboxes) > 0:
                newRule += ","
                newRule += ",".join(non_middleboxes)
            print(newRule)
            rules.append(newRule)
        return rules    

    def getDatalogRule(self, allPaths, destination, ingressNode, ingressAS, egressAS):
        rules = []
        for path in allPaths:
            firewallConditions = [] # need to keep track of all firewall conditions to add to head
            links = []
            for i,vertex in enumerate(path):
                secondVertex = egressAS
                if i < len(path)-1:
                    secondVertex = path[i+1]
                if secondVertex == egressAS:
                    links.append("l({},{},0)".format(self.nodeMappingsPOP[vertex], secondVertex))
                elif vertex == ingressNode:
                    links.append("l({},{},0)".format(ingressAS, self.nodeMappingsPOP[secondVertex]))
                else:
                    # print("checking vertex", vertex)
                    if vertex in self.deployedMiddleBoxes: # if the path includes a node with a firewall in it
                        middleBoxName =  self.deployedMiddleBoxes[vertex]
                        middleBoxNum = self.middleBoxTypes.index(middleBoxName)+1
                        links.append("l({},{},{})".format(self.nodeMappingsPOP[vertex], self.nodeMappingsPOP[secondVertex], middleBoxNum))
                    else:
                        links.append("l({},{},0)".format(self.nodeMappingsPOP[vertex], self.nodeMappingsPOP[secondVertex]))

            head = "R({},{},{}) :- ".format(ingressAS, destination, egressAS)
            # if len(firewallConditions) > 0:
            #     head = "R({},{},{})[And({})] :- ".format(ingressAS, destination, egressAS, ",".join(firewallConditions))

            newRule = head + ",".join(links) + ", A({}, {})".format(destination,egressAS)
            
            print(newRule)
            rules.append(newRule)
        return rules

    def getDatalogRuleFirewall(self, allPaths, destination, ingressNode, ingressAS, egressAS):
        rules = []
        for path in allPaths:
            firewallConditions = [] # need to keep track of all firewall conditions to add to head
            links = []
            for i,vertex in enumerate(path):
                secondVertex = egressAS
                if i < len(path)-1:
                    secondVertex = path[i+1]
                if secondVertex == egressAS:
                    links.append("l({},{},{})".format(self.nodeMappingsPOP[vertex], secondVertex, destination))
                elif vertex == ingressNode:
                    links.append("l({},{},{})".format(ingressAS, self.nodeMappingsPOP[secondVertex], destination))
                else:
                    print("checking vertex", vertex)
                    if vertex in self.deployedFirewall: # if the path includes a node with a firewall in it
                        firewallCondition =  self.deployedFirewall[vertex]
                        firewallConditions.append(firewallCondition)
                        links.append("l({},{},{})[{}]".format(self.nodeMappingsPOP[vertex], self.nodeMappingsPOP[secondVertex], destination, firewallCondition))
                    else:
                        links.append("l({},{},{})".format(self.nodeMappingsPOP[vertex], self.nodeMappingsPOP[secondVertex],destination))

            head = "R({},{},{}) :- ".format(ingressAS, destination, egressAS)
            if len(firewallConditions) > 0:
                head = "R({},{},{})[And({})] :- ".format(ingressAS, destination, egressAS, ",".join(firewallConditions))

            newRule = head + ",".join(links) + ", A({}, {})".format(destination,egressAS)
            
            print(newRule)
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

    def convertToDatalog(self, ingressAS, egressAS, firewall = False):
        self.populateNodeMapping(True)
        self.reverseNodeMappingsPOP[egressAS] = egressAS
        allPaths = self.getShortestPaths()
        if len(allPaths) == 0: # can't do any computation if AS has no paths
            return []
        allLinks = []
        print(allPaths)
        for path in allPaths:
            path.insert(0, -1)
        allRules = []
        if firewall:
            allRules = self.getDatalogRuleFirewall(allPaths=allPaths, destination="D", ingressNode=-1, ingressAS=ingressAS, egressAS=egressAS)
        else:
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

    def setNodes(self, rule):
        if rule not in self._nodesRule:
            self._nodesRule[rule] = []
        for atom in rule._body:
            if atom.db["name"] == "l":
                node1 = atom.parameters[0]
                node2 = atom.parameters[1]
                # if node1.isdigit() or node2.isdigit():
                #     continue
                if not node1.isdigit():
                    self._nodesRule[rule].append(node1)
                if not node2.isdigit():
                    self._nodesRule[rule].append(node2)

    def convertToProgram(self, rulesArr):
        program = DT_Program("\n".join(rulesArr), recursive_rules=False)    
        for rule in program._rules:
            self.setNodes(rule)
        return program

    def convertToFirewallProgram(self, rulesArr):
        program = DT_Program("\n".join(rulesArr), {"R":["integer", "inet_faure", "integer"], "l":["integer", "integer", "inet_faure"], "A":["inet_faure", "integer"]}, domains={}, c_variables=['D'], reasoning_engine='z3', reasoning_type={'D':'BitVec'}, datatype='inet_faure', simplification_on=False, c_tables=["R", "l", "A"], faure_evaluation_mode='implication', recursive_rules=False)
        for rule in program._rules:
            self.setNodes(rule)
        return program

    def minimize(self, program):
        minimizedProgram = deepcopy(program)
        numRulesBefore = len(minimizedProgram._rules)
        start = time.time()
        minimizedProgram.minimize(False, True)
        end = time.time()
        numRulesAfter = len(minimizedProgram._rules)
        return minimizedProgram

    def getNodes(self, rulesArr):
        nodes = {}
        for rule in rulesArr:
            ruleNodes = self._nodesRule[rule]
            # ruleNodes = ["a","b","c"]
            for node in ruleNodes:
                if node not in nodes:
                    nodes[node] = 0
        return len(nodes)

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

    def isEquivalentRule(self, rule1, rule2, firewall):
        program1 = ""
        if not firewall:
            program1 = DT_Program(rule2, recursive_rules=False)
        else:
            program1 = self.convertToFirewallProgram([str(rule2)])
        if not program1.contains_rule(rule1):
            return False
        if firewall:
            program2 = self.convertToFirewallProgram([str(rule1)])
            if not program2.contains_rule(rule2):
                return False
        return True

    def getEquivalenceClasses(self, minimizedProgram, program, firewall):
        equivalentClasses = [] # stores the equivalent classes
        rulesToDelete = []
        numProgramRules = len(program._rules)
        for minRule in minimizedProgram._rules:
            rulesToDelete = []
            currentRuleMatches = []
            for ruleNum, rule in enumerate(program._rules):
                #if str(minRule) == str(rule): # same rule will be equivalent, no need to check
                #    continue
                if self.isEquivalentRule(rule, minRule, firewall):
                    currentRuleMatches.append(rule)
                    rulesToDelete.append(ruleNum)
            rulesToDelete.reverse()
            for ruleNum in rulesToDelete:
                program.deleteRule(ruleNum)
            equivalentClasses.append(currentRuleMatches)
        totalRules = 0
        for eqclass in equivalentClasses:
            totalRules += len(eqclass)
        if totalRules != numProgramRules:
            print("Not all rules were considered for equivalence. Total Rules considered were {} while the original program had {} rules".format(totalRules, numProgramRules))
            if not firewall:
                exit()
        return equivalentClasses

    # equivalent classes is an array of array and we want to select one from each array
    # take cartesian product of lists
    def getMinNodes(self, equivalentClasses, firewall):
        minNodes = 1000000
        minCombination = []
        i = 0
        print(equivalentClasses)
        for combination in itertools.product(*equivalentClasses):
            i += 1
            numNodes = self.getNodes(combination) 
            if numNodes < minNodes:
                minCombination = deepcopy(combination)
                minNodes = numNodes
        print("\n\n==============================NUM COMB ========================")
        print("num comb: ", i)
        print("\n============================================================\n")
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

    def getASPrefixes(self, AllASPrefixes, egressAS):
        return AllASPrefixes[egressAS]
        # ASPrefixes = {}
        # for AS in egressASes:
        #     if AS in AllASPrefixes:
        #         ASPrefixes[AS] = AllASPrefixes[AS]
        # return ASPrefixes


    def getShortestPrefix(self, prefixes):
        minimumLength = 32
        for prefix in prefixes:
            length = int(prefix.split("/")[-1])
            if length < minimumLength:
                minimumLength = length
        minLengthPrefixes = []
        for prefix in prefixes:
            length = int(prefix.split("/")[-1])
            if length == minimumLength and prefix not in minLengthPrefixes:
                minLengthPrefixes.append(prefix)
        return minLengthPrefixes

    # takes a list of prefixes as input and converts them to a blocking firewall
    def convertListToFirewall(self, prefixesList):
        firewall = ""
        if len(prefixesList) > 0:
            prefixBlockingStrings = []
            for prefix in prefixesList:
                prefixBlockingStrings.append("D != {}".format(prefix))
            firewall = "And({})".format(",".join(prefixBlockingStrings))
        return firewall

    # This function gets all prefixes advertised by a particular eggress AS. Then, it selects the shortest length prefixes (which are likely to include most other advertised prefixes). Finally, it picks percentageNodes number of nodes from the current AS to deploy a firewall on. For each node, it either blocks all the shortest prefixes or selects numSinglePrefixesToPick from the list of all advertised prefixes and blocks those. The probability of picking the shortest path prefix vs from all prefixes is currently 50% (e.g. roughly 50% of the nodes block all shortest length prefixes while the other 50% block some randomly chosen prefixes.)
    # numSinglePrefixesToPick is the number of prefixes picked from the list of advertised prefixes to block as a firewall.
    def addFirewallsSingleAS(self, inputFile="rib.txt", target="prefixes2003.txt", percentageNodes = 75, egressAS = "1", numSinglePrefixesToPick = 2, shortestLengthPickProb = 0.5):
        if not(storePrefixes(inputFile=inputFile, target=target)):
            print("There was an error importing prefixes. Exiting.")
            exit()
        AllASPrefixes = getPrefixes(target)
        egressPrefixes = self.getASPrefixes(AllASPrefixes, egressAS)
        shortestPrefixes = self.getShortestPrefix(egressPrefixes)
        shortestFirewall = self.convertListToFirewall(shortestPrefixes)

        self.percentFirewalls = percentageNodes
        numNodes = len(self.nodesSelfPOP)
        n = (int) (numNodes * percentageNodes/100)
        selectedNodes = random.sample(self.nodesSelfPOP, n)
        self.deployedFirewall = {}
        for node in selectedNodes:
            firewall = ""
            random_choice = random.uniform(0, 1)
            if random_choice < shortestLengthPickProb:
                firewall = shortestFirewall
            else:
                randomPrefixes = random.sample(egressPrefixes, numSinglePrefixesToPick)
                firewall = self.convertListToFirewall(randomPrefixes)
            nodeIndex = self.nodesAllPOP.index(node)
            self.deployedFirewall[nodeIndex] = firewall
        print(self.deployedFirewall)
        return # do nothing

    def addFirewalls(self, inputFile="rib.txt", target="prefixes2003.txt", percentageNodes = 25):
        if not(storePrefixes(inputFile=inputFile, target=target)):
            print("There was an error importing prefixes. Exiting.")
            exit()
        AllASPrefixes = getPrefixes(target)
        _, egressASes = self.getAllCustomerPairs()
        egressPrefixes = self.getASPrefixes(AllASPrefixes, egressASes)
        shortestPrefixes = []
        for AS in egressPrefixes:
            shortestPrefixes += self.getShortestPrefix(egressPrefixes[AS])
        self.deployedFirewall[11] = "D != 192.168.1.1"
        self.deployedFirewall[6] = "D != 192.168.1.1"

        # self.percentFirewalls = percentageNodes
        # numNodes = len(self.nodesSelfPOP)
        # n = (int) (numNodes * percentageNodes/100)
        # selectedNodes = random.sample(self.nodesSelfPOP, n)
        # self.deployedFirewall = {}
        # for node in selectedNodes:
        #     firewall = random.sample(middleBoxes, 1)[0]
        #     nodeIndex = self.nodesAllPOP.index(node)
        #     self.deployedFirewall[nodeIndex] = firewall

        return # do nothing

    def getAllCustomerPairs(self):
        ingressASes = self.getAllgress(isIngress=True)
        egressASes = self.getAllgress(isIngress=False)
        return ingressASes, egressASes

    # Adds percentMiddleBoxes % of middle boxes to the AS. Among the nodes selected for middle boxes, the probability of the selecting each type of middle box is uniform (e.g. for two middle boxes the proability is half for each)
    def addMiddleBoxes(self, middleBoxes, percentMiddleBoxes):
        self.percentMiddleBoxes = percentMiddleBoxes
        self.middleBoxTypes = middleBoxes
        numNodes = len(self.nodesSelfPOP)
        n = (int) (numNodes * percentMiddleBoxes/100)
        selectedNodes = random.sample(self.nodesSelfPOP, n)
        self.deployedMiddleBoxes = {}
        for node in selectedNodes:
            middleBox = random.sample(middleBoxes, 1)[0]
            nodeIndex = self.nodesAllPOP.index(node)
            self.deployedMiddleBoxes[nodeIndex] = middleBox
        print(self.deployedMiddleBoxes)

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

def topologyMinimizationAllPairs(ingressASes, egressASes, ASNum, runs = 1,  middleBoxes=[],percentMiddleBoxes=0, firewall=False):
    name = "AS_{}_all_pairs".format(str(ASNum))
    for ingress in ingressASes:
        for egress in egressASes:
            if ingress != egress:
                case = (ingress, ASNum, egress)
                topologyMinimization(case = case, runs = runs, logFilePath=name, mode="a+", middleBoxes=middleBoxes, percentMiddleBoxes=percentMiddleBoxes, firewall=firewall)
    getAllReductionRules(name, ASNum)
    getAllReductionNodes(name, ASNum)
    # getAllReductionLinks(name, ASNum)
    # getAllMinimizationTime(name, ASNum)



def topologyMinimization(case, runs, logFilePath, mode = "w+", middleBoxes = [], percentMiddleBoxes = 0, firewall = False, percentageNodesFirewall = 25):
    with open(logFilePath,mode) as f:
        if "w" in mode:
            f.write("(ingressAS,ASNum,egressAS)|numRulesBefore|numRulesAfter|percentageRuleReduction|numAtomsBefore|numAtomsAfter|percentageAtomReduction|numIngressNodesBefore|numIngressNodesAfter|numEgressNodesBefore|numEgressNodesAfter|numNodesBefore|numNodesAfter|percentageNodeReduction|numLinksBefore|numLinksAfter|percentageLinkReduction|minTime|eqTime|combTime|totalTime\n")
        ingressAS = case[0]
        ASNum = case[1]
        egressAS = case[2]
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
            if percentMiddleBoxes > 0:
                AS.addMiddleBoxes(middleBoxes, percentMiddleBoxes)
            if firewall:
                # AS.addFirewalls(inputFile="rib.txt", target="prefixes2003.txt", percentageNodes = 25)
                AS.addFirewallsSingleAS(inputFile="rib.txt", target="prefixes2003.txt", percentageNodes = percentageNodesFirewall, egressAS = egressAS)
            allRules = AS.convertToDatalog(ingressAS,egressAS, firewall) # only have ingress nodes 
            if len(allRules) == 0:
                return

            if firewall:
                program = AS.convertToFirewallProgram(allRules) 
            else:
                program = AS.convertToProgram(allRules) 
            rules, atoms = program.stats()
            # program = AS.convertToProgram(allRulesDict[1])

            start = time.time()
            minimizedProgram = AS.minimize(program)
            end = time.time()
            minTime = end-start
            
            programCopy = deepcopy(program)
            start = time.time()
            equivalentClasses = AS.getEquivalenceClasses(minimizedProgram, program, firewall)
            end = time.time()
            eqTime = end-start
            # possibleLinks = getMinLinks(equivalenceClasses)
            start = time.time()
            selectedLinksProgram = AS.getMinNodes(equivalentClasses, firewall)
            end = time.time()
            combTime = end-start
            # print(program)
            # print("===============")
            # print(selectedLinksProgram)


            # actualProgram = AS.convertToConstants(str(minimizedProgram))
            # print(actualProgram)
            nodes, links = AS.getLinksNodes(programCopy._rules)
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
            numRulesBefore, numAtomsBefore = programCopy.stats()
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
            percentageRuleReduction = float(cols[3])
            numAtomsBefore = int(cols[4])
            numAtomsAfter = int(cols[5])
            percentageAtomReduction = float(cols[6])
            numingressBefore = int(cols[7])
            numingressAfter = int(cols[8])
            numegressBefore = int(cols[9])
            numegressAfter = int(cols[10])
            numNodesBefore = int(cols[11])
            numNodesAfter = int(cols[12])
            percentageNodeReduction = float(cols[13])
            numLinksBefore = int(cols[14])
            numLinksAfter = int(cols[15])
            percentageLinkReduction = float(cols[16])

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

def getMeanVariance(filename):
    totalTimes = []
    with open(filename) as f:
        lines = f.readlines()
        for line in lines[1:]:
            totalTime = float(line.split("|")[-1].strip())
            totalTimes.append(totalTime)
    return mean(totalTimes), stdev(totalTimes)

def timingExperiments(cases, runs = 1, middleBoxes=[], percentMiddleBoxes=0, firewall = True, outputFileName = "experiments.dat", percentageNodesFirewall=25):
    with open(outputFileName, "w+") as outputFile:
        outputFile.write("AS\tseconds\tstddev\n")
        for case in cases:
            filename = "AS{}.txt".format(case[1])
            topologyMinimization(case = case, runs = runs, logFilePath=filename, mode = "w+", middleBoxes=middleBoxes, percentMiddleBoxes=percentMiddleBoxes, firewall = firewall, percentageNodesFirewall = percentageNodesFirewall)
            meanTime, varianceTime = getMeanVariance(filename)
            outputFile.write("{}\t{}\t{}\n".format(case[1], meanTime, varianceTime))
            avgVarianceSummary(filename)

def sigcommTimingExperiments(runs = 1, firewall = False, middleBoxes=[],percentMiddleBoxes=0, percentageNodesFirewall=25):
    cases = []

    ingressAS = "4323"
    ASNum = "6939"
    egressAS = "3356"
    cases.append((ingressAS,ASNum,egressAS))

    ingressAS = "1"
    ASNum = "6467"
    egressAS = "701"
    cases.append((ingressAS,ASNum,egressAS))
    
    ingressAS = "4565"
    ASNum = "7911"
    egressAS = "7018"    
    cases.append((ingressAS,ASNum,egressAS))

    ingressAS = "2548"
    ASNum = "1"
    egressAS = "3549"        
    cases.append((ingressAS,ASNum,egressAS))

    # ingressAS = "4323"
    # ASNum = "7018"
    # egressAS = "1"    

    # ingressAS = "1"
    # ASNum = "3356"
    # egressAS = "6461"    

    # ingressAS = "4006"
    # ASNum = "1"
    # egressAS = "1239"

    timingExperiments(cases = cases, runs = runs, middleBoxes=middleBoxes,percentMiddleBoxes=percentMiddleBoxes, firewall = firewall, percentageNodesFirewall=percentageNodesFirewall)

def sigcommReductionExperimentsFirewall(runs = 1, firewall = True, percentageNodesFirewall=100, ASNum="6467"):
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
    topologyMinimizationAllPairs(ingressASes = ingressASes, egressASes= egressASes, runs = 10, ASNum=ASNum, firewall = True)

if __name__ == "__main__":
    #sigcommTimingExperiments(runs = 10, firewall = False, middleBoxes=["M","F"],percentMiddleBoxes=25, percentageNodesFirewall=0)
    #sigcommTimingExperiments(runs = 10, firewall = False, middleBoxes=[],percentMiddleBoxes=0, percentageNodesFirewall=0)
    # sigcommReductionExperimentsFirewall(runs = 1, firewall = True, percentageNodesFirewall=25, ASNum="6467")
    sigcommTimingExperiments(runs = 10, firewall = True, middleBoxes=[],percentMiddleBoxes=0, percentageNodesFirewall=25)
    exit()
    # testASes = ["6467","6939", "7911", "1"]
    # testASes = ["6467","6939", "7911"]
    testASes = ["6939"]
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
        topologyMinimizationAllPairs(ingressASes = ingressASes, egressASes= egressASes, runs = 10, ASNum=ASNum, firewall = True)
        # topologyMinimizationAllPairs(ingressASes = ingressASes, egressASes= egressASes, runs = 10, ASNum=ASNum, middleBoxes=["M","F"], percentMiddleBoxes=75, firewall = True)

    # ASes = getAllASes()
    # print(ASes)
    # topologyMinimizationRandomPair(ASes=ASes, runs=1, numRandomRuns = 1)


