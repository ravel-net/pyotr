import sys
from os.path import dirname, abspath
import os
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)
from igraph import *
from Core.Homomorphism.Datalog.program import DT_Program
import time
    
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

        self.add_POP_links()
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
                self.nodeMappingsPOP[i] = l3
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
        with open(path) as file:
            edges = file.readlines()
            for edge in edges:
                edgeSplit = edge.strip("\n").split(" -> ")
                srcAS = edgeSplit[0].strip()
                secondSplit = edgeSplit[1].split(",")
                dst = secondSplit[0]+", "+secondSplit[1][:3].strip()
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

    def getDatalogRule(self, allPaths, destination, link, egress):
        rules = []
        prevNode = link[0]
        currNode = link[1]
        if prevNode == -1:
            head = "R({},{},{}) :- ".format(self.nodeMappingsPOP[int(currNode)],destination,str(currNode))
        else:
            head = "R({},{},{}) :- ".format(self.nodeMappingsPOP[int(currNode)],destination,str(prevNode)+str(currNode))
        for path in allPaths:
            if currNode in path:
                links = []
                indexOfNode = path.index(currNode)
                if indexOfNode == 0 and prevNode != -1:
                    continue
                elif indexOfNode > 0 and path[indexOfNode-1] != prevNode:
                    continue
                for i,vertex in enumerate(path[indexOfNode:-1]):
                    secondVertex = path[indexOfNode+i+1]
                    links.append("l({},{})".format(self.nodeMappingsPOP[vertex], self.nodeMappingsPOP[secondVertex]))
                newRule = head + "l({},{}), A({},{})".format(self.nodeMappingsPOP[path[-1]], egress,destination,egress)
                if len(links) > 0:
                    newRule = head + ",".join(links) + ", l({},{}), A({}, {})".format(self.nodeMappingsPOP[path[-1]],egress, destination,egress)
                rules.append(newRule)
        return rules

    def getShortestPaths(self):
        allPaths = []
        for ingressNode in self.ingressNodes:
            for eggressNode in self.egressNodes:
                if ingressNode == eggressNode:
                    continue
                src = self.nodesAllPOP.index(ingressNode)
                dst = self.nodesAllPOP.index(eggressNode)
                # directed = self.accessGraph.as_directed()
                paths = self.POPGraph.get_all_shortest_paths(src, dst)
                allPaths += paths
        return allPaths

    def convertToDatalog(self, egress):
        self.populateNodeMapping(True)
        self.reverseNodeMappingsPOP[egress] = egress
        allPaths = self.getShortestPaths()
        allLinks = []
        print(allPaths)
        for path in allPaths:
            for i, node in enumerate(path):
                link = (-1, node)
                if i > 0:
                    link = (path[i-1], node)
                if link not in allLinks:
                    allLinks.append(link)
        allRulesDict = {}
        allRulesArr = []
        for link in allLinks:
            linkID = str(link[0])+str(link[1])
            rules = self.getDatalogRule(allPaths, "D", link, egress)
            if rules:
                allRulesArr += rules
                allRulesDict[linkID] = rules
        return allRulesArr, allRulesDict

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
                dstPOP = secondSplit[0]+", "+secondSplit[1][:3].strip()

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
        return "\n".join(rulesArr)

    def minimize(self, program):
        program1 = DT_Program(program, recursive_rules=False)
        numRulesBefore = len(program1._rules)
        start = time.time()
        program1.minimize(False, True)
        end = time.time()
        numRulesAfter = len(program1._rules)
        print(program1)
        print("Time Taken: ", end - start)
        print("Rules Before:", numRulesBefore)
        print("Rules After:", numRulesAfter)
        return program1

    def getLinksNodes(self, program):
        program1 = DT_Program(program, recursive_rules=False)
        links = []
        nodes = []
        for rule in program1._rules:
            for atom in rule._body:
                if atom.db["name"] == "l":
                    node1 = atom.parameters[0]
                    node2 = atom.parameters[1]
                    # if node1.isdigit() or node2.isdigit():
                    #     continue
                    if not node1.isdigit() and node1 not in nodes:
                        nodes.append(node1)
                    if not node2.isdigit() and node2 not in nodes:
                        nodes.append(node2)

                    link = (self.reverseNodeMappingsPOP[node1], self.reverseNodeMappingsPOP[node2])
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

if __name__ == "__main__":
    ingress = "4323"
    ASNum = "6939"
    egress = "3356"

    # ingress = "2548"
    # ASNum = "1"
    # egress = "3549"
    AS = RocketfuelPoPTopo(ASNum)
    AS.addGressNodes(ingress, True)
    AS.addGressNodes(egress, False)
    if len(AS.ingressNodes) == 0:
        print("No ingress nodes")
    if len(AS.egressNodes) == 0:
        print("No egress nodes")
    print("Number of ingress nodes:", len(AS.ingressNodes))
    print("Number of egress nodes:", len(AS.egressNodes))
    # AS.drawPoPGraph()
    allRulesArr, allRulesDict = AS.convertToDatalog(egress) # only have ingress nodes 
    program = AS.convertToProgram(allRulesArr) 
    # program = AS.convertToProgram(allRulesDict[1])
    print(program)

    nodes, links = AS.getLinksNodes(program)

    minimizedProgram = AS.minimize(program)
    # equivalentClasses = AS.equivalenceClasses(minimizedProgram, program)
    # possibleLinks = getMinLinks(equivalenceClasses)
    # selectedLinks = getMinNodes(possibleLinks)


    # actualProgram = AS.convertToConstants(str(minimizedProgram))
    # print(actualProgram)
    nodes2, links2 = AS.getLinksNodes(str(minimizedProgram))
    print("Num Nodes:", len(nodes))
    print("Num Nodes After Minimization:", len(nodes2))
    print("Num Links:", len(links))
    print("Num Links After Minimization:", len(links2))

    # AS.add_access_links()
    # AS.populateAccessGraph()
    # print(AS.nodeMappingsAccess)
    # AS.convertToDatalog()
    # print(AS.accessNodes)
    # print(AS.nodesAllPOP)
    # AS.addIngress()
    # AS.drawAccessGraph()