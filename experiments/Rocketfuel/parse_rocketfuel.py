import sys
from os.path import dirname, abspath
import os
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
from igraph import *
    
class RocketfuelPoPTopo:
    """
    A class used to represent a rocketfuel AS PoP-level topology.

    Attributes
    ----------
    numVertices : int
        the number of vertices of a given AS PoP topology
    ASes : string[]
        list of ASes (including itself) in the PoP topology
    links : DT_Rule[]
        list of all links in the topology


    Methods
    -------
    calculatePaths(src, dest)
        returns the paths between a source and destinations. Currently, paths are simple paths
    """
    pathDir = os.path.join(os.getcwd(), "AS-links")


    def __init__(self, AS = "1"):
        dir_list = os.listdir(self.pathDir)
        self.links = []
        self.nodesSelf = []
        self.nodesAll = {}
        self.nodeNum = 0
        AS_name_length = len(AS)
        for direc in dir_list:
            if direc[:AS_name_length+1] == AS+"_":
                edgesPath = os.path.join(self.pathDir, direc, "edges")
                self.add_links(edgesPath)
        self.g = Graph()
        self.populateGraph()
        layout = self.g.layout("kk")
        plot(self.g, layout=layout)
    # def __str__(self):
    #     DT_Program_str = ""
    #     for rule in self._rules:
    #         DT_Program_str += str(rule) + "\n"
    #     return DT_Program_str[:-1] # removing the last \n

    def populateGraph(self):
        self.g.add_vertices(self.nodeNum)
        for link in self.links:
            src = self.nodesAll[link[0]]
            dst = self.nodesAll[link[1]]
            self.g.add_edges([(src,dst)])

    def add_links(self, path):
        with open(path) as file:
            edges = file.readlines()
            for edge in edges:
                edgeSplit = edge.strip("\n").split(" -> ")
                srcAS = edgeSplit[0].strip()
                secondSplit = edgeSplit[1].split(",")
                dstSrc = secondSplit[0]+", "+secondSplit[1][:3].strip()
                weight = int(secondSplit[1][4:])
                if srcAS not in self.nodesSelf:
                    self.nodesSelf.append(srcAS)
                if srcAS not in self.nodesAll:
                    self.nodesAll[srcAS] = self.nodeNum
                    self.nodeNum += 1
                if dstSrc not in self.nodesAll:
                    self.nodesAll[dstSrc] = self.nodeNum
                    self.nodeNum += 1

                newLink = (srcAS, dstSrc)
                newLinkReverse = (dstSrc, srcAS)
                if newLink not in self.links and newLinkReverse not in self.links:
                    self.links.append(newLink)

if __name__ == "__main__":
    RocketfuelPoPTopo("3")