import sys
import DFS 
import pprint

fileName = sys.argv[1]
with open(fileName, "r") as f:
	lines = f.readlines()
	variables = lines[0].split()
	p1 = DFS.Graph(variables)
	variables_dict = set()
	for var in variables:
		variables_dict.add(var)
	for line in lines[1:]:
		line = line.split()
		if line[0] in variables_dict and line[1] in variables_dict:
			p1.add_edge(line[0], line[1])
	conns = p1.connectedComponents()
	pp = pprint.PrettyPrinter(indent=4)
	pp.pprint(conns)

# print(f.read()) 
# print (fileName)