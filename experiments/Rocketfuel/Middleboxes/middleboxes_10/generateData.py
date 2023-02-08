# File used to generate data (mean and variance) for reductions with middle boxes
import sys
from os.path import dirname, abspath
import os
root = dirname(dirname(dirname(dirname(dirname(abspath(__file__))))))
sys.path.append(root)
from experiments.Rocketfuel.parse_rocketfuel import getMeanVariance

def extractMeanVarianceNodeRules(startingPath="./", outputFileName = "AS_minimization_middleboxes.dat"):
	with open("experiments_rule_nodes.dat", "w+") as outputFile:
		outputFile.write("%\trule-red\tstddev-rule\tnode-red\tstddev-node\n")
		for file in os.listdir(startingPath):
			d = os.path.join(startingPath, file)
			if not os.path.isdir(d):
				continue
			percentage = d.split("/")[-1].strip()
			ruleSummary = ""
			nodeSummary = ""
			for dataFile in os.listdir(d):
				if "rule" in dataFile:
					relativePath = os.path.join(d, dataFile)
					mean,var = getMeanVariance(relativePath)
					ruleSummary = "{}\t{}".format(mean,var)
				if "node" in dataFile:
					relativePath = os.path.join(d, dataFile)
					mean,var = getMeanVariance(relativePath)
					nodeSummary = "{}\t{}".format(mean,var)
			outputFile.write("{}\t{}\t{}\n".format(percentage, ruleSummary, nodeSummary))

if __name__ == "__main__":
	extractMeanVarianceNodeRules(startingPath="./", outputFileName = "AS_minimization_middleboxes.dat")
