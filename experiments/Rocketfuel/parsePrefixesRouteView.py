from pathlib import Path
import json

def fileExists(filename):
	path = Path(filename)
	return path.is_file()

def getPrefixes(target):
	io = open(target,"r")
	return json.load(io)

# Note: rib.txt is generated by using bgpdump on a RouteView file. This current file is from 01-10-2002 (rib.20021001) from the quagga bgpd, from route-views2.oregon-ix.net collector
def storePrefixes(inputFile="rib.txt", target="prefixes2003.txt"):
	if fileExists(target):
		print("Target file {} already exists. Not recomputing paths.".format(target))
		return True
	if not fileExists(inputFile):
		print("Input rib file {} does not exist.".format(inputFile))
		return False
	ASPrefixes = {}
	with open(inputFile) as f:
		lines = f.readlines()
		totalLines = len(lines)
		i = 1
		prefix = "0"
		for line in lines:
			i += 1
			if "PREFIX" in line:
				prefix = line.strip().split(":")[1][1:]
			if "ASPATH:" in line:
				print("Line Num {}/{}".format(i,totalLines))
				AS = line.strip().split(" ")[-1]
				if AS not in ASPrefixes:
					ASPrefixes[AS] = []
				if prefix != "0" and prefix not in ASPrefixes[AS]:
					ASPrefixes[AS].append(prefix)
	with open(target, 'w') as convert_file:
		convert_file.write(json.dumps(ASPrefixes))
	return True

if __name__ == "__main__":
	storePrefixes(inputFile="rib.txt", target="prefixes2003.txt")
	ASPrefixes = getPrefixes(target="prefixes2003.txt")
	print(ASPrefixes)