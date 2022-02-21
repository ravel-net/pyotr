
datName =  "scatter.dat"
f = open(datName, "r")
lines = f.readlines()
groups = []
sumGroups = {}
numGroups = {}
for line in lines:
	length = line.split()[0]
	time = line.split()[1]
	if length not in groups:
		groups.append(length)
		sumGroups[length] = float(time)
		numGroups[length] = 1
	else:
		sumGroups[length] += float(time)
		numGroups[length] += 1

f2 = open("scatter2.dat","w")
for group in groups:
	print (group)
	average = sumGroups[group]/numGroups[group]
	f2.write(group + " " + str(average) + "\n")