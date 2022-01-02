import sys

folder = sys.argv[1]
file = sys.argv[2]
f = open(folder + "/" + file)
lines = f.read()[1:-2].split(',')
sum = 0
i = 0
for time in lines:
	sum += float(time)
	i += 1
print(file)
print(str(sum/i) + " ms")