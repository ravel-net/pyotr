f = open("number_closure_groups.txt", 'r')
lines = f.readlines()
number_closures = []
for line in lines:
	data_points = line.split()
	number_closures = data_points
f.close()

f = open("all_length_closure_groups.txt", 'r')
lines = f.readlines()
all_data_points_lengths = []
for line in lines:
	data_points = line.split()
	all_data_points_lengths = data_points
f.close()

f = open("all_closure_group_timings.txt", 'r')
lines = f.readlines()
all_data_points_timings = []
for line in lines:
	data_points = line.split()
	all_data_points_timings = data_points
f.close()

rangeSize = {'1':25, '2':13, '3':0} 
sizes = {'1':[], '2':[], '3':[]}

all_data_points_lengths_clean = []
all_data_points_timings_clean = []

j = 0
i = 0
while i < len(all_data_points_lengths):
	for num in range(int(number_closures[j])):
		length = all_data_points_lengths[i]
		time = all_data_points_timings[i]
		size = number_closures[j]
		if int(length) > rangeSize[size]:
			all_data_points_lengths_clean.append(length)
			all_data_points_timings_clean.append(time)
		else:
			print("=================")
			print(size)
			print(length)

		if length not in sizes[size]:
			sizes[size].append(length)
		i += 1
	j += 1

f = open("scatter.dat", "w")
for i in range(len(all_data_points_lengths_clean)):
	f.write(str(all_data_points_lengths_clean[i]) + " " + str(float(all_data_points_timings_clean[i])*1000) + "\n")
f.close()

print(sizes)
# if (len(number_closures) != len(all_data_points_lengths)):
# 	print("Lengths of data points not matching. Exiting")
# 	exit()

# f = open("scatter.dat", "w")
# for i in range(len(all_data_points_lengths)):
# 	f.write(str(all_data_points_lengths[i]) + " " + str(float(number_closures[i])*1000) + "\n")
# f.close()

