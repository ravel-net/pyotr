f = open("all_closure_group_timings.txt", 'r')
lines = f.readlines()
all_data_points_timings = []
for line in lines:
	data_points = line.split()
	all_data_points_timings += data_points
f.close()

f = open("all_length_closure_groups.txt", 'r')
lines = f.readlines()
all_data_points_lengths = []
for line in lines:
	data_points = line.split()
	all_data_points_lengths += data_points
f.close()

if (len(all_data_points_timings) != len(all_data_points_lengths)):
	print("Lengths of data points not matching. Exiting")
	exit()

f = open("scatter.dat", "w")
for i in range(len(all_data_points_lengths)):
	f.write(str(all_data_points_lengths[i]) + " " + str(float(all_data_points_timings[i])*1000) + "\n")
f.close()

