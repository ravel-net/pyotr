import sys

file_list = ["inet/UIUC_machine/inet_postgres_select_1000_20.txt", "inet_faure/UIUC_machine/inet_faure_select_1000_20.txt", "text/UIUC_machine/text_select_1000_20.txt", "inet/UIUC_machine/inet_postgres_join_1000_20.txt", "inet_faure/UIUC_machine/inet_faure_join_1000_20.txt", "text/UIUC_machine/text_join_1000_20.txt"]

data = []
for file in file_list:
	f = open(file)
	float_list = []
	lines = f.read()[1:-2].split(',')
	for element in lines:
		float_list.append(float(element))
	Output = sorted(float_list, key = float)
	data.append(Output)

# print(data)
counter = 0
for counter in range(0, 20):
	line = str((counter+1)/20)+"\t"
	for lines in data:
		line += "{:.2f}".format(lines[counter]) + "\t"
	print(line)