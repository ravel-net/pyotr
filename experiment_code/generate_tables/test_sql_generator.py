import sys
from os.path import dirname, abspath, join


if (len(sys.argv) != 5):
	print("Incorrect arguments given. Format: python3 test_sql_generator [sql_file] [file_name] [number_times] [sql_query]")
	exit()

sql_file = sys.argv[1]
file_name = sys.argv[2]
number_times = int(sys.argv[3])
sql_query = sys.argv[4]

curr_dir = dirname(abspath(__file__))
filepath = join(curr_dir, file_name)

sql_query = "explain analyze " + sql_query

f = open(sql_file, "w")
f.write("\\o " + filepath + "\n\n")
for i in range(0,number_times):
	f.write(sql_query + "\n")
f.close()
