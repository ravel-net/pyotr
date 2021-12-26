import sys
from os.path import dirname, abspath, join


sql_file = "test1.sql"
file_name = "string_select_1000.txt"
number_times = 20
sql_query = "select prefix & '255.255.0.0/16' from rib1000;"


curr_dir = dirname(abspath(__file__))
filepath = join(curr_dir, file_name)

sql_query = "explain analyze " + sql_query

f = open(sql_file, "w")
f.write("\\o " + filepath + "\n\n")
for i in range(0,number_times):
	f.write(sql_query + "\n")
f.close()