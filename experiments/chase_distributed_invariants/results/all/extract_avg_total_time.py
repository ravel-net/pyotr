import os
import sys

with open("averages.txt", 'w') as avg:
   for filename in os.listdir(os.getcwd()):
      if filename == sys.argv[0] or filename == "averages.txt":
         continue
      num_hosts = filename.split("_")[1][5:]
      total_times = []
      with open(os.path.join(os.getcwd(), filename), 'r') as f: # open in readonly mode
         lines = f.readlines()[1:]
         for line in lines:
            time = float(line.split(" ")[-1])
            total_times.append(time)
      avg.write(num_hosts + " " + str(sum(total_times)/(1000*len(total_times))) + "\n")
         # do your stuff