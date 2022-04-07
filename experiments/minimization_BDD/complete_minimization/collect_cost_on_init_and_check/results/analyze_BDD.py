import sys
import os
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(dirname(abspath(__file__))))))
print(root)
sys.path.append(root)

import read_json

run_times = int(sys.argv[1])
read_json.read_components_file_BDD("./BDD_components.txt", "./BDD_components_analyzed.txt", run_times)
#read_json.read_components_file_Z3("./Z3_components.txt", "./Z3_components_analyzed.txt", run_times)
