import sys
import os
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(dirname(abspath(__file__))))))
print(root)
sys.path.append(root)

import utils.BDD_translator.optimize_method.read_json as read_json

# read_json.read_components_file_BDD("./BDD_components.txt", "./BDD_components_analyzed.txt")
read_json.read_components_file_Z3("./Z3_components.txt", "./Z3_components_analyzed.txt")
