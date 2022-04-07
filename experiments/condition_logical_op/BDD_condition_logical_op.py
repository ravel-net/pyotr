import BDD_managerModule as bddmm
import sys
from time import time

from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)


import pyotr_translator_BDD.BDD_manager.encodeCUDD as encodeCUDD

DOMAIN = ['1','2','3','4','5']
DECIMAL_PLACES = 4
if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Not enough arguments provided")
    else:
        input_fileName = sys.argv[1]
        with open(input_fileName) as f_input:
            print("Time in seconds")
            print("Encoding\tConstruction\tLogical_AND\tChecking")
            lines = f_input.readlines()
            VARIABLES = encodeCUDD.findVariables(lines[0])
            bddmm.initialize(len(VARIABLES), len(DOMAIN))
            for i in range(0, len(lines)-1, 2):
            #for i in range(0,4,2):
                unencodedCond1 = lines[i]
                unencodedCond2 = lines[i+1]

				#print(unencodedCond1)
				#print(unencodedCond2)
                encode_begin = time()
                variables1 = encodeCUDD.findVariables(unencodedCond1)
                variables2 = encodeCUDD.findVariables(unencodedCond1)
                condition1, variablesArray1 = encodeCUDD.convertToCUDD(unencodedCond1, DOMAIN, variables1)
                condition2, variablesArray2 = encodeCUDD.convertToCUDD(unencodedCond2, DOMAIN, variables2)
                encode_end = time()

                construct_begin = time()
                cond1_idx = bddmm.str_to_BDD(condition1);
                cond2_idx = bddmm.str_to_BDD(condition2);
                construct_end = time()

                logical_begin = time()
                result_idx = bddmm.operate_BDDs(cond1_idx, cond2_idx, '&')
                logical_end = time()		

                checking_begin = time()
                ans = bddmm.evaluate(result_idx)
                checking_end = time()
                encode_time = (str(round(encode_end-encode_begin, 4)))
                construct_time = (str(round(construct_end-construct_begin, 4)))
                logical_or_time = (str(round(logical_end-logical_begin, 4)))
                checking_time = (str(round(checking_end-checking_begin, 4)))
                print("{}\t\t{}\t\t{}\t\t{}".format(encode_time, construct_time, logical_or_time, checking_time))
