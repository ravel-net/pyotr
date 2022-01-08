import psycopg2
from tqdm import tqdm 
import time
import sys
import copy
from os.path import dirname, abspath, join
root = dirname(abspath(__file__))
filename = join(root, 'variable_closure_algo')
print(filename)
sys.path.append(filename)
import closure_overhead
import pprint

host = '127.0.0.1'
user = 'postgres'
password = 'mubashir'
database = 'test'

# generate the F table
# input: tablename(subset of raw rib table,such as rib1000)
def minimize(tablename = 't_v', pos = 0):
    """
    Generate the F table
    @param tablename: the name of the F table, default rib1000
    """
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    #create f_table in database

    pp = pprint.PrettyPrinter(indent=4)
    # get prefix list
    cur.execute('select n1, n2 from {};'.format(tablename))
    prefix_list = cur.fetchall()
    tuple_removal = prefix_list[pos]
    new_table = copy.deepcopy(prefix_list)
    new_table.pop(pos)

    variables = closure_overhead.find_variables(prefix_list)
    print(prefix_list)
    graph = closure_overhead.construct_Graph(variables, prefix_list)
    conns = graph.connectedComponents()
    reverse_conns = graph.reverse_connectComponents(conns)
    minimal_tableau = closure_overhead.calculate_tableau(prefix_list, reverse_conns, len(conns))

    print("=================Orig================")
    pp.pprint(prefix_list)
    print("=================Mod================")
    pp.pprint(new_table)
    print("=================Closure================")
    pp.pprint(minimal_tableau)
    # count = 1
    # for p in tqdm(prefix_list[pos:]): # tqdm is used to show progress bar
    #     find_closure
    #     print(p)        
    #     # conn.commit()
    #     count = count + 1
    # conn.close()

if __name__ == '__main__':
    sizes = [100, 1000, 10000] #, 10000, 100000, 922067]
    minimize(tablename="test3", pos = 1)
    # sizes = [922067]
    # sizes = [500000, 922067]
    # sizes = [] #, 10000, 100000, 922067]
    # print(f"Arguments count: {len(sys.argv)}")
    # if (len(sys.argv) < 2):
    #     print("Please enter the table size")
    #     exit()
    # for i, arg in enumerate(sys.argv):
    #     if (i > 0):
    #         sizes.append(int(arg))
    # print (sizes)
    # for size in sizes:
    #     print("create f table size ", size)
    #     tablename = 'rib' + str(size)
    #     start_time = time.time()
    #     gen_f_table(tablename=tablename)
    #     print('Done! {} running time: {}'.format(tablename, time.time()-start_time))

        # create_index_fid_mark(tablename='f_table_'+tablename) TODO: Make inet index-ible
        # print('{} running time: {}'.format(tablename, time.time()-start_time))


# for num_of_tuples:
#     select new tuple from t1
#     find closure group of tuple on t1
#     create new table t2 with deleted tuple
#     run join test from closure group and t2
#     if join test successful:
#         find substitution in t2
#         substitute in new table t2
#         delete redundant links in t2
#         t1 = t2
