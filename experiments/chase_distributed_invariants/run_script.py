import os
import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time
import datetime
import psycopg2
from tqdm import tqdm
import databaseconfig as cfg
import experiments.gen_large_tableau.func_gen_tableau as func_gen_tableau
import experiments.chase_distributed_invariants.script_chase_distributed_invariants as chase_scripts
from utils.logging import timeit
import logging
logging.basicConfig(filename='program.log', level=logging.DEBUG)
logging.debug('[run_script] Start Logging ...')


@timeit
def run_ordering_strategies_new(conn, runs=10, num_hosts_list=[2], random_path=True, ordering_strategy='random', orderings=None, mode='all'):
    AS_num = 7018

    file_dir  = '/../../topo/ISP_topo/'
    filename = "{}_edges.txt".format(AS_num)

    as_tablename = 'as_{}'.format(AS_num)
    topo_tablename = "topo_{}".format(AS_num)

    E_tablename = 'E'
    E_summary = ['f', 's', 'd']
    E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    E_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]']

    E_tuples, path_nodes, symbolic_IP_mapping = None, None, None
    if not random_path:
        E_tuples, path_nodes, symbolic_IP_mapping = chase_scripts.gen_E_for_chase_distributed_invariants(conn, file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes)

    for num_hosts in num_hosts_list:
        for r in tqdm(range(runs)):
            start = time.time()
            if random_path: 
                E_tuples, path_nodes, symbolic_IP_mapping = chase_scripts.gen_E_for_chase_distributed_invariants(conn, file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes)

            ingress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "10.0.0.1")
            egress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "12.0.0.1")

            # generate dependencies
            dependencies, relevant_in_hosts, relevant_out_hosts, block_list = chase_scripts.gen_dependencies_for_chase_distributed_invariants(ingress_hosts.copy(), egress_hosts.copy(), path_nodes, symbolic_IP_mapping)

            '''
            get whitelist
            '''
            gamma_attributes = ['f', 'n', 'x', 'condition']
            gamma_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
            gamma_summary = None
            gamma_tablename= "W_{}".format(ordering_strategy)
            gamma_summary = chase_scripts.gen_gamma_table(conn, block_list, ingress_hosts, egress_hosts, gamma_tablename, gamma_attributes, gamma_attributes_datatypes, mode)

            
            Z_attributes = ['f', 'src', 'dst', 'n', 'x']
            Z_datatypes = ['text', 'text', 'text', 'text', 'text'] # text is much faster than inet_faure?
            Z_tablename = "Z_{}".format(ordering_strategy)
            Z_tuples = chase_scripts.gen_Z_for_chase_distributed_invariants(conn, E_tuples, gamma_tablename, Z_tablename, Z_attributes, Z_datatypes)
            # print("block_list", block_list)
            #step2 and step3
            ans, count_application = chase_scripts.run_chase_distributed_invariants(conn, E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary, order_strategy=ordering_strategy, orderings=orderings)
            
            print('answer', ans)

            end = time.time()
            logging.info(f'Numhost:{num_hosts}, LenPath:{len(path_nodes)}, Runs:{r}, Count_application:{count_application}, Answer:{ans}, TimeForRun{r}:{end-start:.4f}')

        if os.path.isfile('program.log'):
            os.rename('program.log', 'host{}_{}Order_{}Mode_{}.log'.format(num_hosts, ordering_strategy, mode, datetime.datetime.now().strftime('%Y%m%d%H%M%S')))

        



if __name__ == '__main__':
    # run_scalibility()
    # run_ordering_strategies()

    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])

    runs=50
    num_hosts_list=[128]
    random_path=True
    ordering_strategy='random'
    orderings=[0, 1, 2, 6, 3, 4, 5]
    mode='all'

    start = time.time()
    run_ordering_strategies_new(conn, runs, num_hosts_list, random_path,ordering_strategy, orderings, mode)
    print('total run time:', time.time()-start)


