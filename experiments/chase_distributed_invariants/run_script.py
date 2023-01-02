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
import Applications.Chase.chase as chase
from utils.logging import timeit
import logging
logging.basicConfig(filename='program.log', level=logging.DEBUG)
logging.debug('[run_script] Start Logging ...')


@timeit
def run_ordering_strategies_new(conn, runs=10,  num_hosts_list=[2], inverse=False, random_path=True, ordering_strategy='random', orderings=None, mode='all'):
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
            dependencies, relevant_in_hosts, relevant_out_hosts, block_list = chase_scripts.gen_dependencies_for_chase_distributed_invariants(ingress_hosts.copy(), egress_hosts.copy(), path_nodes, symbolic_IP_mapping, inverse)

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
            if not ans:
                exit()
        if os.path.isfile('program.log'):
            os.rename('program.log', 'host{}_{}Order_{}Mode_{}.log'.format(num_hosts, ordering_strategy, mode, datetime.datetime.now().strftime('%Y%m%d%H%M%S')))

@timeit
def run_ordering_strategies_single_gamma(conn, runs=10,  num_hosts_list=[2], inverse=False, random_path=True, ordering_strategy='random', orderings=None):
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
            dependencies, relevant_in_hosts, relevant_out_hosts, block_list = chase_scripts.gen_dependencies_for_chase_distributed_invariants(ingress_hosts.copy(), egress_hosts.copy(), path_nodes, symbolic_IP_mapping, inverse)

            '''
            get whitelist
            '''
            
            gamma_attributes = ['f', 'n', 'x', 'condition']
            gamma_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
            gamma_summary = ['f', block_list[0], block_list[1]]
            gamma_tablename= "W_{}".format(ordering_strategy)
            chase_scripts.gen_empty_table(conn, gamma_tablename, gamma_attributes, gamma_attributes_datatypes)

            Z_attributes = ['f', 'src', 'dst', 'n', 'x']
            Z_datatypes = ['text', 'text', 'text', 'text', 'text'] # text is much faster than inet_faure?
            Z_tablename = "Z_{}".format(ordering_strategy)
            chase_scripts.gen_empty_table(conn, Z_tablename, Z_attributes, Z_datatypes)

            whitelists_flows = chase_scripts.gen_whitelists(block_list, ingress_hosts, egress_hosts)
            for flow in whitelists_flows:
                flow_start = time.time()

                flow_tuples = [('f', flow[0], flow[1])]
                chase_scripts.update_table(conn, flow_tuples, gamma_tablename)
                
                Z_tuples = chase.gen_inverse_image_with_destbasedforwarding_applied(conn, E_tuples, gamma_tablename)
                chase_scripts.update_table(conn, Z_tuples, Z_tablename)

                Z_tuples = chase_scripts.gen_Z_for_chase_distributed_invariants(conn, E_tuples, gamma_tablename, Z_tablename, Z_attributes, Z_datatypes)
                # print("Z_tuples", Z_tuples)
                ans, count_application = chase_scripts.run_chase_distributed_invariants(conn, E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary, order_strategy=ordering_strategy, orderings=orderings)
                
                flow_end = time.time()
                print('answer', ans)
                logging.info(f'Whitelist:{flow}, Runs:{r}, Count_application:{count_application}, Answer:{ans}, TimeForRun{r}:{flow_end-flow_start:.4f}')

            end = time.time()
            logging.info(f'Numhost:{num_hosts}, LenPath:{len(path_nodes)}, Runs:{r}, Count_application:{count_application}, Answer:{ans}, TimeForRun{r}:{end-start:.4f}')
            
        if os.path.isfile('program.log'):
            os.rename('program.log', 'host{}_{}Order_{}Mode_{}.log'.format(num_hosts, ordering_strategy, mode, datetime.datetime.now().strftime('%Y%m%d%H%M%S')))



if __name__ == '__main__':
    # run_scalibility()
    # run_ordering_strategies()

    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])

    runs=1
    num_hosts_list=[128]
    random_path=True
    ordering_strategy='random'
    orderings=[0, 1, 2, 6, 3, 4, 5]
    mode='all'
    inverse = False
    start = time.time()
    # run_ordering_strategies_new(conn=conn, runs=runs, num_hosts_list=num_hosts_list, rewrite_location=rewrite_location, random_path=random_path, ordering_strategy=ordering_strategy, orderings=orderings, mode=mode)
    run_ordering_strategies_single_gamma(conn=conn, runs=runs, num_hosts_list=num_hosts_list, inverse=inverse, random_path=random_path, ordering_strategy=ordering_strategy, orderings=orderings)
    print('total run time:', time.time()-start)


