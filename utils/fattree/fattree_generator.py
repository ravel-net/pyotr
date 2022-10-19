from copy import copy

class Fattree:
    """
    k-ary fat tree topology

    Parameters:
    -----------
    k: integer(even, >= 4)
        The number of ports 
    
    Functions:
    ----------
    generate_base_program(dst_host): string
        Generate datalog program. 
        Input destination host. 'dst_host' begin with 'h', follows the number. 
        Return datalog program that the rules connected by '\n'.
    """
    def __init__(self, k=4) -> None:
        self._k = k
        self._num_core = int((k/2))**2 
        self._num_pods = k
        self._num_connected_core_per_aggr = int(k/2)
        self._num_connected_aggr_per_core = int(k/2)
        self._num_connected_aggr_per_edge = int(k/2)
        self._num_connected_edge_per_aggr = int(k/2)
        self._num_connected_hosts_per_edge = int(k/2)
        self._num_edge_per_pod = int(k/2)
        self._num_aggr_per_pod = int(k/2)
        self._num_total_hosts = self._num_connected_hosts_per_edge*self._num_edge_per_pod*self._num_pods
        self._num_total_hosts_per_pod = self._num_connected_hosts_per_edge*self._num_edge_per_pod

        self._core_level = 3
        self._aggregation_level = 2
        self._edge_level = 1
        self._host_level = 0

        self._cores = []
        self._generate_cores()
        self._connectivity = {}
        self._aggregrations = []
        self._edges = []
        self._pods = {}
        self._core_aggr_mapping = {}
        self._aggr_core_mapping = {}
        self._aggr_edge_mapping = {}
        self._edge_aggr_mapping = {}
        self._edge_host_mapping = {}
        self._host_edge_mapping = {}
        self._generate_pods()
        
        self._hosts = []
        self._generate_hosts()

        self.rules = []

        self.total_atoms = 0
    
    def _generate_cores(self):
        for idx in range(1, self._num_core+1):
            self._cores.append("c"+str(idx))
    
    def _generate_pods(self):
        for idx in range(1, self._num_pods+1):
            pod = "pod"+str(idx)

            self._pods[pod] = {"aggr":[], "edge":[]}

            for aggr_idx in range((idx-1)*(self._num_aggr_per_pod)+1, (idx-1)*(self._num_aggr_per_pod)+self._num_aggr_per_pod+1):
                aggr = "a"+str(aggr_idx)
                self._aggregrations.append(aggr)
                self._pods[pod]["aggr"].append(aggr)

                for c_idx in range((aggr_idx-1)*self._num_connected_core_per_aggr+1, (aggr_idx-1)*self._num_connected_core_per_aggr+self._num_connected_core_per_aggr+1):
                    c_idx = c_idx % self._num_core
                    if c_idx == 0:
                        c_idx += self._num_core
                    core = "c"+str(c_idx)
                    
                    self._store(aggr, core, self._connectivity)
                    # if aggr in self._connectivity.keys():
                    #     self._connectivity[aggr].append(core)
                    # else:
                    #     self._connectivity[aggr] = [core]
                    self._store(aggr, core, self._aggr_core_mapping)

                    self._store(core, aggr, self._connectivity)
                    # if core in self._connectivity.keys():
                    #     self._connectivity[core].append(aggr)
                    # else:
                    #     self._connectivity[core] = [aggr]
                    self._store(core, aggr, self._core_aggr_mapping)

            for edge_idx in range((idx-1)*(self._num_edge_per_pod)+1, (idx-1)*(self._num_edge_per_pod)+self._num_edge_per_pod+1):
                edge = "e"+str(edge_idx)
                self._edges.append(edge)
                self._pods[pod]["edge"].append(edge)

                for aggr in self._pods[pod]["aggr"]:
                    self._store(edge, aggr, self._connectivity)
                    # if edge in self._connectivity.keys():
                    #     self._connectivity[edge].append(aggr)
                    # else:
                    #     self._connectivity[edge] = [aggr]
                    self._store(edge, aggr, self._edge_aggr_mapping)

                    self._store(aggr, edge, self._connectivity)
                    # if aggr in self._connectivity.keys():
                    #     self._connectivity[aggr].append(edge)
                    # else:
                    #     self._connectivity[aggr] = [edge]
                    self._store(aggr, edge, self._aggr_edge_mapping)

    def _generate_hosts(self):
        for edge_idx, edge in enumerate(self._edges):
            edge_idx = int(edge[1:])

            for idx in range(self._num_connected_hosts_per_edge*(edge_idx-1)+1, self._num_connected_hosts_per_edge*(edge_idx-1)+self._num_connected_hosts_per_edge+1):
                host = "h"+str(idx)
                self._hosts.append(host)
                self._store(host, edge, self._connectivity)
                # if host in self._connectivity.keys():
                #     self._connectivity[host].append(edge)
                # else:
                #     self._connectivity[host] = [edge]
                self._store(host, edge, self._host_edge_mapping)

                self._store(edge, host, self._connectivity)
                # if edge in self._connectivity.keys():
                #     self._connectivity[edge].append(host)
                # else:
                #     self._connectivity[edge] = [host]
                self._store(edge, host, self._edge_host_mapping)

    def _store(self, key, item, mapping):
        if key in mapping.keys():
            mapping[key].append(item)
        else:
            mapping[key] = [item]

    def __str__(self) -> str:
        lines = []
        
        total_host_idx = 0
        base_window = self._num_total_hosts // self._num_core
        for pod_idx, pod in enumerate(self._pods):
            # is_first_core = True
            # core_idx = pod_idx // self._num_core
            # core = self._cores[core_idx]
            # core_line += core + "\t"
            # lines.append("########")

            is_first_aggr = True
            for aggr_idx, aggr in enumerate(self._pods[pod]["aggr"]):
                edge = self._pods[pod]["edge"][aggr_idx]
                for host in self._edge_host_mapping[edge]:
                    line = ""

                    core_idx = total_host_idx // base_window
                    core = self._cores[core_idx]
                    if total_host_idx % base_window == 0:
                        line +="#######\t"
                    elif total_host_idx % base_window == 1:
                        line = core + "\t"
                    else:
                        line += "\t"
                    
                    total_host_idx += 1

                    # if is_first_core:
                    #     line += core_line
                    #     is_first_core = False
                    # else:
                    #     line +="#######\t"
                    
                    if is_first_aggr:
                        # print(aggr, edge, end="\t")
                        line += aggr + "\t" + edge + "\t"
                        is_first_aggr = False
                    else:
                        line +="\t\t"
                    line += host + "\t*"

                    lines.append(line)
                
                lines.append("\t--------------------\t*")
                is_first_aggr = True
            lines.append("\t*************************")
            
        return "\n".join(lines)

    def _is_host(self, node):
        if node.startswith('h'):
            return True
        return False

    def _attach_links_for_each_node(self):
        links_info = {}
        for node in self._connectivity.keys():
            links_info[node] = []
            for neighbor in self._connectivity[node]:
                link = "l({}, {})".format(node, neighbor)
                links_info[node].append(link)
        
        return links_info

    def _propagate_routes_from_dst(self, dst):
        PREDEFINED_PATH = ['x', 'y', 'z', 'u', 'v', 'w']
        known_info = {}
        visited_nodes = []
        queueing_nodes = [dst]
        neighbors = [] 
        next_hops = [] # next_hops[i] is the next hop of neighbors[i]
        for node in self._connectivity[dst]:
            neighbors.append(node)
            next_hops.append(dst)
        
        visited_links = {}

        while len(queueing_nodes) > 0:
            print("\n===================================")
            print("queueing_nodes", queueing_nodes)
            print("visited_nodes", visited_nodes)
            next_hop = queueing_nodes.pop(0)
            if next_hop in visited_nodes:
                continue
            print("neighbors", self._connectivity[next_hop])
            # neighbors = [] 
            for neighbor in self._connectivity[next_hop]:
                
                # neighbor = neighbors.pop(0)
                if neighbor in visited_nodes:
                    continue
                else:
                    if not self._is_host(neighbor):
                        queueing_nodes.append(neighbor)
                    else:
                        visited_nodes.append(neighbor)
                print("neighbor", neighbor, "next_hop", next_hop)
                reachabilities = []
                if next_hop == dst:
                    reachability = [neighbor, dst, [neighbor], 1]
                    # str_reachability = str(neighbor) + str(next_hop) + "[{}]".format(neighbor) + str(1)
                    reachabilities.append(reachability)
                else:
                    different_hops = []
                    for next_hop_reachability in known_info[next_hop]:
                        next_hop_hops = next_hop_reachability[-1]
                        if next_hop_hops in different_hops:
                            continue
                        else:
                            different_hops.append(next_hop_hops)
                        # print("neighbor", neighbor, "next_hop", next_hop, "next_hop_hops", next_hop_hops)
                        reachability = [neighbor, dst, [neighbor] + PREDEFINED_PATH[:next_hop_hops], next_hop_hops+1]
                        # str_reachability = str(neighbor) + str(next_hop) + "[{}]".format(", ".join([neighbor] + PREDEFINED_PATH[:next_hop_hops])) + str(next_hop_hops+1)
                        reachabilities.append(reachability)
                    # print("------------------------------------")
                if neighbor in known_info.keys():
                    known_info[neighbor] += reachabilities
                else:
                    known_info[neighbor] = reachabilities

                if neighbor in visited_links.keys():
                    visited_links[neighbor].append(next_hop)
                else:
                    visited_links[neighbor] = [next_hop]

            visited_nodes.append(next_hop)

            # print("visited_links", visited_links)
            
        
        # print("known_info", known_info)
        return known_info#, visited_links

    def _generate_rules_with_path(self, dst):
        
        known_info = self._propagate_routes_from_dst(dst)
        print("known_info", known_info)
        for host in self._hosts:
            if host == dst:
                continue
            self._generate_rules_with_path_for_node(host, dst, known_info)
        
        for edge in self._edges:
            self._generate_rules_with_path_for_node(edge, dst, known_info)

        for aggr in self._aggregrations:
            self._generate_rules_with_path_for_node(aggr, dst, known_info)

        for core in self._cores:
            self._generate_rules_with_path_for_node(core, dst, known_info)

        print("\n".join(self.rules))
                    
    def _generate_rules_with_path_for_node(self, node, dst, known_info):
        PREDEFINED_PATH = ['x', 'y', 'z', 'u', 'v', 'w']
        links_info = self._attach_links_for_each_node()
        has_host = False
        for neighbor in self._connectivity[node]:
            # print("neighbor", neighbor)
            if self._is_host(neighbor):
                if dst in self._connectivity[node]:
                    if has_host:
                        continue
                    
                    has_host = True
                    rule = "R({node}, {dst}, [{node}], {hops}) :- {links}".format(
                        node = node,
                        dst = dst,
                        path = ", ".join(path),
                        hops = 1, 
                        links = ", ".join(links_info[node])
                    )
                    # print("rule", rule)
                    self.rules.append(rule)
                    self.total_atoms += len(links_info[node])
                else:
                    continue # host does not route traffic
            else:
                different_hops = []
                for neighbor_reachability in known_info[neighbor]:
                    dst = neighbor_reachability[1]
                    hops = neighbor_reachability[-1]
                    path = PREDEFINED_PATH[:hops]
                    if hops in different_hops:
                        continue
                    else:
                        different_hops.append(hops)
                    rule = "R({node}, {dst}, [{node}, {path}], {hops_plus}) :- R({neighbor}, {dst}, [{path}], {hops}), {links}".format(
                        node = node,
                        dst = dst,
                        path = ", ".join(path),
                        hops_plus=hops + 1,
                        neighbor=neighbor,
                        hops = hops, 
                        links = ", ".join(links_info[node])
                    )
                    # print("rule", rule)
                    self.rules.append(rule)
                    self.total_atoms += len(links_info[node]) + 1

    def generate_base_rules(self, dst):
    
        links_info = self._attach_links_for_each_node()
        for node in self._connectivity.keys():
            if node == dst:
                continue
            has_host = False
            for neighbor in self._connectivity[node]:
                # print("neighbor", neighbor)
                if self._is_host(neighbor):
                    if dst in self._connectivity[node]:
                        if has_host:
                            continue
                        
                        has_host = True
                        rule = "R({node}, {dst}) :- {links}".format(
                            node = node,
                            dst = dst,
                            links = ", ".join(links_info[node])
                        )
                        # print("rule", rule)
                        self.rules.append(rule)
                        self.total_atoms += len(links_info[node])
                    else:
                        continue # host does not route traffic
                else:
                    rule = "R({node}, {dst}) :- R({neighbor}, {dst}), {links}".format(
                            node = node,
                            dst = dst,
                            neighbor=neighbor,
                            links = ", ".join(links_info[node])
                        )
                    # print("rule", rule)
                    self.rules.append(rule)
                    self.total_atoms += len(links_info[node]) + 1
        
        # print("\n".join(self.rules))
        return "\n".join(self.rules)

if __name__ == '__main__':
    f = Fattree(16)
    print(f)
    # f.generate_base_program("h16")
    # f._propagate_routes_from_dst('h16')
    print(f._cores)
    print(f._aggregrations)
    print(f._edges)
    print(f._hosts)
    # print(f._connectivity)
    f.generate_base_rules('h1')
    print("total nodes:", len(f._cores)+len(f._aggregrations)+len(f._edges)+len(f._hosts))
    print("total number of rules:", len(f.rules))
    print("total_number of atoms:", f.total_atoms)
    
    ############################# toy example, Program for reachability########################################
    # connectivity = {
    #     'h1':['e1'],
    #     'e1':['h1', 'a1', 'a2'],
    #     'a1':['e1', 'e2', 'c1'],
    #     'c1':['a1', 'a2'],
    #     'a2':['c1', 'e1', 'e2'],
    #     'e2':['a1', 'a2', 'h2'],
    #     'h2':['e2']
    # }
    # f = Fattree(2)
    # f._connectivity = connectivity
    # f._generate_base_rules('h2')

    


        
