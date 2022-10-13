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

        self._rules = []
    
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
                        c_idx += 4
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

    def generate_base_program(self, dst_host):
        nodes_exist_rule = {}
        # nodes_connection = {}
        edge_connected_dst_host = self._host_edge_mapping[dst_host][0]

        # rule for edge to dst_host
        rule = "R({edge}, {dst}, [{edge}], 1) :- l({edge}, {dst})".format(
                                        edge=edge_connected_dst_host, 
                                        dst=dst_host)
        self._rules.append(rule)
        if edge_connected_dst_host not in nodes_exist_rule:
            nodes_exist_rule[edge_connected_dst_host] = [[edge_connected_dst_host, dst_host, ['x'], 1]]
        
        # self._store(edge_connected_dst_host, dst_host, nodes_connection)
        
        # rules for aggregations to edge
        for aggr in self._edge_aggr_mapping[edge_connected_dst_host]:
            predicates_edge = nodes_exist_rule[edge_connected_dst_host]
            for predicate in predicates_edge:
                link = "l({aggr}, {edge})".format(aggr=aggr, edge=edge_connected_dst_host)
                header_path = copy(predicate[2])
                header_path.insert(0, aggr)
                pred = "R({}, {}, [{}], {})".format(predicate[0], predicate[1], ", ".join(predicate[2]), predicate[3])
                rule = "R({aggr}, {dst}, [{path}], 2) :- {predicate}, {link}".format(
                                            aggr=aggr, 
                                            dst=dst_host, 
                                            path=", ".join(header_path),
                                            predicate=pred,
                                            link=link)
                self._rules.append(rule)

                if aggr not in nodes_exist_rule:
                    nodes_exist_rule[aggr] = []
                nodes_exist_rule[aggr].append([aggr, dst_host, ['y', 'x'], 2])

                # self._store(aggr, edge_connected_dst_host, nodes_connection)

            # rules for core to aggr
            for core in self._aggr_core_mapping[aggr]:
                for predicate in nodes_exist_rule[aggr]:
                    header_path = copy(predicate[2])
                    header_path.insert(0, core)
                    link = "l({core}, {aggr})".format(core=core, aggr=aggr)
                    pred = "R({}, {}, [{}], {})".format(predicate[0], predicate[1], ", ".join(predicate[2]), predicate[3])
                    rule = "R({core}, {dst}, [{path}], 3) :- {predicate}, {link}".format(
                                            core=core, 
                                            dst=dst_host, 
                                            path=", ".join(header_path), 
                                            predicate=pred, 
                                            link=link)
                    
                    self._rules.append(rule)

                    if core not in nodes_exist_rule:
                        nodes_exist_rule[core] = []
                    nodes_exist_rule[core].append([core, dst_host, ['z', 'y', 'x'], 3])
        
        # rules for remaining aggregations
        for aggr in self._aggr_core_mapping:
            if aggr in nodes_exist_rule:
                continue

            links = []
            for core in self._aggr_core_mapping[aggr]:
                link = "l({aggr}, {core})".format(aggr=aggr, core=core)
                links.append(link)

            for core in self._aggr_core_mapping[aggr]:
                for predicate in nodes_exist_rule[core]:
                    header_path = copy(predicate[2])
                    header_path.insert(0, aggr)
                    pred = "R({}, {}, [{}], {})".format(predicate[0], predicate[1], ", ".join(predicate[2]), predicate[3])
                    rule = "R({aggr}, {dst}, [{path}], {hops}) :- {predicate}, {links}".format(
                                            aggr=aggr, 
                                            dst=dst_host, 
                                            path=", ".join(header_path), 
                                            hops=predicate[-1]+1,
                                            predicate=pred, 
                                            links=", ".join(links))
                    self._rules.append(rule)

            if aggr not in nodes_exist_rule:
                nodes_exist_rule[aggr] = []
            nodes_exist_rule[aggr].append([aggr, dst_host, ['u', 'z', 'y', 'x'], 4])

        # rules for remaining edges
        for edge in self._edge_aggr_mapping:
            if edge in nodes_exist_rule:
                continue
            hops = None
            for aggr in self._edge_aggr_mapping[edge]:
                for predicate in nodes_exist_rule[aggr]:
                    header_path = copy(predicate[2])
                    header_path.insert(0, edge)
                    pred = "R({}, {}, [{}], {})".format(predicate[0], predicate[1], ", ".join(predicate[2]), predicate[3])
                    hops = predicate[-1]+1
                    link = "l({edge}, {aggr})".format(edge=edge, aggr=aggr)
                    rule = "R({edge}, {dst}, [{path}], {hops}) :- {predicate}, {link}".format(
                                                edge=edge, 
                                                dst=dst_host, 
                                                path=", ".join(header_path), 
                                                hops=hops,
                                                predicate=pred,
                                                link=link)
                    
                    self._rules.append(rule)
            
            if edge not in nodes_exist_rule:
                nodes_exist_rule[edge] = []
            path = ['v', 'u', 'z', 'y', 'x']
            nodes_exist_rule[edge].append([edge, dst_host, path[0-hops:], hops])
        
        # rules for remaining hosts
        for host in self._host_edge_mapping:
            if host in nodes_exist_rule:
                continue
            if host == dst_host:
                continue
            hops = None
            for edge in self._host_edge_mapping[host]:
                for predicate in nodes_exist_rule[edge]:
                    header_path = copy(predicate[2])
                    header_path.insert(0, host)
                    pred = "R({}, {}, [{}], {})".format(predicate[0], predicate[1], ", ".join(predicate[2]), predicate[3])
                    link = "l({host}, {edge})".format(host=host, edge=edge)
                    hops = predicate[-1]+1
                    rule = "R({host}, {dst}, [{path}], {hops}) :- {predicate}, {link}".format(
                                                host=host, 
                                                dst=dst_host, 
                                                path=", ".join(header_path), 
                                                hops=hops,
                                                predicate=pred,
                                                link=link)

                    self._rules.append(rule)

            if host not in nodes_exist_rule:
                nodes_exist_rule[host] = []
            path = ['v', 'u', 'z', 'y', 'x']
            nodes_exist_rule[host].append([host, dst_host, path[0-hops:], hops])
    
        print("\n".join(self._rules))

        return "\n".join(self._rules)

if __name__ == '__main__':
    f = Fattree(4)
    print(f)
    f.generate_base_program("h16")


        
