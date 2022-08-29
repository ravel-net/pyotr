from ipaddress import IPv4Address

class Fattree():

    def __init__(self, k, IP_switch=False):
        self._k = k
        self._num_core_switches = int(( self._k / 2 )**2)
        self._num_pods = int(self._k)
        self._num_aggregation_switches_per_pod = int(self._k / 2)
        self._num_egde_switches_per_pod = int(self._k / 2)
        self._num_hosts = int((self._k)**3 / 4)
        self._core_switches = {}
        self._pods = {}
        self._aggregation_switches = {}
        self._edge_switches = {}
        self._hosts = {}
        self._core_aggregation_links = []
        self._aggregation_edge_links = []
        self._edge_host_links = []
        self._IP_switch=IP_switch
        self._node_index = 0

        self.generate_core_switches()
        self.generate_pods_switches()
        self.generate_hosts()
        self.add_core_aggregation_links()
        self.add_aggregation_edge_links()
        self.add_edge_host_links()

        self._links = self._core_aggregation_links + self._aggregation_edge_links + self._edge_host_links
    

    def generate_core_switches(self):
        if self._IP_switch:
            idx = 0
            for j in range(1, int(self._k/2) + 1):
                for i in range(1, int(self._k/2) + 1):
                    addr = IPv4Address("10.{}.{}.{}".format(self._k, j, i))
                    core_node = {
                        'name': 'c' + str(idx),
                        'addr': addr,
                        'type': 'core'
                    }
                    idx += 1
                    self._core_switches[self._node_index] = core_node
                    self._node_index += 1
        else:
            for idx in range(0, self._num_core_switches):
                core_node = {
                    'name': 'c' + str(idx),
                    'addr': self._node_index,
                    'type': 'core'
                }
                self._core_switches[self._node_index] = core_node
                self._node_index += 1
        return
    
    def generate_pods_switches(self):
        if self._IP_switch:
            for pod in range(0, self._num_pods):
                edge_switches_per_pod = {}
                aggregation_switches_per_pod = {}
                for switch in range(0, self._num_egde_switches_per_pod):
                    addr = IPv4Address("10.{}.{}.1".format(pod, switch))
                    egde_node = {
                        'name': 'e' + str(switch + pod*self._num_egde_switches_per_pod),
                        'addr': addr,
                        'type': 'edge', 
                        'pod_num': pod
                    }
                    edge_switches_per_pod[self._node_index] = egde_node
                    self._edge_switches[self._node_index] = egde_node
                    self._node_index += 1
                for switch in range(0, self._num_aggregation_switches_per_pod):
                    addr = IPv4Address("10.{}.{}.1".format(pod, switch+self._num_egde_switches_per_pod))
                    aggregation_node = {
                        'name': 'a' + str(switch + pod*self._num_aggregation_switches_per_pod),
                        'addr': addr,
                        'type': 'aggregation', 
                        'pod_num': pod
                    }
                    aggregation_switches_per_pod[self._node_index] = aggregation_node
                    self._aggregation_switches[self._node_index] = aggregation_node
                    self._node_index += 1
                self._pods[pod] = {
                    'aggregation': aggregation_switches_per_pod,
                    'edge': edge_switches_per_pod
                }
        else:
            edge_switches_per_pod = {}
            aggregation_switches_per_pod = {}
            for pod in range(0, self._num_pods):
                for switch in range(0, self._num_egde_switches_per_pod):
                    egde_node = {
                        'name': 'e' + str(switch + pod*self._num_egde_switches_per_pod),
                        'addr': self._node_index,
                        'type': 'edge',
                        'pod_num': pod
                    }
                    edge_switches_per_pod[self._node_index] = egde_node
                    self._edge_switches[self._node_index] = egde_node
                    self._node_index += 1
                for switch in range(0, self._num_aggregation_switches_per_pod):
                    aggregation_node = {
                        'name': 'a' + str(switch + pod*self._num_aggregation_switches_per_pod),
                        'addr': self._node_index,
                        'type': 'aggregation',
                        'pod_num': pod
                    }
                    aggregation_switches_per_pod[self._node_index] = aggregation_node
                    self._aggregation_switches[self._node_index] = aggregation_node
                    self._node_index += 1
                self._pods[pod] = {
                    'aggregation': aggregation_switches_per_pod,
                    'edge': edge_switches_per_pod
                }
        return

    def generate_hosts(self):
        host_num = 0
        if self._IP_switch:
            for edge_switch_idx in self._edge_switches.keys():
                edge_switch = self._edge_switches[edge_switch_idx]

                for i in range(1, int(self._k/2)+1):
                    new_addr = int(edge_switch['addr']) + i
                    host = {
                        'name': 'h' + str(host_num),
                        'addr': IPv4Address(new_addr),
                        'type': 'host',
                        'pod_num': edge_switch['pod_num']
                    }
                    host_num += 1
                    self._hosts[self._node_index] = host
                    self._node_index += 1
        else:
            for edge_switch_idx in self._edge_switches.keys():
                edge_switch = self._edge_switches[edge_switch_idx]

                for i in range(1, int(self._k/2)+1):
                    host = {
                        'name': 'h' + str(host_num),
                        'addr': self._node_index,
                        'type': 'host',
                        'pod_num': edge_switch['pod_num']
                    }
                    host_num += 1
                    self._hosts[self._node_index] = host
                    self._node_index += 1
        return
    
    def add_core_aggregation_links(self):
        is_first_half = True
        first_half = list(self._core_switches.keys())[:int(self._k/2)]
        second_half = list(self._core_switches.keys())[int(self._k/2):]
        for aggregation_idx in self._aggregation_switches.keys():
            if is_first_half:
                for core_idx in first_half:
                    self._core_aggregation_links.append((core_idx, aggregation_idx))
                    # self._core_aggregation_links.append((aggregation_idx, core_idx))
            else:
                for core_idx in second_half:
                    self._core_aggregation_links.append((core_idx, aggregation_idx))
                    # self._core_aggregation_links.append((aggregation_idx, core_idx))
            is_first_half = not is_first_half
    
    def add_aggregation_edge_links(self):
        for aggregation_idx in self._aggregation_switches.keys():
            aggregation_pod_num = self._aggregation_switches[aggregation_idx]['pod_num']
            for edge_idx in self._edge_switches.keys():
                edge_pod_num = self._edge_switches[edge_idx]['pod_num']
                if aggregation_pod_num != edge_pod_num:
                    continue

                self._aggregation_edge_links.append((aggregation_idx, edge_idx))
                # self._aggregation_edge_links.append((edge_idx, aggregation_idx))
    
    def add_edge_host_links(self):
        for edge_idx in self._edge_switches.keys():
            edge_pod_num = self._edge_switches[edge_idx]['pod_num']
            edge_addr = int(self._edge_switches[edge_idx]['addr'])
            for host_idx in self._hosts.keys():
                host_pod_num = self._hosts[host_idx]['pod_num']

                if edge_pod_num != host_pod_num:
                    continue
                
                host_addr = int(self._hosts[host_idx]['addr'])

                if host_addr-edge_addr <= int(self._k/2) and host_addr-edge_addr >= 1:
                    self._edge_host_links.append((edge_idx, host_idx))
                    # self._edge_host_links.append((host_idx, edge_idx))
                else:
                    continue


    def __str__(self):
        # print("================ k={} ==================\n".format(self._k))
        # print("----------- Core Switches --------------\n")
        core_str = "".join([
                'id:{} | core name:{} | address:{} | type:{} \n'.format(
                    idx,
                    self._core_switches[idx]['name'], 
                    self._core_switches[idx]['addr'], 
                    self._core_switches[idx]['type']
                    ) for idx in self._core_switches.keys()
            ])
        aggregation_str = "".join([
            'id:{} | aggregation name:{} | address:{} | type:{} | pod_num:{} \n'.format(
                    idx,
                    self._aggregation_switches[idx]['name'], 
                    self._aggregation_switches[idx]['addr'], 
                    self._aggregation_switches[idx]['type'],
                    self._aggregation_switches[idx]['pod_num']
                    ) for idx in self._aggregation_switches.keys()
        ])
        edge_str = "".join([
            'id:{} | edge name:{} | address:{} | type:{} | pod_num:{} \n'.format(
                    idx,
                    self._edge_switches[idx]['name'], 
                    self._edge_switches[idx]['addr'], 
                    self._edge_switches[idx]['type'],
                    self._edge_switches[idx]['pod_num']
                    ) for idx in self._edge_switches.keys()
        ])
        host_str = "".join([
            'id:{} | host name:{} | address:{} | type:{} | pod_num:{} \n'.format(
                    idx,
                    self._hosts[idx]['name'], 
                    self._hosts[idx]['addr'], 
                    self._hosts[idx]['type'],
                    self._hosts[idx]['pod_num']
                    ) for idx in self._hosts.keys()
        ])
        core_aggregation_links_str = "".join([
            '{} <--> {} \n'.format(
                self._core_switches[link[0]]['name'],
                self._aggregation_switches[link[1]]['name'],
            ) for link in self._core_aggregation_links
        ])
        aggregation_edge_links_str = "".join([
            '{} <--> {} \n'.format(
                self._aggregation_switches[link[0]]['name'],
                self._edge_switches[link[1]]['name'],
            ) for link in self._aggregation_edge_links
        ])
        edge_host_links_str = "".join([
            '{} <--> {} \n'.format(
                self._edge_switches[link[0]]['name'],
                self._hosts[link[1]]['name'],
             ) for link in self._edge_host_links
        ])

        str = "================ k={} ==================\n".format(self._k) + \
            "----------- Core Switches --------------\n" + \
            core_str + \
            "-------- Aggregation Switches ----------\n" + \
            aggregation_str + \
            "------------- Edge Switches ------------\n" + \
            edge_str + \
            "----------------- Hosts ----------------\n" + \
            host_str + \
            "------- Core Aggregation links ---------\n" + \
            core_aggregation_links_str + \
            "------- Aggregation Edge links ---------\n" + \
            aggregation_edge_links_str + \
            "----------- Edge Host links ------------\n" + \
            edge_host_links_str
        return str

if __name__ == '__main__':
    fattree = Fattree(k=2, IP_switch=True)
    print(fattree)