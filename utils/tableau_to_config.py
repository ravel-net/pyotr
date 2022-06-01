import math
import os
import json
from ipaddress import IPv4Address


def getHostFacingIP(router, source_links, destination_links, IP_curr, NEXT_IP_ADDER):
    """
    Given a router in question, returns the ip addresses of all the host facing interfaces
    Parameters:
    ------------
    router : string
        router in question

    source_links : list
        a list of routers connected to sources

    destination_links : list
        a list of routers connected to destinations

    IP_curr : integer
        current IP address being assinged

    NEXT_IP_ADDER : integer
        number to add to get the next IP assignment

    Returns
    ------------
    hosts : list
        list of host facing ip addresses for the router in question
    """
    hostIPs = []
    source_IPs = {}
    dest_IPs = {}
    if router in source_links:
        for hosts in source_links[router]:
            source_IPs[hosts] = IPv4Address(IP_curr)
        hostIPs.append(IPv4Address(IP_curr))
        IP_curr += NEXT_IP_ADDER

    if router in destination_links:
        for hosts in destination_links[router]:
            dest_IPs[hosts] = IPv4Address(IP_curr)
        hostIPs.append(IPv4Address(IP_curr))
        IP_curr += NEXT_IP_ADDER

    return hostIPs, source_IPs, dest_IPs

def getLinks(tableau, sources, destinations):
    """
    Given a tableau, returns the adjacency list of connected routers. Also returns the routers connected to hosts. Note that we assume tableau[i][0] is the source of the ith link while tableau[i][1] is the destination of the ith link

    Parameters:
    ------------
    tableau : list
        a tableau where each tuple represents an interface

    sources : list
        a list of routers connected to sources

    destinations : list
        a list of routers connected to destinations

    Returns
    ------------
    router_links : dictionary
        adjacency list of router connections

    source_links : dictionary
        routers connected to sources

    destination_links : dictionary
        routers connected to destinations
    """

    # Add hosts
    source_links = {}
    destination_links = {}
    sourceNum = 1
    if len(sources) == 0:
        source_router = tableau[0][0]
        source_links[source_router] = ["source"+str(sourceNum)]
        sourceNum += 1
    else:
        for router in sources:
            if router not in source_links:
                source_links[router] = []
            source_links[router].append("source"+str(sourceNum))
            sourceNum += 1    

    destNum = 1
    if len(destinations) == 0:
        dest_router = tableau[-1][1]
        destination_links[dest_router] = ["dest"+str(destNum)]
        destNum += 1
    else:
        for router in destinations:
            if router not in destination_links:
                destination_links[router] = []
            destination_links[router].append("d"+str(destNum))
            destNum += 1

    # Add links
    router_links = {}
    for link in tableau:
        source_router = link[0]
        dest_router = link[1]
        if (source_router == dest_router): # ignoring self links
            continue
        if (source_router not in router_links):
            router_links[source_router] = []
        # if (dest_router not in router_links):
        #     router_links[dest_router] = []
        if dest_router not in router_links[source_router]:
            router_links[source_router].append(dest_router)
        # if source_router not in router_links[dest_router]:
        #     router_links[dest_router].append(source_router)
    router_links[tableau[-1][1]] = []

    return router_links, source_links, destination_links

def getHostNameStart(router):
    return "\n!\nhostname r_{}".format(str(router))

def getInterface(IP, eth_num, subnet):
    return "\n!\ninterface eth{}\n\tip address {}/{}".format(eth_num, str(IP), subnet)

def getOSPFInformation(IPs, subnet, NEXT_IP_ADDER):
    router_address = ""
    for IP in IPs:
        IP_int = int(IP)
        router_id_in_net = IP_int % NEXT_IP_ADDER
        if (router_id_in_net == 1):
            router_address = IP
            break
    OSPF = "\n!\nrouter ospf 1\n\trouter-id {}".format(str(router_address)) 
    for IP in IPs:
        IP_int = int(IP)
        id_in_net = IP_int % NEXT_IP_ADDER
        network_IP = IPv4Address(IP_int - id_in_net)
        OSPF += "\n\tnetwork {}/{} area 0".format(str(network_IP), subnet)

    return OSPF


def tableau_to_config(tableau=[], sources=[], destinations=[], subnet=24):
    """
    Given a tableau representing a forwarding state, converts the state into individual router and switch configurations. If routers connected to source and destinations are not identified, the first and the last router are used as source and destination respectively

    Parameters:
    ------------
    tableau : list
        a tableau where each tuple represents an interface

    sources : list
        a list of routers connected to sources

    destinations : list
        a list of routers connected to destinations

    subnet : integer
        a number between 1-32

    Returns
    ------------
    configs : dictionary
        the configurations (in string format) for each router. e.g. {"r1":"! r1...", ...}

    hosts : dictionary
        contains configuration for hosts in json format. e.g. {"source":"...", "destination":"..."}

    source_summary : dictionary
        contains the summary for each source host. Contains ip_address and name.

    dest_summary : dictionary
        contains the summary for each dest host. Contains ip_address and name.
    """

    NEXT_IP_ADDER = int(math.pow(2,32-subnet))

    router_links, source_links, destination_links = getLinks(tableau, sources, destinations) # returns the links of each router - adjacency list for routers and hosts separately. e.g. {"r1":["r2", "r3"]}, {"r1":["h1","h2"]}. Make sure that each router only occurs once in router_links

    router_interfaces = {}
    # router_acls = {}
    router_host_ips = {}
    source_IPs = {}
    dest_IPs = {}
    IP_curr = int(IPv4Address("1.0.0.1")) # will add 1 for same link at two different routers. 256 otherwise
    for router in router_links:
        if router not in router_interfaces:
            router_interfaces[router] = []
            # router_acls[router] = []
        if router in source_links or router in destination_links: 
            hostIPs, curr_source_IPs, curr_dest_IPs = getHostFacingIP(router, source_links, destination_links, IP_curr, NEXT_IP_ADDER)
            router_interfaces[router] += hostIPs
            if len(curr_source_IPs) > 0:
                source_IPs = curr_source_IPs
            if len(curr_dest_IPs) > 0:
                dest_IPs = curr_dest_IPs
            IP_curr += NEXT_IP_ADDER*len(hostIPs) # multiplying by the number of hosts the router is connected to 

        for router_2 in router_links[router]:
            if router_2 not in router_interfaces: # thus interface hasn't already been added
                router_interfaces[router_2] = []
            router_interfaces[router].append(IPv4Address(IP_curr))
            router_interfaces[router_2].append(IPv4Address(IP_curr+1))
            IP_curr += NEXT_IP_ADDER

    # Get router configs in string form
    configs = {}
    for router in router_interfaces:
        config = ""
        config += getHostNameStart(router)
        for count, IP in enumerate(router_interfaces[router]):
            config += getInterface(IP, count, subnet) # add ACLs too
        config += getOSPFInformation(router_interfaces[router], subnet, NEXT_IP_ADDER)
        # config += getACLInformation(router_acls[router]) #
        configs[router] = config

    # Get host configs in string form. Assuming each host is only connected to a single router
    hosts = {}
    adder  = 19
    for host in source_IPs:
        hosts[host] = getHostJSON(host, source_IPs[host], subnet, adder)
        adder += 5

    adder  = 19
    for host in dest_IPs:
        hosts[host] = getHostJSON(host, dest_IPs[host], subnet, adder)
        adder += 5
    return configs, hosts, source_IPs, dest_IPs

def getHostJSON(host, hostIP, subnet, adder):
    hostJSON = {}
    prefix = str(IPv4Address(int(hostIP+adder)))+"/"+str(subnet)
    gateway = str(hostIP)
    hostInterfaces = {}
    eth0 = {}
    eth0["name"] = "eth0"
    eth0["prefix"] = prefix
    eth0["gateway"] = gateway
    hostInterfaces["eth0"] = eth0
    hostJSON["hostname"] = host
    hostJSON["hostInterfaces"] = hostInterfaces
    return hostJSON

def createDirectories(toponame):
    current_directory = os.getcwd()
    final_directory = os.path.join(current_directory, toponame)
    if not os.path.exists(final_directory):
        os.makedirs(final_directory)
    host_directory = os.path.join(final_directory, r'hosts')
    if not os.path.exists(host_directory):
        os.makedirs(host_directory)
    configs_directory = os.path.join(final_directory, r'configs')
    if not os.path.exists(configs_directory):
        os.makedirs(configs_directory)

def createConfigs(configs, toponame):
    current_directory = os.getcwd()
    final_directory = os.path.join(current_directory, toponame)
    configs_directory = os.path.join(final_directory, r'configs')
    for router in configs:
        f = open("{}/r_{}.cfg".format(configs_directory,router), "w")
        f.write(configs[router])
        f.close()

def createHosts(hosts, toponame):
    current_directory = os.getcwd()
    final_directory = os.path.join(current_directory, toponame)
    host_directory = os.path.join(final_directory, r'hosts')
    for host_name in hosts:
        f = open("{}/{}.json".format(host_directory,host_name), "w")
        f.write(json.dumps(hosts[host_name]))
        f.close()


if __name__ == "__main__":
    T1 = [
        ("1","u",""),
        ("u","2",""),
        ("1","2",""), 
        ("2","v",""), 
        ("v","w",""), 
        ("2","w","")
    ]    

    T2 = [
        ("1","u",""),
        ("u","2",""),
        ("1","v",""), 
        ("2","v",""), 
        ("v","w",""), 
        ("2","w","")
    ]   

    T3 = [
        ("1","2",""),
        ("1","v",""), 
        ("2","v",""), 
        ("v","w",""), 
        ("2","w","")
    ]   

    T4 = [
        ("1","2",""),
        ("1","v",""), 
        ("2","v",""), 
        ("v","w",""), 
        ("2","w","")
    ]   

    all_topos = [T1, T2, T3, T4]
    all_topo_names = ["t1", "t2", "t3", "t4"]

    for i, topo in enumerate(all_topos):
        configs, hosts, source_IPs, dest_IPs = tableau_to_config(topo, sources=["1","1"])
        createDirectories(all_topo_names[i])
        createConfigs(configs, all_topo_names[i])
        # print(hosts)
        createHosts(hosts, all_topo_names[i])