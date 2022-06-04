import math
import os
import json
from ipaddress import IPv4Address

# Tuple location of each attribute
SOURCE_ID = 0
DEST_ID = 1
FIREWALL_ID = 2
CONDITION_ID = 3
EMPTY_FIREWALL = ""

SOURCE_IP = "100.0.2.1"
DEST_IP = "100.0.7.1"
FIREWALL_ACL1 = "\n!\nip access-list extended ACL1\n\tpermit ip 100.0.2.20 any\n\tpermit ip 100.0.2.25 any\n\tdeny ip any any\n"
FIREWALL_ACL2 = "\nip access-list extended ACL2\n\tpermit ip 100.0.2.20 any\n\tdeny ip any any"
FIREWALL_RULES = FIREWALL_ACL1+FIREWALL_ACL2

# NEXT STEPS:
#     Create API in which two tableau are given as input and batfish is run on them to check for homomorphism


def getHostFacingIP(router, source_links, destination_links):
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
        host1 = source_links[router][0]
        host2 = source_links[router][1]
        source_IPs[host1] = IPv4Address(SOURCE_IP)
        source_IPs[host2] = IPv4Address(SOURCE_IP)
        hostIPs.append(IPv4Address(SOURCE_IP))

    if router in destination_links:
        host = destination_links[router][0]
        dest_IPs[host] = IPv4Address(DEST_IP)
        hostIPs.append(IPv4Address(DEST_IP))


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

    firewalls : dictionary
        firewalls connected to each source in router_links
    """


    # Add links
    router_links = {}
    firewalls = {}
    for link in tableau:
        source_router = link[SOURCE_ID]
        dest_router = link[DEST_ID]
        firewall = link[FIREWALL_ID] 

        if (source_router not in firewalls):
            firewalls[source_router] = []

        firewalls[source_router].append(firewall)

        if (source_router == dest_router): # ignoring self links
            continue
        if (source_router not in router_links):
            router_links[source_router] = []
        if dest_router not in router_links[source_router]:
            router_links[source_router].append(dest_router)

    router_links[tableau[-1][1]] = [] # Since final node never appears in source


    # Add hosts
    source_links = {}
    destination_links = {}
    sourceNum = 1
    if len(sources) == 0:
        source_router = tableau[0][SOURCE_ID]
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
        dest_router = tableau[-1][DEST_ID]
        destination_links[dest_router] = ["dest"+str(destNum)]
        destNum += 1
    else:
        for router in destinations:
            if router not in destination_links:
                destination_links[router] = []
            destination_links[router].append("dest"+str(destNum))
            destNum += 1

    return router_links, source_links, destination_links, firewalls

def getHostNameStart(router):
    return "\n!\nhostname r_{}".format(str(router))

def getInterface(IP, eth_num, subnet, firewall):
    interface_info = "\n!\ninterface eth{}\n\tip address {}/{}".format(eth_num, str(IP), subnet) 
    if firewall != EMPTY_FIREWALL:
        interface_info += "\n\tip access-group ACL{} out".format(firewall)
    return interface_info

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

def getLinkFailureConfig(primary_links, backup_links, network_name):
    linkfailJSON = {}
    topo_dir = './networks/{}'.format(network_name)
    one_link_fails = {'fail_link':primary_links[0], 'backup_link':backup_links[1]}
    another_link_fails = {'fail_link':primary_links[1], 'backup_link':backup_links[0]}

    linkfailJSON["{}_config".format(network_name)] = {
        'network_name': network_name,
        'topo_dir': topo_dir,
        'backup_links': backup_links,
        'primary_links': primary_links,
        'one_link_fails': one_link_fails,
        'another_link_fails': another_link_fails
    }

    return linkfailJSON

def getEthernetLinkID(link, ethernet_table):
    """
    Given an ethernet table and a link, returns the location of the link in the ethernet table

    Parameters:
    ------------
    link : tuple
        a tuple from tableau

    ethernet_table : list
        tableau with ethernet table. Each tuple is of the form: (source_router, dest_router, ethernet_source, ethernet_dest)

    Returns
    ------------
    link_id : int
        the id of the corresponding link in the ethernet table
    """
    for id, eth_link in enumerate(ethernet_table):
        if eth_link[SOURCE_ID] == link[SOURCE_ID] and eth_link[DEST_ID] == link[DEST_ID]:
            return id

def getPrimaryBackupLinks(tableau, ethernet_table):
    """
    Given a tableau representing a forwarding state and the same tableau with ethernet information, return the set of primary and the corresponding backup links

    Parameters:
    ------------
    tableau : list
        a tableau where each tuple represents an interface

    ethernet_table : list
        tableau with ethernet table. Each tuple is of the form: (source_router, dest_router, ethernet_source, ethernet_dest)

    Returns
    ------------
    primary_links : list
        list of primary links. Each tuple in list is a tuple that contains a router name and the corresponding id. e.g [{router_1: ethernet_id_1, router_2: ethernet_id_2}, ...]

    backup_links : list
        list of backup links. Each tuple in list is a tuple that contains a router name and the corresponding id. e.g [{router_1: ethernet_id_1, router_2: ethernet_id_2}, ...]
    """
    if len(tableau) != len(ethernet_table):
        print("Length of tableau and ethernet table is not equal. Exiting")
        exit()

    primary_links = []
    backup_links = []
    for link in tableau:
        condition = link[CONDITION_ID]
        if len(condition) == 0:
            continue
        link_name = condition.split("==")[0].strip()
        link_status = condition.split("==")[1].strip()
        primary_link_id = getEthernetLinkID(link, ethernet_table)
        if link_status == "1":
            for link2 in tableau: # find backup pair. This is done over here to ensure that the order of backup and primary links correspond to each other
                condition2 = link2[CONDITION_ID]
                if len(condition2) == 0:
                    continue
                link_name2 = condition2.split("==")[0].strip()
                link_status2 = condition2.split("==")[1].strip()
                if (link_name2 == link_name) and link_status2 == "0":
                    backup_link_id = getEthernetLinkID(link2, ethernet_table)
                    primary_links.append( {link[SOURCE_ID]: ethernet_table[primary_link_id][2], link[DEST_ID]: ethernet_table[primary_link_id][3]} )
                    backup_links.append( {link2[SOURCE_ID]: ethernet_table[backup_link_id][2], link2[DEST_ID]: ethernet_table[backup_link_id][3]} )
    return primary_links, backup_links

def getFirewallMapping(tableau):
    """
    Given a tableau representing a forwarding state, converts the state into individual router and switch configurations. If routers connected to source and destinations are not identified, the first and the last router are used as source and destination respectively

    Parameters:
    ------------
    tableau : list
        a tableau where each tuple represents an interface

    Returns
    ------------
    firwall_mapping : dictionary
        Maps firewall in tableau to either ACL 1 or ACL 2 
    """
    firewall_mapping = {}
    firewall_num = 1
    for link in tableau:
        firewall_ACL = link[FIREWALL_ID]
        if len(firewall_ACL) == 0:
            continue
        elif (firewall_ACL in firewall_mapping):
            continue
        else:
            firewall_mapping[firewall_ACL] = str(firewall_num)
            firewall_num += 1
    return firewall_mapping


def tableau_to_config(tableau=[], sources=[], destinations=[], subnet=24, network_name="t1"):
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

    network_name : string
        name of the network

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

    firewall_mapping = getFirewallMapping(tableau) # maps firewalls to ACL1 and ACL2
    print(firewall_mapping)
    router_links, source_links, destination_links, firewalls = getLinks(tableau, sources, destinations) # returns the links of each router - adjacency list for routers and hosts separately. e.g. {"r1":["r2", "r3"]}, {"r1":["h1","h2"]}. Make sure that each router only occurs once in router_links


    router_interfaces = {}
    ethernet_table = []
    router_host_ips = {}
    source_IPs = {}
    dest_IPs = {}
    firewalls_both_sides = {}
    IP_curr = int(IPv4Address("1.0.0.1")) # will add 1 for same link at two different routers. 256 otherwise
    for router in router_links:
        if router not in router_interfaces:
            router_interfaces[router] = []
            firewalls_both_sides[router] = []

        for count, router_2 in enumerate(router_links[router]):
            if router_2 not in router_interfaces: # thus interface hasn't already been added
                router_interfaces[router_2] = []
                firewalls_both_sides[router_2] = []
            router_interfaces[router].append(IPv4Address(IP_curr))
            router_interfaces[router_2].append(IPv4Address(IP_curr+1))
            ethernet_table.append((router, router_2, len(router_interfaces[router])-1, len(router_interfaces[router_2])-1)) # source_router, dest_router, ethernet_source, ethernet_dest

            firewalls_both_sides[router].append(firewalls[router][count])
            firewalls_both_sides[router_2].append(EMPTY_FIREWALL)
            # if firewall, then add firewall. Else add emptiness
            IP_curr += NEXT_IP_ADDER

        if router in source_links or router in destination_links: 
            hostIPs, curr_source_IPs, curr_dest_IPs = getHostFacingIP(router, source_links, destination_links)
            for hostIP in hostIPs:
                router_interfaces[router].append(hostIP)
                firewalls_both_sides[router].append(EMPTY_FIREWALL) # denotes empty entry in firewall

            if len(curr_source_IPs) > 0:
                source_IPs = curr_source_IPs
            if len(curr_dest_IPs) > 0:
                dest_IPs = curr_dest_IPs
            # IP_curr += NEXT_IP_ADDER*len(hostIPs) # multiplying by the number of hosts the router is connected to 

    primary_links, backup_links = getPrimaryBackupLinks(tableau, ethernet_table)
    # Get router configs in string form
    configs = {}
    for router in router_interfaces:
        config = ""
        config += getHostNameStart(router)
        for ethernet_ID, IP in enumerate(router_interfaces[router]):
            ACL_num = ''
            curr_firewall_entry = firewalls_both_sides[router][ethernet_ID]
            if curr_firewall_entry != '':
                ACL_num = firewall_mapping[curr_firewall_entry]
            config += getInterface(IP, ethernet_ID, subnet, ACL_num) # add ACLs too
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

    link_failure_config = getLinkFailureConfig(primary_links, backup_links, network_name)
    print(json.dumps(link_failure_config))
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

def createConfigs(configs, toponame, firewall_rules):
    current_directory = os.getcwd()
    final_directory = os.path.join(current_directory, toponame)
    configs_directory = os.path.join(final_directory, r'configs')
    for router in configs:
        f = open("{}/r_{}.cfg".format(configs_directory,router), "w")
        f.write(configs[router])
        f.write(firewall_rules)
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
        ("1","u","123", "l1u == 1"),
        ("u","2","", ""),
        ("1","2","1321", "l1u == 0"), 
        ("2","v","123", "l2v == 1"), 
        ("v","w","", ""), 
        ("2","w","1321", "l2v == 0")
    ]    

    T2 = [
        ("1","u","1", "x == 1"),
        ("u","2","", ""),
        ("1","v","1", "x == 0"), 
        ("2","v","2", "y == 1"), 
        ("v","w","", ""), 
        ("2","w","2", "y == 0")
    ]   

    T3 = [
        ("1","2","1", "x == 1"),
        ("1","v","1", "x == 0"), 
        ("2","v","2", "y == 1"), 
        ("v","w","", ""), 
        ("2","w","2", "y == 0")
    ]   

    T4 = [
        ("1","2","1", "x == 1"),
        ("1","v","1", "x == 0"), 
        ("2","v","", "y == 1"), 
        ("v","w","2", ""), 
        ("2","w","2", "y == 0")
    ]   

    all_topos = [T1, T2, T3, T4]
    all_topo_names = ["t1", "t2", "t3", "t4"]

    for i, topo in enumerate(all_topos):
        configs, hosts, source_IPs, dest_IPs = tableau_to_config(topo, sources=["1","1"], network_name=all_topo_names[i])
        createDirectories(all_topo_names[i])
        createConfigs(configs, all_topo_names[i], FIREWALL_RULES)
        # print(hosts)
        createHosts(hosts, all_topo_names[i])