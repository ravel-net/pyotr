import sys
import os
import pprint
import ipaddress
import subprocess

# os.system('ls -l')

def get_search_word(vlan):
	# Format of search is "*00000". If we have a two digit vlan, it would be "*   00"
	str_to_search = "*"
	for i in range(0,(5 - len(vlan))):
		str_to_search += " "
	str_to_search += vlan
	return str_to_search

def get_file_output(vlan):
	search_word = get_search_word(vlan)
	command = "bash extract_relevant_macs.sh \"" + search_word + "\""
	file_name = "relevant_vlans_" + vlan + ".txt"
	print(command + ">" + file_name)
	os.system(command + ">" + file_name)

def get_mac_addresses(vlan):
	file_name = "relevant_vlans_" + vlan + ".txt"
	f = open(file_name, "r")
	mac_addresses = []
	for x in f:
		if "Processing" in x:
			mac_add = x[11:].strip()
			# print(len(mac_add))
			mac_addresses.append(mac_add)
	return mac_addresses

def get_ips(vlan, mac_add):
	file_name = "relevant_vlans_" + vlan + ".txt"
	f = open(file_name, "r")
	ip_list = []

	for x in f:
		if mac_add in x and "Processing" not in x:
			split_line = x.split()
			ip = split_line[1]
			if ip not in ip_list:
				ip_list.append(ip)
	return ip_list

def longest_prefix_match(ip_dest, ip_prefixes):
	if (len(ip_prefixes) < 1):
		print("ERROR: No prefix found")
		return -1
	longest_prefix = ip_prefixes[0].split("/")[1]
	longest_prefix_id = 0
	i = 0
	for ip_prefix in ip_prefixes:
		prefix = ip_prefixes[i].split("/")[1]
		if prefix > longest_prefix:
			longest_prefix = prefix
			longest_prefix_id = i
		i += 1
	return longest_prefix_id 


# based on longest prefix match
def route(ip_dest, router):
	router += "_route.txt"
	f = open(router, "r")
	lines = f.readlines()[1:]
	ip_prefix_matches = []
	next_hop = []
	interface = []
	for x in lines:
		x = x.split()
		prefix = x[0]
		if ipaddress.ip_address(ip_dest) in ipaddress.ip_network(prefix):
			ip_prefix_matches.append(prefix)
			next_hop.append(x[1])
			if (len(x) > 2): # some routes don't contain information regarding interface. We are currently not using interface so don't need to do extra handling for this
				interface.append(x[2])
			else:
				interface.append("null")
	LPM_index = longest_prefix_match(ip_dest, ip_prefix_matches)
	if (LPM_index == -1):
		return -1, -1
	return next_hop[LPM_index], interface[LPM_index]

def extract_router_mac_addr():
	output = subprocess.check_output("grep \"\-   Router\" *mac_table.txt | tr :* \" \" | awk '{print $1,$3}' | sort --unique", shell=True).decode('ascii').split("\n")
	mac_addresses = {}
	for line in output:
		if ".txt" in line:
			router_file = line.split()[0]
			mac_addr = line.split()[1]
			# if (mac_addr in mac_addresses and mac_addresses[mac_addr] != router_file):
				# print(mac_addr, mac_addresses[mac_addr], router_file)
				# print("Another entry already exists. Might denote an error")
			mac_addresses[mac_addr] = router_file
	return mac_addresses

def find_mac_addr(next_hop, curr_router):
	file_name = curr_router+"_arp_table.txt"
	f = open(file_name, "r")
	lines = f.readlines()[1:]
	for line in lines:
		line = line.split()
		if next_hop == line[1]:
			return line[3]
	print("Error: Could not find mac address corresponding to", next_hop)

def get_route(ip_dest, curr_router, complete_route, mac_router_mapping, mac_mappings):
	# print(curr_router)
	complete_route.append(curr_router)
	next_hop, interface = route(ip_dest, curr_router)
	# print(next_hop)
	if next_hop == "attached" or next_hop == "receive":
		return complete_route
	else:
		mac_addr = find_mac_addr(next_hop, curr_router)
		if mac_addr not in mac_router_mapping:
			print("Error, mac adress does not correspond to any router", mac_addr)
			return []
		new_router = mac_router_mapping[mac_addr][:-14]
		return get_route(ip_dest, new_router, complete_route, mac_router_mapping, mac_mappings)

def find_all_paths_in_vlan(ip_mappings, curr_router, mac_router_mapping, mac_mappings):
	all_routes = []
	for device in ip_mappings:
		for ip_addresses in ip_mappings[device]:
			# print(ip_addresses)
			complete_route = []
			get_route(ip_addresses, curr_router, complete_route, mac_router_mapping, mac_mappings)
			# complete_route.append(ip_addresses)
			# print(complete_route)
			all_routes.append(complete_route)
	print("All routes computed")
	return all_routes

# Check lines in spanning tree to see if it is root
def is_root(lines):
	for line in lines:
		if "is the root" in line:
			return True
	return False

def find_root_router(vlan):
	vlan_to_search = "VLAN"
	for i in range(0, 4-len(vlan)):
		vlan_to_search += "0"
	vlan_to_search += vlan
	files = [f for f in os.listdir('.') if os.path.isfile(f)]
	for file_name in files:
		if "spanning_tree" not in file_name:
			continue
		f = open(file_name, "r")
		lines = f.readlines()
		i = 0		
		for line in lines:
			if vlan_to_search in line and is_root(lines[i:i+10]):
				return file_name[:-18]
			i += 1
	print("No root router found. Exiting")
	return "Error"

# Ideally should just take a vlan and then does everything by itself
vlan = sys.argv[1]
get_file_output(vlan) # Get all the MAC addresses that use 'vlan X' and then search for all ARP entries corresponding to that MAC address to build a list of IP to MAC mapping
ip_mappings = {}
mac_mappings = {}
mac_addresses = get_mac_addresses(vlan)
for mac_add in mac_addresses:
	ip_list = get_ips(vlan, mac_add)
	ip_mappings[mac_add] = ip_list # Create a list of MAC addresses in vlan X and their corresponding IP addresses
	for ip in ip_list:
		mac_mappings[ip] = mac_add



# all starting with the same router, yozb
mac_router_mapping = extract_router_mac_addr()
# curr_router = "yoza_rtr"
curr_router = find_root_router(vlan)

print("Root Router for vlan" + vlan + ": " + curr_router)
all_routes = find_all_paths_in_vlan(ip_mappings, curr_router, mac_router_mapping, mac_mappings)
links = {}
for route in all_routes:
	if len(route) <= 1:
		continue
	print(route)

# ip_dest = "171.67.230.129"
# complete_route = []
# get_route(ip_dest, curr_router, complete_route, mac_router_mapping, mac_mappings)
# print(complete_route)
# pp = pprint.PrettyPrinter(indent=4)
# pp.pprint(mac_router_mapping)

# 1. Find a pair of prefix - nexthop
# Recursively until next-hop is attached:
	# 2. Find for the mac address of the next hop
	# 3. Find the corresponding router
	# 3. Search for original ip in new router table to get next hop