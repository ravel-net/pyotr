import sys
import os
import pprint
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


# Ideally should just take a vlan and then does everything by itself
vlan = sys.argv[1]
# get_file_output(vlan)
ip_mappings = {}
mac_addresses = get_mac_addresses(vlan)
for mac_add in mac_addresses:
	ip_list = get_ips(vlan, mac_add)
	ip_mappings[mac_add] = ip_list

pp = pprint.PrettyPrinter(indent=4)
pp.pprint(ip_mappings)
