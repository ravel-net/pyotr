from calendar import c
import sys
import os
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

from ipaddress import IPv4Network
import json
import psycopg2
from psycopg2.extras import execute_values
import databaseconfig as cfg 

conn = psycopg2.connect(host=cfg.postgres["host"], database="arch", user=cfg.postgres["user"], password=cfg.postgres["password"])
conn.set_session(readonly=False, autocommit=True)
cursor = conn.cursor()

def read_access_list(filename, deny_filename, permit_filename):
    deny_f = open(deny_filename, "a")
    permit_f = open(permit_filename, "a")

    deny_list = []
    permit_list = []
    with open(filename) as d:
        items_list = []
        ac_number = None
        for line in d:
            items = line.split()
            if len(items) == 0:
                continue
            if items[0] == 'access-list':
                if items[1] == ac_number:
                    items_list.append(items)
                else:
                    if len(items_list) != 0:
                        address_dict = process_access_list(items_list)
                        deny_list.extend(address_dict["deny"])
                        permit_list.extend(address_dict["permit"])

                    items_list.clear()
                    ac_number = items[1]
                    items_list.append(items)
    for deny_item in deny_list:
        deny_f.write("{}\n".format(deny_item))
    for permit_item in permit_list:
        permit_f.write("{}\n".format(permit_item))

    deny_f.close()
    permit_f.close()
    print("Read {} Done!".format(filename))

def process_access_list(items_list):
    address_dict = {"permit":[], "deny":[]}
    for items in items_list:
        if items[2].strip() == "remark":
            continue
        info = {}
        if len(items) == 5:
            info = {"source":"{}/{}".format(items[3], process_netmask(items[4]))}
        elif len(items) == 4:
            if items[3] == 'any':
                info["source"] = "0.0.0.0/32"
            else:
                info["source"] = items[3]
        elif len(items) == 6:
            if items[3] == 'ip':
                if items[4] == 'any':
                    info["source"] = "0.0.0.0/32"
                if items[5] == 'any':
                    info["destination"] = "0.0.0.0/32"
        elif len(items) == 7:
            if items[3] == "ip":
                if items[4] == "host":
                    info["source"] = items[5]
                elif items[4] == "any":
                    info["source"] = "0.0.0.0/32"
                else:
                    info["source"] = "{}/{}".format(items[4], process_netmask(items[5]))
                if items[5] == "host":
                    info["destination"] = items[6]
                elif items[6] == "any":
                    info["destination"] = "0.0.0.0/32"
        elif len(items) == 8:
            if items[3] == "ip":
                if items[4] == "host":
                    info["source"] = items[5]
                else:
                    info["source"] = "{}/{}".format(items[4], process_netmask(items[5]))
                if items[6] == "host":
                    info["destination"] = items[7]
                else:
                    info["destination"] = "{}/{}".format(items[6], process_netmask(items[7]))
        
        if len(info) != 0:
            address_dict[items[2].strip()].append(info)
        # print(address_dict)
    return address_dict

def process_netmask(netmask):
    network = "0.0.0.0/{}".format(netmask)
    bits_num = IPv4Network(network).prefixlen
    return bits_num

def read_permit_or_deny_list(filename, tablename):
    stored_list = []
    with open(filename) as d:
        rule_list = []
        for line in d:
            if line not in rule_list:
                rule_list.append(line)
                data = json.loads(line.strip())
                if len(data) == 2:
                    if data["source"] == "0.0.0.0/32" and data["destination"] == "0.0.0.0/32":
                        continue
                    stored_list.append((data["source"], data["destination"]))
    cursor.execute("drop table if exists {}".format(tablename))
    cursor.execute("create table {} (source inet, dest inet)".format(tablename))
    sql = "insert into {} values %s".format(tablename)
    execute_values(cursor, sql, stored_list)
    print("Done!")

        


if __name__ == '__main__':
    # process_netmask("0.3.255.255")
    # config_dirs = [
    #     "../../../stanford_backbone/stanford_bench/bbra_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/bbrb_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/boza_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/bozb_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/coza_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/cozb_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/goza_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/gozb_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/poza_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/pozb_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/roza_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/rozb_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/soza_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/sozb_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/yoza_rtr_config.txt",
    #     "../../../stanford_backbone/stanford_bench/yozb_rtr_config.txt",
    # ]
    # # config_dir = "../../../stanford_backbone/stanford_bench/bbra_rtr_config.txt"
    # for config_dir in config_dirs:
    #     print("current config file:", config_dir)
    #     deny_dir = "./deny_list.txt"
    #     permit_dir = "./permit_list.txt"

    #     read_access_list(config_dir, deny_dir, permit_dir)
    # filename = "./permit_list.txt"
    # tablename = "permit_rules"
    filename = "./deny_list.txt"
    tablename = "deny_rules"
    read_permit_or_deny_list(filename, tablename)

