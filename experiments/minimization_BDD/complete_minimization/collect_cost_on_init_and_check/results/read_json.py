import json

def read_json_file(filename, output):
    f = open(output, "w")
    with open(filename) as d:
        data = json.load(d)
        f.write("{} {:.4f}\n".format("total", data["total"]))
        f.write("{} {:.4f}\n".format("data", data["data"]))
        f.write("{} {:.4f}\n".format("condition", data["condition"]))
        f.write("{} {:.4f}\n".format("merged", data["merged"]))
        f.write("\n{} {:.4f}\n".format("\ndata details", sum(data["data_details"])))

        condition_keys = [
            "generate_condition",
            "encode",
            "str_to_BDD",
            "operate_BDDs",
            "refine_condition",
            "update_condition"
            ]
        f.write("\ncondition details\n")
        f.write("{}\n".format(" ".join(condition_keys)))
        condition_details = data["condition_details"]
        
        time_condition = [0]*len(condition_keys)
        for item in condition_details:
            for idx, key in enumerate(condition_keys):
                time_condition[idx] += item[key]
        
        time_condition_to_str = []
        for i in range(len(time_condition)):
            time_condition_to_str.append(str(round(time_condition[i], 4)))
        
        f.write("{}\n".format(" ".join(time_condition_to_str)))

        merged_keys = [
            "get_condition",
            "merge_tuples",
            "operate_BDDs",
            "insertion"
        ]
        f.write("\nmerged details\n")
        f.write("{}\n".format(" ".join(merged_keys)))
        merged_details = data["merged_details"]

        time_merged = [0] * len(merged_keys)

        for item in merged_details:
            for idx, key in enumerate(merged_keys):
                time_merged[idx] += item[key]
        
        time_merged_to_str = []
        for i in range(len(time_merged)):
            time_merged_to_str.append(str(round(time_merged[i], 4)))
        f.write("{}\n".format(" ".join(time_merged_to_str)))

        f.close()

def read_components_file_BDD(filename, output, running_times):
    f = open(output, "w")
    with open(filename) as d:
        high_level_keys = ["total", "data", "condition", "merged", "checking"]
        time_high_level =[0] * len(high_level_keys)

        time_data = 0

        condition_keys = [
                "generate_condition",
                "encode",
                "str_to_BDD",
                "operate_BDDs",
                "refine_condition",
                "update_condition"
                ]
        time_condition = [0]*len(condition_keys)

        merged_keys = [
                "get_condition",
                "merge_tuples",
                "operate_BDDs",
                "insertion"
            ]
        time_merged = [0] * len(merged_keys)
        
        for line in d:
            line = line.replace("'", "\"")
            data = json.loads(line.strip())
            
            for idx, key in enumerate(high_level_keys):
                time_high_level[idx] += data[key]

            time_data += sum(data["data_details"])

            condition_details = data["condition_details"]
            for item in condition_details:
                for idx, key in enumerate(condition_keys):
                    time_condition[idx] += item[key]
            
            merged_details = data["merged_details"]
            for item in merged_details:
                for idx, key in enumerate(merged_keys):
                    time_merged[idx] += item[key]

        checking_idx = high_level_keys.index("checking")
        total_idx = high_level_keys.index("total")
        f.write("\nTotal_time_averaged {} {}\n".format(str(time_high_level[total_idx]/running_times), str(time_high_level[checking_idx]/running_times)))
        f.write("\nhigh level\n")
        f.write("|{}|\n".format("|".join(high_level_keys)))
        time_high_level_to_str = []
        for i in range(len(time_high_level)):
            time_high_level_to_str.append(str(round(time_high_level[i], 4)))
        f.write("|{}|\n".format("|".join(time_high_level_to_str)))
    
        f.write("\n|{}|\n|{:.4f}|\n".format("data details", time_data))
        
        f.write("\ncondition details\n")
        f.write("|{}|\n".format("|".join(condition_keys)))
        time_condition_to_str = []
        for i in range(len(time_condition)):
            time_condition_to_str.append(str(round(time_condition[i], 4)))
        f.write("|{}|\n".format("|".join(time_condition_to_str)))
        
        f.write("\nmerged details\n")
        f.write("|{}|\n".format("|".join(merged_keys)))
        time_merged_to_str = []
        for i in range(len(time_merged)):
            time_merged_to_str.append(str(round(time_merged[i], 4)))
        f.write("|{}|\n".format("|".join(time_merged_to_str)))

        f.close()

def read_components_file_Z3(filename, output, runtimes):
    f = open(output, "w")
    with open(filename) as d:
        total_init_nor = 0
        total_checking_nor = 0
        total_init_merged = 0
        total_checking_merged = 0
        # total_update_condition = 0
        # total_insertion = 0
        for line in d:
            line = line.replace("'", "\"")
            print (line)
            data = json.loads(line.strip())
            
            contradiction_details = data["normalization"]["contrdiction"]
            for item in contradiction_details:
                total_init_nor += item["init"]
                total_checking_nor += item["checking"]

            redundancy_details = data["normalization"]["redundancy"]
            for item in redundancy_details:
                total_init_nor += item["init"]
                total_checking_nor += item["checking"]

            check_tauto_details = data["check_tauto"]["check_tauto"]
            for item in check_tauto_details:
                total_init_merged += item["init"]
                total_checking_merged += item["checking"]
            
            # total_insertion += data["check_tauto"]["insertion"]
            # total_update_condition += data["upd_time"]
        
        # f.write("\nUpdate condition\n")
        # f.write("|{:.4f}|\n".format(total_update_condition))

        f.write("\nNormalization\n")
        f.write("|{}|{}|\n".format("initializaiton", "checking"))
        f.write("|{:.4f}|{:.4f}|\n".format(total_init_nor/runtimes, total_checking_nor/runtimes))
        
        f.write("\nMerge tuples\n")
        f.write("|{}|{}|\n".format("initializaiton", "checking"))
        f.write("|{:.4f}|{:.4f}|\n".format(total_init_merged/runtimes, total_checking_merged/runtimes))

        f.write("\nTotal_Time " + str((total_init_merged+total_init_nor)/runtimes) + " " + str((total_checking_merged+total_checking_nor)/runtimes))

        # f.write("\nInsertion\n")
        # f.write("|{:.4f}|\n".format(total_insertion))

        f.close()

if __name__ == '__main__':
    filename = "./runtime_after_refine_translator.json"
    output = "./runtime_after_refine_translator.txt"
    read_json_file(filename, output)