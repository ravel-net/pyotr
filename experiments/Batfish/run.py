from networks.run_config import config
import performance 

for i in range(1, 5):
    for j in range(1+i, 5):
        if i == j:
            continue

        config_topo1 = "t{}_config".format(i)
        config1 = config[config_topo1]

        config_topo2 = "t{}_config".format(j)
        config2 = config[config_topo2]
        print('topo1 = t', i)
        print('topo2 = t', j)
        # no failures
        flow1_no_failure, time_config1_no_failure = performance.no_failure(config1['network_name'], config1['topo_dir'], config1['backup_links'])
        flow2_no_failure, time_config2_no_failure = performance.no_failure(config2['network_name'], config2['topo_dir'], config2['backup_links'])
        print('flow1', flow1_no_failure)
        print('flow2', flow2_no_failure)
        comp1, time_comp1 = performance.compare_flows(flow1_no_failure, flow2_no_failure)

        # one link fails
        flow1_one_link_fails, time_config1_one_link_fails = performance.one_link_fails(config1['network_name'], config1['topo_dir'], config1['one_link_fails']['fail_link'], config1['one_link_fails']['backup_link'])
        flow2_one_link_fails, time_config2_one_link_fails = performance.one_link_fails(config2['network_name'], config2['topo_dir'], config2['one_link_fails']['fail_link'], config2['one_link_fails']['backup_link'])
        print('flow1', flow1_one_link_fails)
        print('flow2', flow2_one_link_fails)
        comp2, time_comp2 = performance.compare_flows(flow1_one_link_fails, flow2_one_link_fails)

        # anther link fails
        flow1_another_link_fails, time_config1_another_link_fails = performance.one_link_fails(config1['network_name'], config1['topo_dir'], config1['another_link_fails']['fail_link'], config1['another_link_fails']['backup_link'])
        flow2_another_link_fails, time_config2_another_link_fails = performance.one_link_fails(config2['network_name'], config2['topo_dir'], config2['another_link_fails']['fail_link'], config2['another_link_fails']['backup_link'])
        print('flow1', flow1_another_link_fails)
        print('flow2', flow2_another_link_fails)
        comp3, time_comp3 = performance.compare_flows(flow1_another_link_fails, flow2_another_link_fails)

        # two links fail
        flow1_two_failures, time_config1_two_failures = performance.two_failures(config1['network_name'], config1['topo_dir'], config1['primary_links'])
        flow2_two_failures, time_config2_two_failures = performance.two_failures(config2['network_name'], config2['topo_dir'], config2['primary_links'])
        print('flow1', flow1_two_failures)
        print('flow2', flow2_two_failures)
        comp4, time_comp4 = performance.compare_flows(flow1_two_failures, flow2_two_failures)

        total_time = time_config1_no_failure + time_config2_no_failure + time_config1_one_link_fails + time_config2_one_link_fails + time_config1_another_link_fails + time_config2_another_link_fails + time_config1_two_failures + time_config2_two_failures + time_comp1 + time_comp2 + time_comp3 + time_comp4
        is_equal = comp1 and comp2 and comp3 and comp4

        f = open("result.txt", "a")
        f.write("topo1|topo2||runtime|is_equal\n")
        f.write("t{}|t{}|{}|{}\n".format(i, j, total_time, is_equal))
        f.close()