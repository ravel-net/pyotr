grep "${1}" *mac_table.txt | awk '{print $3}' | while read -r line ; do
    echo "Processing $line"
    grep "$line" *arp_table.txt -a
    echo "======="
    echo " "
    # your code goes here
done

# grep "*   22" *mac_table.txt | awk '{print $3}' | while read -r line ; do

# grep "*   22" * | awk '{print $3}' | while read -r line ; do
#     echo "Processing $line"
#     grep "$line" *spanning_tree.txt -a
#     echo "======="
#     echo " "
#     # your code goes here
# done