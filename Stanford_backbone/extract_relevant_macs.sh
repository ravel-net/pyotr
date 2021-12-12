grep "*   22" * | awk '{print $3}' | while read -r line ; do
    echo "Processing $line"
    grep "$line" *arp_table.txt -a
    echo "======="
    echo " "
    # your code goes here
done
