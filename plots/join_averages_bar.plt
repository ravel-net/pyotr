set title "Join Performance"
pyotr = "#99ffff"; faure = "#4671d5";
set auto x
set yrange [0:4]
set style data histogram
set style histogram cluster gap 1
set style fill solid border -1
set boxwidth 0.9
set xtic scale 0
set xlabel "Joins"
set ylabel "Query Execution Time (s)"
set terminal png
set output "join_averages.png"
# 2, 3, 4, 5 are the indexes of the columns; 'fc' stands for 'fillcolor'
plot 'join_averages.data' using 2:xtic(1) ti col fc rgb pyotr, '' u 3 ti col fc rgb faure
unset output  
