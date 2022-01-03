reset
set termoption dash
set for [i=1:9] linetype i dashtype i
set style line 80 lt -1 lc rgb "#808080"
set style line 81 lt 0  # dashed
set style line 81 lt rgb "#808080"
set grid back linestyle 81
set border 3 back linestyle 80

set style line 1 lt rgb "black" lw 0.5 pt 13 ps 1
set style line 2 lt rgb "black" lw 0.5 pt 6 ps 1
set style line 3 lt rgb "black" lw 0.5 pt 2 ps 1
set style line 8 lt rgb "black" lw 0.5 pt 1 ps 1
set style line 4 lt rgb "black" lw 0.5 pt 8 ps 1
set style line 5 lt rgb "black" lw 0.5 pt 4 ps 1
set style line 6 lt rgb "black" lw 0.5 pt 25 ps 1
set style line 7 lt rgb "black" lw 0.5 pt 7 ps 1
set style line 11 lt -1 lc rgb "#A00000" lw 3 
set style line 12 lt -1 lc rgb "#00A000" lw 3
set style line 13 lt -1 lc rgb "#5060D0" lw 3
set style line 14 lt 1 lc rgb "#F25900" lw 3


set terminal pdfcairo enhanced color lw 3 size 10,6 font 'Gill sans,18'
set termopt enhanced 
set key top right
set key outside
#set key top right center inside #horizontal center
#set key at 3200, 1
#set key font 'Gill Sans,30'
set key spacing 1
#set xtics 5 nomirror font 'Gill Sans,24'
set ytics 0.2 nomirror font 'Gill Sans,24'
set mxtics 1
set mytics 2
set yrange [0:1]
#set xrange [0:1000000] 

set logscale x 10
#set format x '10^{%T}'

set title font 'Gill Sans,15'

set xlabel "time (ms)" font 'Gill Sans,24'
set ylabel "probability" font 'Gill Sans,24' #offset -1,0,0 

set xtics font ", 28"
set ytics font ", 28"

#set xtics (" " 0.1, " " 1, "10" 10, " " 100, "1000" 1000, "" 10000, "100000" 100000, \
#" " 100000, "100000" 100000, " " 1000000)

set xrange [0:2000]

set output "ip_operations.pdf"

plot 'ip_operations.dat' using ($2):($1) title '𝜎_{inet}' with p linestyle 8,\
'ip_operations.dat' using ($3):($1) title '𝜎_{typed-inet}' with p linestyle 3,\
'ip_operations.dat' using ($4):($1) title '𝜎_{text}' with p linestyle 2,\
'ip_operations.dat' using ($5):($1) title '⋈_{inet}' with p linestyle 4,\
'ip_operations.dat' using ($6):($1) title '⋈_{typed-inet}' with p linestyle 5,\
'ip_operations.dat' using ($7):($1) title '⋈_{text}' with p linestyle 6 


unset output  