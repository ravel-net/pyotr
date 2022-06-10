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
set style line 4 lt rgb "black" lw 0.5 pt 8 ps 1
set style line 8 lt rgb "black" lw 0.5 pt 1 ps 1
set style line 5 lt rgb "#A00000" lw 2 pt 3 ps 1
set style line 6 lt rgb "#00A000" lw 3 pt 5 ps 1
set style line 7 lt rgb "#5060D0" lw 3 pt 7 ps 1
set style line 11 lt -1 lc rgb "#A00000" lw 3 
set style line 12 lt -1 lc rgb "#00A000" lw 3
set style line 13 lt -1 lc rgb "#5060D0" lw 3
set style line 14 lt 1 lc rgb "#F25900" lw 3


set terminal pdfcairo enhanced color lw 3 size 5,3 font 'Gill sans,18'
set termopt enhanced 
# set key top left

set key top left center inside #horizontal center
set key at 0.3, 1
set key font 'Gill Sans,30'
set key spacing 1
#set xtics 5 nomirror font 'Gill Sans,24'
set ytics 0.2 nomirror font 'Gill Sans,24'
set mxtics 1
set mytics 2
set yrange [0:1]
set xrange [10:1100] 

# set logscale x 10
#set format x '10^{%T}'

set title font 'Gill Sans,15'

set xlabel "time (ms)" font 'Gill Sans,24'
set ylabel "probability" font 'Gill Sans,24' #offset -1,0,0 

set xtics font ", 28"
set ytics font ", 28"

# set xtics (" " 0.1, "1" 1, " " 10, "100" 100, " " 1000, "10000" 10000, " " 100000)



set output "cdf_faure.pdf"

plot 'cdf_as_7018.dat' using ($2):($1) title 'Faure' with p linestyle 8,\
# 'cproject_pa.dat' using ($2):($1) title '𝜋' with p linestyle 3,\
# 'cjoin_p2.dat' using ($2):($1) title '⋈_1' with p linestyle 2,\
# 'cjoin_p1_p3.dat' using ($2):($1) title '⋈_2' with p linestyle 4 #smooth unique


unset output  