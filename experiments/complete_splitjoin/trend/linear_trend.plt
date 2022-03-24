reset
set termoption dash
set autoscale y
set for [i=1:9] linetype i dashtype i
set style line 80 lt -1 lc rgb "#808080"
set style line 81 lt 0  # dashed
set style line 81 lt rgb "#808080"
set grid back linestyle 81
set border 3 back linestyle 80
# set style line 1 lt rgb "#A00000" lw 2 pt 13 ps 0.5
# set style line 2 lt rgb "#00A000" lw 2 pt 6 ps 0.5
# set style line 3 lt rgb "#5060D0" lw 2 pt 2 ps 1
# set style line 4 lt rgb "#EE82EE" lw 2 pt 9 ps 0.5

set style line 1 lt rgb "black" lw 0.5 pt 13 ps 1
set style line 2 lt rgb "black" lw 0.5 pt 6 ps 1
set style line 3 lt rgb "black" lw 0.5 pt 2 ps 1
set style line 4 lt rgb "black" lw 0.5 pt 9 ps 1
set style line 8 lt rgb "black" lw 0.5 pt 1 ps 1
set style line 5 lt rgb "#A00000" lw 2 pt 3 ps 1
set style line 6 lt rgb "#00A000" lw 3 pt 5 ps 1
set style line 7 lt rgb "#5060D0" lw 3 pt 7 ps 1
#set style line 8 lt rgb "#F25900" lw 2 pt 1 ps 1
set style line 11 lt -1 lc rgb "#A00000" lw 3 
set style line 12 lt -1 lc rgb "#00A000" lw 3
set style line 13 lt -1 lc rgb "#5060D0" lw 3
set style line 14 lt 1 lc rgb "#F25900" lw 3

set style line 15 \
    linecolor rgb '#0060ad' \
    linetype 1 linewidth 2 \
    pointtype 2 pointsize 1.5
set style line 16 \
    linecolor rgb '#dd181f' \
    linetype 1 linewidth 2 \
    pointtype 1 pointsize 1.5


set terminal pdfcairo enhanced color lw 3 size 6,8 font 'Gill sans,18'
# set key top left
set key autotitle columnhead
set key right outside #horizontal center
set key font 'Gill Sans Bold,20'
set key spacing 1
# set xtics 0.2 nomirror font 'Gill Sans,24'
# set ytics 0.2 nomirror font 'Gill Sans,24'
set mxtics 3
set mytics 2

set xtics ("R13" 0, "R13" 1, "R14" 2, "R15" 3)
# set yrange [0:1]
# set xrange [0:1] 

# set title 'Is Possible - Recursion'
set title font 'Gill Sans,15'
# # set xrange [0:11]
# # set yrange [0:1]
set xlabel "composition view" font 'Gill Sans,24'
set ylabel "time (seconds)" font 'Gill Sans,24' #offset -1,0,0 

# eval('plot itr_time' )



# plot 'recur_all_101.dat' using 2:1 title 'P1-rc' linestyle 14#smooth unique  
# replot 'recur_all_101.dat' using 3:1 title 'P3-rc' linestyle 4#smooth unique
# replot 'recur_all_101.dat' using 4:1 title 'p4-rc' linestyle 2#smooth unique
# replot 'recur_all_101.dat' using 5:1 title 'ALL-rc' linestyle 3#smooth unique
set output "linear_trend.pdf"

plot 'trend15.dat' using ($2):xtic(1) title 'simp' with linespoints linestyle 15, '' using ($3) title "non-simp" with linespoints linestyle 16
# replot 'recur_all_101.dat' using 3:1 title 'P3-rc' with p linestyle 3 #smooth unique
# replot 'recur_all_101.dat' using 4:1 title 'P4-rc' with p linestyle 2 #smooth unique
# replot 'recur_all_101.dat' using 5:1 title 'all-rc' with p linestyle 4 #smooth unique
# replot 'recur_all_101.dat' using 6:1 title 'all-z3time' with p linestyle 1 #smooth unique

unset output  