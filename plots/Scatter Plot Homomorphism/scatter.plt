reset
set mxtics 1
set mytics 2
set ytics 5
set xtics 5
#set title"scalability" font 'Gill Sans,24'
set xlabel"Size of Closure Group" font 'Gill Sans,24'
set ylabel"time (ms)" rotate by 90 font 'Gill Sans,24'
# set yrange [0:1342177280]
#set logscale y 2
# set format y '%.0s%cB'
set style line 80 lt -1 lc rgb "#808080"
set border 3 back linestyle 80
red = "#FF0000"; green = "#00FF00"; blue = "#0000FF"; skyblue = "#87CEEB";

set boxwidth 1.5
set style fill solid
set xtics font 'Gill Sans,28' #rotate by -30 left
set ytics font 'Gill Sans,24'
# set style data histogram
# set style histogram clustered gap 1.5
set grid ytics
set tic scale 0
set size 1,0.9
set size ratio 0.6
#set autoscale y
#set xrange [0:36]
# set yrange [-0:0.02]
set key autotitle columnhead
set key inside top left#center
set key font 'Gill Sans,24'
set key spacing 2
set key off
set term pdf
set terminal pdfcairo enhanced color lw 3 size 5,3 font 'Gill sans,18'
# set style histogram errorbars linewidth 2
# set errorbars linecolor "#A00000"
# set errorbars linecolor black linewidth 2
# set style histogram errorbars linewidth 1 
# set errorbars linecolor black

#set label 1 '10' front at screen 0.29,0.145 font "Gill sans,24" tc default
#set label 2 '100' front at screen 0.52,0.145 font "Gill sans,24"
#set label 3 '1000' front at screen 0.76,0.145 font "Gill sans,24"

# set xtics (" " -0.5, "4755" 0, " " 0.5, "3356" 1, " " 1.5, "7018" 2, " " 2.5, "2914" 3, " " 3.5)




#set style line 1 lt rgb "#A00000" lw 2 pt 13 ps 0.5
set style line 1 lt rgb 'black' lw 2 pt 13 ps 0.5
   

set output "scatter_closure_groups.pdf"
plot 'scatter2.dat' with points pt 2 lt 'black'
# plot"incre_ctable_errorbar.dat" using ($2):xtic(1) notitle fs pattern 5 lt rgb 'black'# with errorbars
### 3 
###
# plot "bar_rocketfuel_homomorphism.dat" using ($2):($2-$3):($2+$3):xtic($1) title " " fs pattern 10 lt rgb 'black'
               #""  using ($3):($3+.1):(sprintf("%3.2f",$4)) with labels notitle

            #    '' using ($4):0:0 with labels center offset -2,1 notitle, \
            #    '' using 0:($4):($4) with labels center offset 2,1 notitle
unset output  