reset
set mxtics 3
set mytics 2
#set title"scalability" font 'Gill Sans,24'
set xlabel"composition view" font 'Gill Sans,24'
set ylabel"time (seconds)" rotate by 90 font 'Gill Sans,24'
# set yrange [0:1342177280]
set logscale y 2
# set format y '%.0s%cB'
set style line 80 lt -1 lc rgb "#808080"
set border 3 back linestyle 80
# red = "#FF0000"; green = "#00FF00"; blue = "#0000FF"; skyblue = "#87CEEB";

set boxwidth 0.8
set style fill solid
set xtics font 'Gill Sans,24' #rotate by -30 left
set ytics font 'Gill Sans,21'
set style data histogram
set style histogram clustered gap 1.5
set grid ytics
set tic scale 0
set size 1,1
set size ratio 0.75 #set 0.75 as high as wide 
# set autoscale y
# set ytics 2000 nomirror font 'Gill Sans,24'
# set xrange [-1:3]
# set x2range [0:10]
# set yrange [0:40000]
# set y2range [0:35000]
set key autotitle columnhead
set key horizontal outside right#center
# set key inside top left#center
set key font 'Gill Sans Bold,20'
set key spacing 2
# set key off
set terminal pdfcairo enhanced color lw 3 size 5,4 font 'Gill sans,18'
# set style histogram errorbars linewidth 2
# set errorbars linecolor "#A00000"
# set errorbars linecolor black linewidth 2
# set style histogram errorbars linewidth 1 
# set errorbars linecolor black


set label 1 '4' front at screen 0.31,0.34 font "Gill sans,14"
set label 2 '13' front at screen 0.45,0.41 font "Gill sans,14"
set label 3 '296' front at screen 0.59 ,0.63 font "Gill sans,14"
set label 4 '7240' front at screen 0.72,0.86 font "Gill sans,14"

set label 5 '0.5' front at screen 0.35,0.19 font "Gill sans,14"
set label 6 '5' front at screen 0.51 ,0.34 font "Gill sans,14"
set label 7 '137' front at screen 0.65,0.58 font "Gill sans,14"
set label 8 '3766' front at screen 0.79 ,0.81 font "Gill sans,14"

set xtics ("R12" 0, "R13" 1, "R14" 2, "R15" 3)

set style line 1 lt rgb "#A00000" lw 2 pt 13 ps 0.5
   

set output"bar_trend_chain15.pdf"
# plot"incre_ctable_errorbar.dat" using ($2):xtic(1) notitle fs pattern 5 lt rgb 'black'# with errorbars
### 3 
###
plot "trend15.dat" using ($2) title "split-merge" fs pattern 5 lt rgb 'black', \
                '' using ($3) title "naive" fs pattern 1 lt 1 lc rgb 'black'
               # ""  using ($3):($3+.1):(sprintf("%3.2f",$4)) with labels notitle

            #    '' using ($4):0:0 with labels center offset -2,1 notitle, \
            #    '' using 0:($4):($4) with labels center offset 2,1 notitle
unset output  
