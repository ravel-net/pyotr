reset
set mxtics 3
set mytics 2
#set title"scalability" font 'Gill Sans,24'
set xlabel"compostion view" font 'Gill Sans,24'
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
set size 1,0.9
set size ratio 0.5
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
set terminal pdfcairo enhanced color lw 3 size 5,8 font 'Gill sans,18'
# set style histogram errorbars linewidth 2
# set errorbars linecolor "#A00000"
# set errorbars linecolor black linewidth 2
# set style histogram errorbars linewidth 1 
# set errorbars linecolor black

#set label 1 '10' front at screen 0.29,0.145 font "Gill sans,24" tc default
#set label 2 '100' front at screen 0.52,0.145 font "Gill sans,24"
#set label 3 '1000' front at screen 0.76,0.145 font "Gill sans,24"
set label 1 '21' front at screen 0.35,0.40 font "Gill sans,14"
set label 2 '592' front at screen 0.52,0.475 font "Gill sans,14"
# set label 3 '39062' front at screen 0.67 ,0.56 font "Gill sans,14"
set label 4 '3' front at screen 0.42,0.36 font "Gill sans,14"
set label 5 '224' front at screen 0.58,0.455 font "Gill sans,14"
set label 6 '21045' front at screen 0.77 ,0.58 font "Gill sans,14"

set xtics ("R12" 0, "R13" 1, "R14" 2)

set style line 1 lt rgb "#A00000" lw 2 pt 13 ps 0.5
   

set output"bar_trend.pdf"
# plot"incre_ctable_errorbar.dat" using ($2):xtic(1) notitle fs pattern 5 lt rgb 'black'# with errorbars
### 3 
###
plot "trend.dat" using ($2) title "simp" fs pattern 5 lt rgb 'black', \
                '' using ($3) title "non-simp" fs pattern 1 lt 1 lc rgb 'black'
               # ""  using ($3):($3+.1):(sprintf("%3.2f",$4)) with labels notitle

            #    '' using ($4):0:0 with labels center offset -2,1 notitle, \
            #    '' using 0:($4):($4) with labels center offset 2,1 notitle
unset output  
