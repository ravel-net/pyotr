reset
set mxtics 3
set mytics 2
#set title"scalability" font 'Gill Sans,24'
set xlabel"#backup links" font 'Gill Sans,24'
set ylabel"time (ms)" rotate by 90 font 'Gill Sans,24'
# set yrange [0:1342177280]
# set logscale y 4
# set format y '%.0s%cB'
set style line 80 lt -1 lc rgb "#808080"
set border 3 back linestyle 80
# red = "#FF0000"; green = "#00FF00"; blue = "#0000FF"; skyblue = "#87CEEB";

set boxwidth 1
set style fill solid
set xtics font 'Gill Sans,21' #rotate by -15 left
set ytics font 'Gill Sans,21'
set style data histogram
set style histogram clustered gap 1
set grid ytics
set tic scale 0
set size 1,1
set size ratio 0.5 #set 0.75 as high as wide 
# set margin 1
# set autoscale y
# set ytics 2000 nomirror font 'Gill Sans,24'
set xrange [-0.5:2.5]
# set x2range [0:10]
set yrange [0:130]
# set y2range [0:35000]
set key autotitle columnhead
set key horizontal outside right#center
# set key inside top left#center
set key font 'Gill Sans Bold,20'
set key spacing 2
# set key off
set terminal pdfcairo enhanced color lw 3 size 5,3 font 'Gill sans,18'
set style histogram errorbars linewidth 2
# set errorbars linecolor "#A00000"
# set errorbars linecolor black linewidth 2
# set style histogram errorbars linewidth 1 
# set errorbars linecolor black


# set label 1 '1.56' front at screen 0.22,0.35 font "Gill sans,18"
# set label 2 '1.35' front at screen 0.41,0.35 font "Gill sans,18"
# set label 3 '12.35' front at screen 0.65,0.73 font "Gill sans,18"
# set label 4 '14.23' front at screen 0.85,0.80 font "Gill sans,18"
# set label 5 '0.31' front at screen 0.67 ,0.20 font "Gill sans,14"
# set label 6 '0.27' front at screen 0.77,0.18 font "Gill sans,14"

# set label 7 '0.30' front at screen 0.31,0.19 font "Gill sans,10"
# set label 8 '0.28' front at screen 0.41 ,0.18 font "Gill sans,10"
# set label 9 '0.71' front at screen 0.5,0.28 font "Gill sans,14"
# set label 10 '3.6' front at screen 0.61 ,0.45 font "Gill sans,14"
# set label 11 '23.7' front at screen 0.71,0.63 font "Gill sans,14"
# set label 12 '135.43' front at screen 0.80 ,0.81 font "Gill sans,14"

# set xtics ("firewall" 1, "rewrite" 2, "forward" 3, "combination" 4)

set style line 1 lt rgb "#A00000" lw 2 pt 13 ps 0.5
   

set output"bar_vary_pick_num.pdf"
# plot"incre_ctable_errorbar.dat" using ($2):xtic(1) notitle fs pattern 5 lt rgb 'black'# with errorbars
### 3 
###
plot "bar_vary_pick_num.dat" using 2:($2-$3):($2+$3):xtic(1) title "" fs pattern 5 lt rgb 'black' 
   #   '' using ($3) title "naive" fs pattern 1 lt 1 lc rgb 'black' \
   #   '' using ($4) title "naive" fs pattern 2 lt 1 lc rgb 'black'

            #    '' using ($4):0:0 with labels center offset -2,1 notitle, \
            #    '' using 0:($4):($4) with labels center offset 2,1 notitle
unset output  
