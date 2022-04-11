reset
set mxtics 3
set mytics 2
set ylabel"time (seconds)" rotate by 90 font 'Gill Sans,24'
set xlabel"Number of nodes" font 'Gill Sans,24'
#set logscale y 2
# set format y '%.0s%cB'
set style line 80 lt -1 lc rgb "#808080"
set border 3 back linestyle 80
# red = "#FF0000"; green = "#00FF00"; blue = "#0000FF"; skyblue = "#87CEEB";

set boxwidth 1
set style fill solid
set xtics font 'Gill Sans,24' #rotate by -30 left
set ytics font 'Gill Sans,21'
set style data histogram
set style histogram clustered gap 1.5
set grid ytics
set tic scale 0
set size 1,0.9
set size ratio 0.6 #set 0.75 as high as wide 
# set autoscale y
# set ytics 2000 nomirror font 'Gill Sans,24'
set xrange [-0.5:5]
set yrange [0:12]
# set x2range [0:10]
# set yrange [0:40000]
# set y2range [0:35000]
set key autotitle columnhead
set key inside top left#center
set key font 'Gill Sans,15'
set key spacing 1
set key on
# set key off
set terminal pdfcairo enhanced color lw 3 size 5,3 font 'Gill sans,18'

set xtics ("20" 0, "40" 1, "60" 2, "80" 3, "100" 4)

set style line 1 lt rgb "#A00000" lw 2 pt 13 ps 0.5
   

set output"bar_init_time.pdf"
# plot"incre_ctable_errorbar.dat" using ($2):xtic(1) notitle fs pattern 5 lt rgb 'black'# with errorbars
### 3 
###
plot "init_time.dat" using ($2) title "SMT Naive" fs pattern 5 lt rgb 'black', \
                '' using ($3) title "SMT split-merge" fs pattern 1 lt 1 lc rgb 'black', \
                '' using ($4) title "BDD" fs pattern 10 lt 1 lc rgb 'black'
               # ""  using ($3):($3+.1):(sprintf("%3.2f",$4)) with labels notitle

            #    '' using ($4):0:0 with labels center offset -2,1 notitle, \
            #    '' using 0:($4):($4) with labels center offset 2,1 notitle
unset output  