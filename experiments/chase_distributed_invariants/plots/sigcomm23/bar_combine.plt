reset
set mxtics 3
set mytics 2
#set title"scalability" font 'Gill Sans,24'
set xlabel"#dependencies" font 'Gill Sans,24'
set ylabel"time (ms)" rotate by 90 font 'Gill Sans,24'
# set yrange [0:1342177280]
#set logscale y 2
# set format y '%.0s%cB'
set style line 80 lt -1 lc rgb "#808080"
set border 3 back linestyle 80
# red = "#FF0000"; green = "#00FF00"; blue = "#0000FF"; skyblue = "#87CEEB";

set boxwidth 1
set style fill solid
set xtics font 'Gill Sans,21' #rotate by -30 left
set ytics font 'Gill Sans,21'
set style data histogram
set style histogram clustered gap 1
set grid ytics
set tic scale 0
set size 1.05,1.05
set size ratio 0.75
#set autoscale y
set xrange [-0.5:2.5]
set yrange [-0:100]
set key autotitle columnhead
set key inside top right#center
set key samplen 1
set key at 1.6, 110
set key font 'Gill Sans,18'
set key spacing 2
set key on
set terminal pdfcairo enhanced color lw 3 size 3.8,3 font 'Gill sans,18'
set style histogram errorbars linewidth 2
# set errorbars linecolor "#A00000"
set errorbars linecolor black linewidth 2
# set style histogram errorbars linewidth 1 
# set errorbars linecolor black

#set label 1 '10' front at screen 0.29,0.145 font "Gill sans,24" tc default
#set label 2 '100' front at screen 0.52,0.145 font "Gill sans,24"
#set label 3 '1000' front at screen 0.76,0.145 font "Gill sans,24"

set xtics ("22" 0, "52" 1, "89" 2)




set style line 1 lt rgb "#A00000" lw 2 pt 13 ps 0.5
   

set output"bar_combine.pdf"
# plot"incre_ctable_errorbar.dat" using ($2):xtic(1) notitle fs pattern 5 lt rgb 'black'# with errorbars
### 3 
###
plot "avg_specific.dat" using ($2):($2-$3):($2+$3) title "optimal" fs pattern 5 lt rgb 'black',\
"avg_random_policy.dat" using ($2):($2-$3):($2+$3) title "random\n(per-policy)" fs pattern 2 lt rgb 'black',\
"avg_random_dependency.dat" using ($2):($2-$3):($2+$3) title "random\n(per-dependency)" fs pattern 1 lt rgb 'black',\
               #""  using ($3):($3+.1):(sprintf("%3.2f",$4)) with labels notitle

            #    '' using ($4):0:0 with labels center offset -2,1 notitle, \
            #    '' using 0:($4):($4) with labels center offset 2,1 notitle
unset output  