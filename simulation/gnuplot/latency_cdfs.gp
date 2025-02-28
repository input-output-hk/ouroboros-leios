fixed = 2

if (ARGC < fixed || (ARGC - fixed) % 2 != 0) {
    print (ARGC - fixed)
    print ARGV
    print "Usage: gnuplot -e \"set terminal TRM; set output 'FILE'\" -c script.gp plot_title y_label (data.csv line_title)+"
    print 'Expects data in \"latency, fraction\" format, latency on logscale y_axis.'
    exit
}

plot_title = ARG1
y_label = ARG2
output = ARG3

# Calculate number of datasets
n = (ARGC - fixed) / 2

set title plot_title
set grid
set xlabel "Centile, fraction of sample population"
set xrange [0:1] extend
set logscale y
set ylabel y_label


plot for [i=0:n-1] ARGV[2*i + 1 + fixed] using 2:1 \
    with lines \
    title ARGV[2*i + 2 + fixed]
