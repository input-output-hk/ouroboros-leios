# Instructions

This directory contains the tool `estimator.py` which produces a CDF showing the time needed
to transmit a file over TCP. It models the CUBIC congestion control algorithm slow start and
congestion avoidance phases and accounts for random loss and jitter. The CDF is produced by
a monte carlo simulation. Various relevant input parameters can be configured by editing
'inputs.yaml' file. The syntax of the command is `estimator.py OPTIONAL_INPUT [-p PERCENTILE]`,
where OPTIONAL_INPUT is an input file in yaml format, or otherwise the script defaults to reading
`inputs.yaml`. By default, the output plot's filename is `cdf.svg`.

# Supplementary tools

The `tools` directory contains three more python utilities:
1. plot_chunking.py
2. chunk_compare.py
3. chunking_stability.py
With further description in the `README.md` file.

# Additional documentation

The `notes` subdirectory contains some additional research into the benefit of chunking
downloads, and how it can reduce download time of the aggregate datum. Essentially, it is a means
of avoiding packet loss-induced drawn out tails on the CDF. The notes cover this issue comprehensively.

# References

Algorithm is based on reports in the `papers` subdirectory.
