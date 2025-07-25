# Data processing tool for simulation traces

The `leios-trace-processor` reads simulation trace log files from the Leios [Haskell](../../../simulation/) or [Rust](../../../sim-rs/) simulator, analyzes them, and formats the results as CSV files.


## Running the tool

```console
$ nix run .#leios-trace-processor -- --help

Process Leios trace logs into CSV file abstracts

Usage: leios-trace-processor [--trace-file FILE] --lifecycle-file FILE

  Leios trace processor

Available options:
  --trace-file FILE        Short Leios simulation trace log file
  --lifecycle-file FILE    Output CSV file for transaction lifecycle data
  -h,--help                Show this help text
```


## Example output

```console
$ nix run .#leios-trace-processor -- --trace-file sim.log --lifecycle-file lifecycle.csv

$ head lifecycle.csv

Kind,Item,Size [B],References,Created [s],To IB [s],To EB [s],To RB [s],In RB [s]
EB,10-node-19,240,0,10.075,NA,NA,NA,NA
EB,100-node-51,336,25,100.075,NA,130.075,129.091,NA
EB,1000-node-27,976,20,1000.075,NA,1090.075,1127.091,NA
EB,1000-node-59,976,19,1000.075,NA,1040.075,1084.091,NA
EB,1010-node-70,1008,39,1010.075,NA,1040.075,1084.091,NA
EB,1020-node-56,1008,24,1020.075,NA,1050.075,1127.091,NA
EB,1020-node-90,1008,8,1020.075,NA,1080.075,1207.091,NA
EB,1020-node-93,1008,5,1020.075,NA,1050.075,1084.091,NA
EB,1040-node-19,944,28,1040.075,NA,1080.075,1104.091,NA
```


## Generic analysis

The R script [generic-analysis.R](generic-analysis.R) creates a generic set of plots from the `cpus.csv`, `lifecycle.csv`, `receipts.csv`, and `resources.csv` files output by `leios-trace-processor`.

Under Nix, simply run `./generic-analysis.R`. Without Nix, run `R --vanilla < generic-analysis.R`.
