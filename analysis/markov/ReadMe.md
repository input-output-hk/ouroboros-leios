# Markov-model simulation for Linear Leios

This Markovian model of Linear Leios computes the probability of EB certifications as RBs are produced.


## Example

The `linleios` program executes the Markov model for EB production in Linear Leios. The protocol parameters and network characteristic are specified as flags on the command line. The program outputs the following information:

- The efficiency of EB production, defined as the expected number of certified EBs per RB, on `/dev/stdout`.
- The "missing probability" resulting from the finite-resolution arithmetic of the computations, on `/dev/stderr`.
- Optionally, a JSON file containing the probabilities of the given number of certified EBs.

```console
$ lake exe linleios --l-header 1 --l-vote 4 --l-diff 5 --committee-size 600 --quorum-fraction 0.80 --p-rb-header-arrives 0.95 --p-eb-validates 0.85 --rb-count 100 --output-file tmp.json                                         

Efficiency: 0.358416
Missing probability: 0.000001

$ json2yaml tmp.json

'61': 0
'60': 0
'59': 1e-06
'58': 2e-06
'57': 5e-06
'56': 1.2e-05
'55': 2.8e-05
'54': 6.2e-05
'53': 0.00013
'52': 0.000263
'51': 0.00051
'50': 0.00095
'49': 0.0017
'48': 0.002924
'47': 0.004832
'46': 0.00767
'45': 0.011695
'44': 0.017128
'43': 0.024091
'42': 0.032532
'41': 0.042169
'40': 0.052455
'39': 0.062599
'38': 0.071642
'37': 0.0786
'36': 0.082632
'35': 0.083203
'34': 0.080197
'33': 0.073954
'32': 0.065202
'31': 0.054925
'30': 0.044172
'29': 0.033887
'28': 0.024777
'27': 0.017248
'26': 0.011419
'25': 0.007182
'24': 0.004285
'23': 0.002422
'22': 0.001295
'21': 0.000654
'20': 0.000311
'19': 0.000139
'18': 5.8e-05
'17': 2.3e-05
'16': 8e-06
'15': 3e-06
'14': 1e-06
'13': 0
'12': 0
```


## Usage

```console
$ lake exe linleios --help

markov [0.0.1]
Run a Markov simulation of Linear Leios.

USAGE:
    markov [FLAGS]

FLAGS:
    -h, --help                         Prints this message.
    --version                          Prints the version.
    --active-slot-coefficient : Float  The active slot coefficient for RBs, in
                                       probability per slot. [Default: `0.05`]
    --l-header : Nat                   L_header protocol parameter, in slots.
                                       [Default: `1`]
    --l-vote : Nat                     L_vote protocol parameter, in slots.
                                       [Default: `4`]
    --l-diff : Nat                     L_diff protocol parameter, in slots.
                                       [Default: `7`]
    --committee-size : Nat             Expected number of voters in the
                                       committee, out of 2500 stakepools total.
                                       [Default: `600`]
    --quorum-fraction : Float          τ protocol parameter, in %/100. [Default:
                                       `0.75`]
    --p-rb-header-arrives : Float      Probability that the RB header arrives
                                       before L_header. [Default: `0.95`]
    --p-eb-validates : Float           Probability that the EB is fully
                                       validated before 3 L_header + L_vote.
                                       [Default: `0.90`]
    --tolerance : Float                Discard states with less than this
                                       probability. [Default: `1e-8`]
    --rb-count : Nat                   Number of RBs to simulate. [Default:
                                       `100`]
    --output-file : String             Path to the JSON output file for the EB
                                       distribution.
```


## Building

```console
$ nix-shell -p lean4 elan

$ lake build
```

The executable program will reside at `.lake/build/bin/linleios`.
