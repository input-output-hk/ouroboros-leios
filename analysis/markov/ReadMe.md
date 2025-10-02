# Markov-model simulation for Linear Leios

This Markovian model of Linear Leios computes the probability of EB certifications as RBs are produced.

## Contents

- [Approach](#approach)
- [Parameters](#parameters)
- [Example](#example)
- [Usage](#usage)
- [Building](#building)


## Approach

(to be written)


## Parameters

| Symbol          | Flag                    | Default | Description                                                                         |
|-----------------|-------------------------|--------:|-------------------------------------------------------------------------------------|
| $L_\text{hdr}$  | `--l-header`            |       1 | Constraint on header diffusion time.                                                |
| $L_\text{vote}$ | `--l-vote`              |       4 | Constraint on voting time.                                                          |
| $L_\text{diff}$ | `--l-diff`              |       7 | Constraint on diffusion time.                                                       |
| $m$             | `--committee-size`      |     600 | Number of members on the voting committee.                                          |
| $\tau$          | `--quorum-fraction`     |    0.75 | Stake-weighted fraction of committee's votes required to produce a certificate.     |
| $p_\text{rb}$   | `--p-rb-header-arrives` |    0.95 | Probability that the RB header arrives at the node before $L_\text{hdr}$ seconds.   |
| $p_\text{eb}$   | `--p-eb-validates`      |    0.90 | Probability that the EB is fully validated before $3 L_\text{hdr} + L_\text{vote}$. |
| $f_\text{adv}$  | `--adversary-fraction`  |    0.00 | Fraction of stake held by adversaries.                                              |


## Example

The `linleios` program executes the Markov model for EB production in Linear Leios. The protocol parameters and network characteristic are specified as flags on the command line. The program outputs the following information:

- The efficiencies, on `/dev/stdout`.
    - RB efficiency: the fraction of possible RBs that were actually produced.
    - EB efficiency: the fraction of possible EBs that were actually produced.
    - Efficiency: the fraction o possible payload bytes that were actual produced.
- The "missing probability" resulting from the finite-resolution arithmetic of the computations, on `/dev/stderr`.
- Optionally, a JSON file containing the probabilities of the given number of certified EBs.

```bash
lake exe linleios \
  --l-header 1 \
  --l-vote 4 \
  --l-diff 5 \
  --committee-size 600 \
  --quorum-fraction 0.80 \
  --p-rb-header-arrives 0.95 \
  --p-eb-validates 0.85 \
  --rb-count 100 \
  --adversary-fraction 0.1 \
  --output-file tmp.json
```

```console
RB efficiency: 0.899977
EB efficiency: 0.290308
Overall efficiency: 0.331256
Missing probability: 0.000028
```

```bash
jq 'to_entries | sort_by(.key | tonumber) | from_entries' tmp.json
```

```console
{
  "8": 0,
  "9": 0.000001,
  "10": 0.000003,
  "11": 0.000012,
  "12": 0.000036,
  "13": 0.0001,
  "14": 0.000251,
  "15": 0.000582,
  "16": 0.001251,
  "17": 0.0025,
  "18": 0.004659,
  "19": 0.008126,
  "20": 0.013297,
  "21": 0.020463,
  "22": 0.02968,
  "23": 0.040648,
  "24": 0.052656,
  "25": 0.064622,
  "26": 0.07524,
  "27": 0.083218,
  "28": 0.087538,
  "29": 0.087673,
  "30": 0.083686,
  "31": 0.076199,
  "32": 0.066239,
  "33": 0.055015,
  "34": 0.043687,
  "35": 0.03319,
  "36": 0.024137,
  "37": 0.016812,
  "38": 0.011221,
  "39": 0.00718,
  "40": 0.004405,
  "41": 0.002593,
  "42": 0.001464,
  "43": 0.000794,
  "44": 0.000413,
  "45": 0.000206,
  "46": 0.000098,
  "47": 0.000045,
  "48": 0.000019,
  "49": 0.000008,
  "50": 0.000003,
  "51": 0.000001,
  "52": 0
}
```

![Example results](example-results.png)


## Usage

```console
$ lake exe linleios --help

markov [0.0.1]
Run a Markov simulation of Linear Leios.

USAGE:
    markov [FLAGS]

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
    --adversary-fraction : Float       Fraction of stake that is adversarial:
                                       the adversary never produces RBs or EBs
                                       and never votes. [Default: `0`]
    --tolerance : Float                Discard states with less than this
                                       probability. [Default: `1e-8`]
    --rb-count : Nat                   Number of potential RBs to simulate.
                                       [Default: `100`]
    --output-file : String             Path to the JSON output file for the EB
                                       distribution.
```


## Building

```console
$ nix-shell -p lean4 elan

$ lake build
```

The executable program will reside at `.lake/build/bin/linleios`.
