# Markovian simulation of Linear Leios

This Markovian simulation of Linear Leios computes the probability of EB certifications as RBs are produced.


## Contents

- [Model](#model)
- [Parameters](#parameters)
- [Example](#example)
- [Usage](#usage)
- [Building](#building)


## Model

The protocol state is represented by three quantities.

- The number of RBs that have been produced.
- The number of EBs that have been produced.
- Whether an honest RB was produced.
- Whether a certificate is ready for inclusion in the next RB.

Time is tracked in terms of block-forging opportunties instead of in terms of slots.

Transitions occur in several substeps:

1. *Forge RB:* create a new RB.
2. *Certify:* include a certificate in the RB.
3. *Forge EB:* create a new EB.
4. *Vote:* cast votes to reach a quorum.


### Substep 1: Forge RB

The adversarial model assumes that adversaries obstain from producing RBs, EBs, and votes. Let $f_\text{adv}$ be the fraction of stake held by the adversary. Two transitions are possible:

- *Forge a new RB:* probability $1 - f_\text{adv}$.
- *Abstain from forging a new RB:* probability $f_\text{adv}$. 


### Substep 2: Certify

Provided that a quorum of votes have endorsed the EB, the following conditions are required for certifying it in the RB that was just forged.

- *RB spacing:* The previous RB must have been forged at least $3 L_\text{hdr} + L_\text{vote} + L_\text{diff}$ slots previously.
    - The distribution of gaps between RBs follows the negative-binomial distribution.
- *Quorum:* The voting yielded a quorum.
- *Not an adversary:* There is no RB if an adversary is the designated block producer.


### Substep 3: Forge EB

Provided that an honest RB exists, an EB can be forged if the node has received the previous EB and computed the ledger state.

- Because of their membership in the previous vote, a fraction $n_\text{comm} / n_\text{pools}$ of the pools have already updated their ledger state.
- We define $p_\text{late}$ as the probability that the EB has arrived too late to compute the ledger state needed to produce the next EB.


### Substep 4: Vote

Obtaining a successful quorum of votes is distributed according to bernoulli trials where the expected number of successes is the mean committee size and the success probabilities of individual pools accord with the stake distribution. Those success probabilities are modified in several ways:

- *Adversaries do not vote:* probability $f_\text{adv}$.
- *RB header arrives within* $L_\text{hdr}$ *slots:* probability $p_\text{rb}$.
- *EB is fully validated within* $3 L_\text{hdr} + L_\text{vote}$ *slots*: probability $p_\text{eb}$.


## Parameters

| Symbol           | Flag                    | Default | Description                                                                                          |
|------------------|-------------------------|--------:|------------------------------------------------------------------------------------------------------|
| $L_\text{hdr}$   | `--l-header`            |       1 | Constraint on header diffusion time.                                                                 |
| $L_\text{vote}$  | `--l-vote`              |       4 | Constraint on voting time.                                                                           |
| $L_\text{diff}$  | `--l-diff`              |       7 | Constraint on diffusion time.                                                                        |
| $n_\text{comm}$  |                         |    2500 | Number of stakepools (constant).                                                                     |
| $n_\text{pools}$ | `--committee-size`      |     600 | Number of members on the voting committee.                                                           |
| $\tau$           | `--quorum-fraction`     |    0.75 | Stake-weighted fraction of committee's votes required to produce a certificate.                      |
| $p_\text{rb}$    | `--p-rb-header-arrives` |    0.95 | Probability that the RB header arrives at a node before $L_\text{hdr}$ seconds.                      |
| $p_\text{eb}$    | `--p-eb-validates`      |    0.90 | Probability that the EB is fully validated by a node before $3 L_\text{hdr} + L_\text{vote}$.        |
| $p_\text{late}$  | `--p-late-diffusion`    |    0.05 | Probability that an RB producer hasn't yet validated the EB by the time they need to forge their RB. |
| $f_\text{adv}$   | `--adversary-fraction`  |    0.00 | Fraction of stake held by adversaries.                                                               |


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
  --p-eb-validates 0.95 \
  --p-late-diffusion 0.05 \
  --rb-count 100 \
  --adversary-fraction 0.1 \
  --output-file tmp.json
```

```console
RB efficiency: 0.899974
EB efficiency: 0.313049
Overall efficiency: 0.352469
Missing probability: 0.000030
```

```bash
jq 'to_entries | sort_by(.key | tonumber) | from_entries' tmp.json
```

```console
{
  "10": 0,
  "11": 0.000003,
  "12": 0.00001,
  "13": 0.000031,
  "14": 0.000081,
  "15": 0.000196,
  "16": 0.00044,
  "17": 0.000919,
  "18": 0.001799,
  "19": 0.003308,
  "20": 0.005731,
  "21": 0.009381,
  "22": 0.014533,
  "23": 0.021353,
  "24": 0.029805,
  "25": 0.039585,
  "26": 0.050095,
  "27": 0.060484,
  "28": 0.069757,
  "29": 0.07693,
  "30": 0.081208,
  "31": 0.082129,
  "32": 0.079641,
  "33": 0.074106,
  "34": 0.066214,
  "35": 0.056847,
  "36": 0.04692,
  "37": 0.037253,
  "38": 0.028464,
  "39": 0.020939,
  "40": 0.014837,
  "41": 0.010129,
  "42": 0.006664,
  "43": 0.004227,
  "44": 0.002586,
  "45": 0.001525,
  "46": 0.000868,
  "47": 0.000476,
  "48": 0.000252,
  "49": 0.000128,
  "50": 0.000063,
  "51": 0.00003,
  "52": 0.000013,
  "53": 0.000005,
  "54": 0.000002,
  "55": 0.000001,
  "56": 0
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
    --p-late-diffusion : Float         Probability than a RB producer hasn't
                                       validated the previous EB. [Default:
                                       `0.05`]
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
