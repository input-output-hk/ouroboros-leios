# Leios technical feasibility: a measured assessment of the pipeline on the public testnet and the benchmarking cluster

Ezequiel Postan, ezequiel.postan@iohk.io

Build of 2026-11-12, from commit 49da0561. Sections in this build: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, Appendix A.

## Contents

- 0. Summary
- 1. Mainnet baseline and targets
- 2. What is assessed and what to expect
- 3. Populations and instruments
- 4. Results by parameter set
- 5. Leios on Praos
- 6. Cross-cutting explanations
- 7. Models against measurements: DeltaQ and the CIP cost model
- 8. What binds certification, and what would move it
- 9. A change to the voting loop, and where it has run
- Appendix A. How each quantity was measured

# 0. Summary

This report measures the Leios pipeline on the public testnet and on
the benchmarking cluster at three parameter sets, named by the
reference list an endorser block may carry and the bytes of its
closure. Every transaction measured is a value transfer without
scripts. The standard is the proposal's: a parameter set confirmed
feasible, with a credible path upward.

| parameter set | ceiling, kB/s | measured, kB/s | certified of the eligible EBs | verdict |
|---|---:|---:|---:|---|
| 40 kB / 260 kB, cluster and testnet | 8.9 | 7.5 and 7.2 | 99 % and 97 % | confirmed |
| 100 kB / 1 MB, cluster | 27.9 | 12.2 and 15.5; 26.6 on the latest build | 69 % and 52 %; 99 % on the latest build | confirmed on the cluster on the latest build at the time of this report; the testnet at this set is the next stage |
| 308 kB / 2 MB, testnet | 53.5 | 12.0 and 22.0 | 49 % and 45 % | not confirmed as measured; not measured on the latest build, for which sections 8 and 9 give evidence of feasibility on the validation side |

Table 0.1. The three sets against their parameter ceiling, the rate
with every EB full and certified; two windows or runs per set (Tables
1.4, 4.1, 4.3 and 4.5), and for the 100 kB / 1 MB set a third run on
the latest build at the time of this report (Table 9.3). An EB is
eligible when the next RB leaves it the certification gap; on the 2 MB
set the EBs were at 0.6 of the cap on average.

Leios is confirmed at twice the Praos ceiling on both populations. It
is confirmed at six times on the cluster on the latest build at the
time of this report; the testnet at that set is the next stage. The
ten-times set depends on that build and on the closure's diffusion.
The ten-times line needs a closure of about 1.7 MB, smaller than the
2 MB closures measured here.

**The confirmed set.** At 40 kB / 260 kB, twice the Praos ceiling, every
stage of the pipeline is inside its budget on both populations and the
voting stage loses nothing.

**What bound above it, and what the latest build changes.** On the
build of section 4, one stage bound certification above the confirmed
set: closure validation at the voting stage. The latest build removes
most of its cost. Where that build is measured, on a testnet host over
three days and on the cluster at 100 kB / 1 MB, validation is no
longer the limit: the cluster run at 100 kB / 1 MB certifies 99 % of
its eligible EBs where the build of section 4 certified 52 %
(section 9).

Section 5 measures a cost to Praos on the build of section 4, a slower
forge path and a higher fork rate. The latest build removes it where
it is measured, on the cluster at 100 kB / 1 MB (section 9.3).

**What is not yet measured on the latest build.** At the time of this
report the latest build runs on one testnet host, and no cluster run
exists at the 308 kB / 2 MB set.

For those, section 8 estimates what the latest build would do. It
reprices the votes measured on the build of section 4 at the latest
build's validation cost. On the testnet's 2 MB windows that repricing
takes validation out of the causes of late votes at every host class
and EB size. The same repricing was made for the 100 kB / 1 MB cluster
run before that run existed on the latest build: it predicted 97 %
certification, and the run gave 99 %.

What stays late on the testnet, as recorded on the build of section 4,
is the closure's arrival on its topology, a fifth of the votes on the
largest EBs. The changes that
would move it, in closure forwarding, egress scheduling and the
upstream peer count, are not measured in this report (section 8.4).

**What the measurements do not cover.** The transaction mix of mainnet,
with scripts: no window or run in this report exercised it, so the
comparison with the targets of section 1 is in bytes per
second at the measured transactions, not at mainnet's mix. The
validation margin the latest build opens is room for that computation;
how much of it is a measurement still to make.

The latest build at the committee's scale: on the testnet it has run
on one host, and on the cluster on every node of one run.

Further experiments on the latest build are scheduled. This report
makes no claim about the points they would measure.

# 1. Mainnet baseline and targets

Before any Leios measurement is read, two things have to be fixed: what
Praos delivers on mainnet today, both on paper and under real congestion,
and what the targets for Leios are once they are expressed in the same unit.
The results in the later sections are read against the numbers established
here.

## 1.1 Praos on paper and on the chain

A Praos block is limited to 90,112 bytes, and the chain produces one block
every 20 seconds on average, since the active slot coefficient f is 0.05. The
protocol therefore carries at most 4.5 kB/s. The chain comes close to this
rate in practice. Chain density, the share of the expected blocks that
actually extend the chain, lies between 97 and 99 % in every period
considered below except one; the remainder is made of slots lost to
propagation and to competing blocks. The parameter ceiling is thus nearly
the real one, and it is the quantity of which every Leios parameter set is a
multiple.

What the chain carries under load is a different quantity. Table 1.1 lists
the six periods of highest load in the chain's history for which the data
was pulled, taken from block headers and epoch parameters (Koios, fetched on
2026-10-21), each measured against the block limit of its own epoch. A block
is counted as full at 90 % of the limit, since a block stops when the next
transaction does not fit and so never reaches the limit exactly.

| period (UTC) | event | hours | RBs | spacing; chain density | carried, kB/s | fullness, mean / median | RBs full | tx per RB | bytes per tx |
|---|---|---|---|---|---|---|---|---|---|
| 2022-01-21 00:00 to 01-23 06:00 | SundaeSwap launch; pre-Vasil, scripts inline | 54 | 9,114 | 21.3 s; 93.8 % | 3.25 | 94 % / 96 % | 85 % | 45 | 1,549 |
| 2023-12-08 06:00 to 12-09 18:00 | memecoin minting wave | 36 | 6,307 | 20.5 s; 97.4 % | 3.43 | 78 % / 92 % | 60 % | 29 | 2,396 |
| 2024-09-05 12:00 to 09-06 00:00 | Snek.fun launch | 12 | 2,094 | 20.6 s; 96.9 % | 2.49 | 57 % / 55 % | 31 % | 51 | 1,011 |
| 2024-12-02 18:00 to 12-03 00:00 | bull-run activity, the busiest 6 h of epoch 525 | 6 | 1,063 | 20.3 s; 98.6 % | 2.86 | 64 % / 80 % | 42 % | 43 | 1,344 |
| 2026-10-08 06:00 to 18:00 | Hosky spam campaign (synthetic mix) | 12 | 2,107 | 20.5 s; 97.6 % | 3.40 | 77 % / 96 % | 62 % | 151 | 461 |
| 2026-10-11 to 10-16, epoch 661 | normal operation | 120 | 21,385 | 20.2 s; 99.0 % | 0.51 | 12 % / 6 % | 2 % | 12 | 877 |

Table 1.1. Praos under load on mainnet. Carried is block bytes over
wall-clock time, fullness is block bytes over the epoch's block limit, and
RBs full is the share of blocks at 90 % of the limit or more. The table is
regenerated by `scripts/mainnet_windows.sh` from the data set listed in
DATA.md.

Three observations from this table are used throughout the report. The
first is that mainnet has been saturated for days only once. The SundaeSwap
launch in January 2022 ran at a mean fullness of 94 % for 54 hours. Every
episode of congestion since the introduction of reference scripts (Vasil,
September 2022) has lasted hours rather than days, and even at its peak has
left between 20 and 45 % of the available bytes unused: the median block is
full, at 92 to 96 %, while the mean is only 57 to 78 %, because full blocks
alternate with near-empty ones as the mempool drains faster than it refills.
The best sustained rate since Vasil is 3.4 kB/s, three quarters of the
ceiling. This is what load looks like on mainnet, and it is the reason the
report measures Leios in load windows and against its caps rather than per
day: a daily average mixes the congested hours with the quiet ones and
describes neither.

The second observation is that transaction size is a range rather than a
constant. The mean bytes per transaction run from 461 B under the spam
campaign, through 877 B in normal operation and 1,000 to 1,550 B at the two
DEX launches, to 2,396 B in the metadata-heavy minting wave; the CIP-164
convention of 1,500 B sits in the middle of this range. A throughput target
stated as a transaction count therefore has no meaning without a declared
transaction size. The report states every target in bytes per second and
converts it to transactions per second at three sizes.

The third is that chain density is a second, smaller loss: one percent in
normal operation, 2.5 to 3 % in the congested periods, and 6 % in the one
sustained full-block period. Leios keeps the Praos block at its present size,
but a certifying block carries more work at adoption, and section 5 covers
what that does to this term.

## 1.2 The targets

The throughput targets against which this report reads its measurements
are the ones set by the two documents that commissioned Leios, the treasury
proposal and CIP-164, and they are taken here as those documents state
them. The treasury proposal ("IO: Consensus Initiative") sets no unit for
capacity. It commits to 27 million transactions a month by 2030, from about
800,000 today, and asks for at least six times the current capacity with 50
to 70 % headroom; elsewhere it states that Leios delivers ten times or more.
Its implicit measure of current capacity is a count, about three
transactions per second, which is the Praos ceiling at a transaction of
1,500 B. The report reads the proposal's multipliers as counts at the
mainnet size mix, so that six and ten times the current capacity are 27 and
45 kB/s respectively.

CIP-164 gives 50 transactions per second as the sustained throughput beyond
which fees offset diminishing rewards (in its cost-estimate document),
quotes throughput at 1,500 B per transaction, and simulates 150 to 350 kB/s
for the parameter set it describes as feasible: 512 kB endorser blocks,
12 MB of transactions and reference scripts, 900 committee seats, a quorum
of 0.75, and timings of 1, 4 and 7 s. The proposal itself treats the
CIP-164 parameters as an ideal goal: technical feasibility may be confirmed
at a lower parameter set, with the higher targets addressed through the
gradual deployment plan. That is the standard this report applies: a
parameter set confirmed feasible, with a credible path upward.

Bytes are one of several limits on what a Leios block carries. Plutus
execution steps and memory and the bytes of reference scripts are capped
alongside them, and reading the proposal's capacity as a count at the
mainnet mix extends to whatever those budgets allow. Section 2 states the
full set of limits and which of them the measurements exercise.

The congested periods of Table 1.1 are characterised in bytes only.
Their Plutus steps and memory and reference-script bytes, the share of
block bytes in script transactions and how often the execution-unit
limit binds before the size limit, are not measured here, although the
transaction-level data is available from Koios. Whether the proposed
parameter sets scale the script budgets proportionally from the Praos
limits is a question this report does not settle. The validation
margin that script computation would draw on is discussed in sections
8.5 and 9.

Tables 1.2 and 1.3 put the targets and the Praos baseline in one unit. The
byte-defined targets are converted to transactions per second at the three
sizes identified above, and the count-defined ones are converted to bytes
per second the other way.

| target | kB/s | tx/s at 877 B (normal) | at 1,500 B (CIP) | at 2,396 B (mint wave) |
|---|---|---|---|---|
| Praos ceiling, 90,112 B x 0.05 | 4.5 | 5.1 | 3.0 | 1.9 |
| Praos in its busiest post-Vasil hours | 3.4 | 3.9 | 2.3 | 1.4 |
| current load, epoch 661 | 0.5 | 0.6 | 0.3 | 0.2 |
| proposal, 6x capacity | 27 | 31 | 18 | 11 |
| proposal, 10x capacity | 45 | 51 | 30 | 19 |
| CIP-164 feasible parameters, simulated | 150-350 | 171-399 | 100-233 | 63-146 |

Table 1.2. Byte-defined targets and the Praos baseline, in bytes per second
and in transactions per second at three transaction sizes.

| target | tx/s | kB/s at 877 B (normal) | at 1,500 B (CIP) | at 2,396 B (mint wave) |
|---|---|---|---|---|
| proposal, 27 M transactions a month at 50 to 70 % utilisation | 15-21 | 13-18 | 22-31 | 36-50 |
| CIP-164 sustainability line | 50 | 44 | 75 | 120 |

Table 1.3. Count-defined targets, in bytes per second at the same three
sizes. The proposal's figures are taken from its on-chain metadata (Koios),
the CIP's from the CIP-164 README and its cost-estimate document.

The proposal's tenfold target and the CIP's 50 transactions per second
coincide near 45 kB/s at the normal mix; at the CIP's own transaction size
of 1,500 B, the 50 tx/s line is 75 kB/s. The CIP's simulated parameter set
sits three to eight times above that line.

## 1.3 Where the measured parameter sets sit on paper

The report measures three parameter sets, each named by the two caps that
define it: the reference list an endorser block may carry, which caps the
transaction count at 36 or 37 bytes per reference by the transaction's
size, and the bytes of its closure,
the transactions it brings into the chain. Table 1.4 gives the parameter
ceiling of each set, the rate it would carry with every endorser block full
and every one certified, against the targets of the previous subsection.

| parameter set | reference cap | closure cap | parameter ceiling, kB/s | tx/s at 877 B | against the targets |
|---|---|---|---|---|---|
| 40 kB / 260 kB | 40,000 B (1,111 txs) | 260 kB | 8.9 | 10 | twice the Praos ceiling |
| 100 kB / 1 MB | 100,000 B (2,777 txs) | 1,000 kB | 27.9 | 32 | the proposal's 6x line |
| 308 kB / 2 MB | 308,000 B (8,555 txs) | 2,000 kB | 53.5 | 61 | the 10x line, and the CIP's 50 tx/s at the normal mix |

Table 1.4. The parameter ceiling of each set, computed as the closure cap
times f times p, plus the plain Praos block's share at its 90,112 B limit,
where p = 0.513 is the probability that the next block arrives late enough
(14 slots or more) for the certificate to be included. Section 2 defines the ceiling and the
corrections that take it down to a measurement, and section 4 reports both
for each set.

How much of each ceiling the protocol delivers on real nodes, and why it
falls short where it does, is the question the rest of the report answers.

# 2. What is assessed and what to expect

This section describes the Leios pipeline as it is deployed on the networks
measured in this report, the clock each of its stages runs against, the set
of parameters and conditions that bound it, and the way the report relates a
parameter set's ceiling to what the chain actually carries. It contains no
measurements. Its purpose is to fix the vocabulary and the expectations that
the results in section 4 are read with, so that each result there can be
stated as what was expected, what was measured, and why the two differ.

## 2.1 The pipeline and its clock

Leios adds to Praos a second kind of block, the endorser block, which lets a
ranking block bring into the chain many more transactions than it could
carry itself. The ranking block (RB) remains the Praos block: produced by the
slot leader, limited in size, and the only block that extends the chain. The
endorser block (EB) is a list of transaction references announced inside an
RB; the transactions it refers to, called its closure, enter the ledger only
when a later RB carries a certificate stating that a committee of stake
pools has validated them. The pipeline between an announcement and its
certificate has six stages, each with a clock of its own.

The first stage is the forger's snapshot. When a pool is elected for a slot,
its node takes a snapshot of its mempool, builds the RB, and, as deployed,
announces an EB with it: the references of the transactions in the snapshot
that fit the caps, 36 or 37 bytes per reference by the transaction's
size. The node budgets a fixed time for
the snapshot, so the EB is bounded by what the mempool holds when the slot
comes and by the time the node allows itself to partition it, not only by
the caps. An RB that carries a certificate brings the certified closure's
transactions into the ledger and, as deployed, carries no transactions of
its own; an RB without a certificate carries its own transactions as a Praos
block does.

The second and third stages are diffusion. The EB body, the reference list,
is fetched by every node that learns of the announcement; the closure, the
transactions themselves, is assembled next, from the node's own mempool for
the transactions it already holds and from its peers for the rest. Both are
driven by the node's block-fetch and transaction-fetch logic and therefore
depend on the topology, the bandwidth and the mempool content of each node.

The fourth stage is validation and voting. The committee, the pools with
the most stake up to a maximum number of seats (900 on the testnet), one
seat per pool and each seat's vote weighted by its pool's stake, validates
the closure against the ledger state and votes. The vote is
scheduled three seconds after the EB's slot and must be cast by seven
seconds after it, the deployed diffusion bound (the protocol's timing
parameters L_hdr, L_vote and L_diff are 1, 4 and 7 s on these networks). A
voter that holds the closure before the three-second mark waits; one that
receives it after the seven-second deadline does not vote. Validation
applies to the ledger state every transaction of the closure, in full for
the ones the node has not validated before and as a reapplication for the
ones it validated at mempool admission or in an earlier EB, so its cost
depends on how much of the EB the voter had already validated.

The fifth stage is the tally. Votes diffuse between the nodes, and every
node keeps a running tally of the weight behind each EB; the EB is
certifiable once the tally reaches the quorum, three quarters of the
committee's weight. The certificate can be included only in an RB whose slot
is at least fourteen slots after the announcing RB's, the certification gap,
which gives the votes time to arrive. Since RBs come at random with an
active slot coefficient of 0.05, the probability that the next RB is far
enough away is 0.95 raised to the thirteenth power, 0.513: on paper, about
half of the EBs announced are eligible for certification at all, and the
other half are superseded by the next announcement before their votes could
count.

The sixth stage is adoption. A node that receives a certifying RB must hold
the certified closure before it can select the block, apply or reapply its
transactions on top of the chain, and only then adopt it. This is the point
at which Leios touches Praos directly: the certifying RB is a Praos block
whose adoption carries more work than a plain one, and if that work delays
its propagation, the next slot leader may build on the previous block
instead, forking the chain. Section 5 is about this stage.

Each stage thus has either a deadline or a budget: the snapshot has a time
budget, the body and the closure must arrive before the vote can be cast,
validation must fit between the closure's arrival and the deadline, the
tally must reach the quorum before an eligible RB comes, and adoption must
not delay the Praos block. The results tables of section 4 have one row per
stage for that reason.

## 2.2 The constraint set

A Leios parameter set is not one number. The caps and budgets below bound
the pipeline jointly, and the quantity of interest, the bytes the chain
carries per second, integrates all of them. Table 2.1 lists them with the
stage each one binds and whether the measurements in this report exercise
it.

| constraint | what it bounds | stage it binds | exercised by the measurements |
|---|---|---|---|
| reference cap (bytes of the EB body) | the number of transactions an EB may reference, at 36 or 37 B each | snapshot; body diffusion | yes, binding at small transactions |
| closure cap (bytes of the EB's transactions) | the bytes an EB brings into the chain | closure diffusion; validation; adoption | yes, binding at large transactions |
| reference-script cap | the bytes of reference scripts the closure may pull in | validation | no: the transactions used carry no scripts |
| Plutus steps and memory budgets | the script computation the closure may require | validation | no: the transactions used carry no scripts |
| timings L_hdr, L_vote, L_diff | when votes are cast and by when | validation and voting | yes, at the deployed values only |
| certification gap | how far the next RB must be for a certificate to count | tally | yes, at 14 slots |
| committee size and quorum | how much stake must vote, and how it is spread | tally | yes, with the real stake distribution of each network |
| the Praos block limit and f | the plain block's share and the RB rate | all, as the clock | fixed at mainnet's values |

Table 2.1. The parameters of a Leios set and the stage each one binds.

Three conditions outside the parameter set bound the pipeline as much as
the parameters do and cannot be set by the protocol: the hardware of the
nodes, which decides how fast a closure is validated; the mempool coverage,
how much of an EB a node already holds when it is announced, which decides
how much validation is applied in full; and the topology, which decides how
fast bodies, closures and votes travel. The report measures on the
populations described in section 3 and states its results against them; it
does not define a reference machine. The script and reference-script
budgets are the one part of the parameter set the measurements leave
untouched, because every population ran plain value transactions. Those
budgets share the voter's validation window with the byte caps, so they are
not independent of them. A voter must have received and validated the
closure by the deadline, so the seven seconds after the slot are shared
between the closure's arrival and its validation: whatever validation
work a closure carries, script computation or more transactions, must be
paid for by a closure that arrives earlier, and at a given bandwidth an
earlier closure is a smaller one. Only a closure that arrives before the
three-second mark escapes this trade, since voting cannot start earlier
and its validation has the full four seconds whatever its size; there,
script computation trades against the validation of other transactions
instead. A larger script budget therefore means a smaller closure in
either case. The report treats them as budgets to be set conservatively
alongside the byte caps it measures, not as dimensions it has confirmed.

## 2.3 The ceiling and the ladder

The rate a parameter set can carry on paper follows from the pipeline above.
Each RB either certifies the EB announced by the previous one, with
probability p, and brings its closure of up to E bytes, or does not and
carries a plain block of up to R bytes; RBs come at the rate f per slot. The
parameter ceiling is therefore

    f x (p x E + (1 - p) x R)

bytes per second, with p = 0.513 under the fourteen-slot gap, E the closure
cap and R the Praos block limit of 90,112 B, against which the plain
block's fullness is also read in the rungs below. It assumes every EB full
and every eligible EB certified. The chain carries less than this for reasons that can be
named one at a time, and the report presents them as a ladder of rungs,
each a correction applied on top of the previous one:

| rung | what it replaces | what the loss means |
|---|---|---|
| parameter ceiling | nothing: the caps, f and p on paper | the protocol's rate at this parameter set |
| workload ceiling | E by the cap that actually binds at the measured transaction size | at small transactions the reference cap fills before the closure cap, and the EB carries fewer bytes than the closure cap allows |
| observed spacing | f and p by the RB rate and gap share actually observed | the chain's own randomness in the window: more or fewer RBs than expected, more or fewer of them far enough apart |
| voting-adjusted | p by p times the share of eligible EBs that were certified | EBs that reached no quorum in time: the voting stage's loss; shown for full EBs, and for the actual mix when the two differ |
| load-adjusted | E and R by the bytes the EBs and plain blocks actually held, and the share of RBs that announced | the load offered to the forgers fell short of the caps: the generator's or the mempools' loss, not the protocol's |
| measured | all of the above by the bytes counted on the chain | what the chain carried |

Table 2.2. The throughput ladder. Each rung is computed from the chain
itself (block headers, EB sizes and certificates) over the load windows of
a period, independently of which nodes report.

The ladder separates what the parameters allow from what the chain
randomly offered, what the voters lost and what the load did not supply.
Section 4 shows it in full for every parameter set, and the stage table
next to it says where in the pipeline the voting loss arose.

## 2.4 Load and mempool coverage

Load, for this report, is what reaches a forger's mempool when its slot
comes, not what users submitted to the network. The distinction matters
twice. For the forger, an EB is bounded by the mempool at the slot, so a
generator that submits in bursts, or to a few nodes, produces EBs well
under the caps regardless of the parameters, and the load-adjusted rung
exists to separate that shortfall from the protocol's. For the voters,
validation cost depends on the share of the EB's transactions they already
hold: a transaction that reached the voter's mempool before the EB was
announced is reapplied cheaply, one that did not is applied in full. Leios
therefore wants the same transaction in many mempools, where Praos only
needs it in the next leader's. How transactions are submitted on mainnet
is not known from the testnet, and the report does not claim that the
generators used are an optimistic or a pessimistic case for it; it reports
the mempool coverage of each population alongside its results so that the
reader can place mainnet against them.

The same distinction explains why the report measures in load windows. The
caps bound the long-run rate, and the lottery's variance over a day washes
out; but the mempools, taken over the forgers of a short burst, decide how
full the EBs of that burst are. A burst of full EBs over a few minutes is
therefore not evidence of headroom, and a daily average mixes loaded hours
with idle ones. Every measurement in section 4 is taken over the hours in
which the generators kept the mempools loaded, with the windows stated.

## 2.5 What to expect at each stage

The structure above gives an expectation for each stage before any
measurement, and section 4 states them per parameter set with the
numbers the ceiling and the models supply.

Body and closure diffusion should scale with the bytes to move and be bound
either by bandwidth, on hosts that receive from well-connected peers, or
by topology, on hosts several hops from the forgers; a closure that arrives
after the vote deadline is lost to the voting stage whatever else happens.
Validation should cost a roughly constant time per transaction the voter
has not validated before, so it grows with the EB's transaction count and
with the share of it the voter applies in full, and it has to fit in the
four seconds
between the vote mark and the deadline after the closure is in hand. The
tally should reach the quorum once three quarters of the committee's
weight has voted, so it arrives close to the deadline when the slow voters
hold much of the weight, and it is sensitive to stake that does not vote
at all: a quorum of 0.75 leaves a margin of 0.25, and every seat that is
silent for any reason spends it. Certification therefore depends on the
stake distribution of the network as much as on the parameters, and a
network where most of the weight sits on fast, well-connected hosts will
certify EBs that a network with the same parameters and a wider spread of
hosts will not. Adoption of a certifying RB should cost the closure's
reapplication on top of a plain block's adoption, growing with the closure,
and the consequence to look for is not a missed slot but a late block: the
next leader building on the previous block because the certifying one had
not reached it.

Where a stage falls short of its expectation in section 4, the report asks
which of the three outside conditions, hardware, mempool coverage or
topology, or which parameter, explains the shortfall, and what change
would recover it. That is the content of sections 6 and 8.

# 3. Populations and instruments

The measurements in this report come from three sources: the public Leios
testnet, the benchmarking cluster, and a ledger benchmark run by stake pool
operators on their own machines. Each observes a different population of
nodes under different conditions, and each answers a different part of the
question. This section describes the three, the instruments that read
them, and what each can and cannot say, so that the results of section 4
are read with their population in mind. The report does not define a
reference machine; every result is stated against the population it was
measured on.

No reference hardware has been defined for Leios yet. The report measures
on the populations it has: the operator nodes of the testnet, whose
hardware is unknown except through the ledger benchmark's spread and the
measured validation speeds; the IOG and PIR hosts, whose instance types
are known; and the cluster's uniform c5d.2xlarge hosts. Which of these
stands for the machine the parameters are set for is a decision this
report does not make.

## 3.1 The public testnet

The testnet is a Leios network run by stake pool operators and by IOG, on
a chain restarted with a new genesis on 2026-10-18. Its protocol parameters
are those of the sets named in section 1, with a committee of 900 seats, a
quorum of three quarters of the committee's weight, timings of 1, 4 and 7 s,
a certification gap of 14 slots and a reference-script cap of 1 MiB. The
reference and closure caps were 40 kB and 260 kB from the restart, and
308 kB and 2 MB from the epoch boundary of 2026-10-24 00:00 UTC. The
committee seats the pools with the most stake, one seat per pool and up to
900 of them, and each seat's vote carries the weight of its pool's stake.
With 100 to 150 pools holding stake, every one of them is seated, so the
voters are the pools themselves and the vote traffic per EB is one vote
from each, not 900. Table 3.1 lists the three load windows the report
measures on it.

| window | caps | loaded hours (UTC) | transaction size (mean over the certified closures) | pools in the committee | weight of the 14 IOG and PIR pools |
|---|---|---|---|---|---|
| 40 kB / 260 kB | 40 kB references, 260 kB closure | 2026-10-21 12:00-13:00, 17:00-21:00, 10-22 00:00-01:00 (6 h) | 257 B | 100-108 | 0.45-0.48 |
| 308 kB / 2 MB | 308 kB references, 2 MB closure | 25 even hours from 2026-10-24 12:00 to 10-26 13:00 | 318 B | 145-148 | 0.35-0.36 |
| 308 kB / 2 MB, 1 kB transactions | the same | 2026-10-28 18:00, 20:00, 22:00, 10-29 00:00 (4 h) | 810 B | 150 | 0.35 |

Table 3.1. The testnet load windows. The loaded hours are those in which
the generator ran; the odd hours between them carried residual load only
and are excluded. The 2 MB window's 318 B is the mean of two sizes of
the same one-input transaction from two generators, 247 B for three
quarters of the transactions and 506 B for a quarter, which differ in
their metadata.

The stake is not evenly spread. Fourteen pools are operated by IOG (IOG1
to IOG3, PIR0 to PIR10), and together they hold between a
third and a half of the committee's weight depending on the window, PIR0
alone a tenth or more. The operator pools, between 86 and 136 of them,
share the rest at an average of well under one percent each, with the
largest at about half a percent. Certification, which needs three quarters
of the weight, therefore depends on the IOG and PIR pools voting and on a
large number of small pools voting as well; the quorum's margin of a
quarter is spent by whichever of them does not.

The operator nodes are the population of interest for Leios on mainnet,
and the least known. Their hardware is not reported; what the report knows
of it is the validation speed it measures on each node and the spread the
ledger benchmark of section 3.3 found across operator machines. Their
topology is not known beyond the naming of their agents as producers or
relays. Their software is: during the first two windows, nearly every
operator agent sending metrics ran one build of the node (version
11.2.0.164 at revision 2d6a2a66, the same code as the IOG hosts and the
cluster, with ten agents on an older 11.1.0 build in the first window and
one in the second); during the 1 kB window the fleet was mid-upgrade, with
two thirds of the agents on the next revision (65dd69d1) and one third
still on the previous one, and the IOG and PIR hosts on the next revision
as well. The 1 kB window is thus measured on a mixed build, and the report
treats it as such.

The IOG and PIR hosts are AWS instances whose configuration is known
(Table 3.2). The node runs with an in-memory ledger on every host but
IOG3, which keeps the UTxO set on disk (the LSM backend on the instance's
local NVMe), and one capability per vCPU; each PIR host is in a different
AWS region. PIR0 runs on a host
outside the monitoring and sends neither logs nor metrics to any source
the report reads.

| hosts | instance type | vCPUs, node capabilities | memory | role |
|---|---|---|---|---|
| IOG1, IOG3 | c8id.xlarge | 4 | 8 GiB | block producers behind IOG relays; IOG3 with the UTxO set on disk |
| IOG2 | r8id.xlarge | 4 | 32 GiB | block producer behind IOG relays |
| PIR1, PIR3, PIR4, PIR8, PIR10 | c8id.xlarge | 4 | 8 GiB | block producers, one region each |
| PIR2, PIR5, PIR6 | c6id.2xlarge | 8 | 16 GiB | block producers, one region each |
| PIR7, PIR9 | c5d.2xlarge | 8 | 16 GiB | block producers, one region each; the cluster's instance type |

Table 3.2. The IOG and PIR hosts that report through the IOG monitoring,
as the monitoring's host series record them in every window (the three
IOG producers were resized to these types on 2026-10-16, before the
chain's restart). The c8id and r8id instances are the current CPU
generation, c6id two generations older and c5d three. IOG1 reports
through both sources; the report uses its monitoring copy.

The load is generated by one IOG-run transaction generator submitting into
three IOG relays in different regions during the even UTC hours, with a
transaction size set per window: value transactions of 250 to 435 B in the
first two windows, and from 2026-10-28 transactions of about 1 kB carrying
metadata, with a second generator submitting 230 to 260 B transactions at
the same time, so that EBs of 1 kB transactions bound by the closure cap and
EBs of small transactions bound by the reference cap coexist in every hour
of that window. Because the injection points are IOG relays, the IOG hosts'
mempools fill first and hold the most transactions when an EB is announced,
which places them at the low end of the fleet's validation cost in section
4. The rate the generator actually sustained is not a parameter of the
network but a measurement, and it appears in section 4 as the
load-adjusted rung of each window's ladder.

Two instruments read the testnet. The first is the operator telemetry: an
agent on each participating operator node ships the node's event log and
its metrics scrapes to an archive, signed and identified by pool and agent.
From it the report reads, per node, the Leios kernel's events (an EB
announcement accepted, its body and its closure acquired, the closure
validated with the counts of transactions applied in full and reapplied,
the node's vote or its reason for not voting, every vote received with the
node's running tally), the forge loop's events, and the node's metrics
(version, resident memory, CPU time, mempool content). The second is the
IOG monitoring, which holds the same event families and metrics for the
IOG and PIR hosts; the report merges the two into one database per window
so that every instrument reads both populations at once. Table 3.3 gives
the coverage that results. Whenever a section 4 table is captioned with
reporting nodes and weight, these are the figures.

| window | reporting nodes | from pools | pools in the committee | committee weight observed | largest weight not observed |
|---|---|---|---|---|---|
| 40 kB / 260 kB | 83 | 83 | 100-108 | 0.73-0.75 | PIR0, 0.13 |
| 308 kB / 2 MB | 89 | 89 | 145-148 | 0.63 | PIR0, 0.10 |
| 308 kB / 2 MB, 1 kB transactions | 85 | 85 | 150 | 0.61 | PIR0, 0.10 |

Table 3.3. Reporting coverage of the testnet per window, both sources
merged. A pool counts as observed when its node's votes are in the data;
the weight is the share of the committee's weight those pools hold.

The third input is the chain itself: every block header with the size of
the EB it announces, the size of the closure it certifies and whether it
carries a certificate, from the testnet explorer's API, with the
committee's seats and weights per epoch from a db-sync instance. The ladder
of each window, the sizes of EBs and closures and the certification rate
are computed from the chain alone and do not depend on which nodes report.
The nodes' event timestamps are their own clocks; the report checks them
against the slot clock and found no measurable spread in the windows used.

What the testnet can say is what no other source can: how the pipeline
behaves on nodes run by independent operators, on hardware and connections
the protocol does not control, with certification weighted by a real
distribution of stake. What it cannot say follows from the same facts. The
hardware and topology of the operator nodes are unknown. The load is not
under the report's control and never saturated the caps for long. Between
0.61 and 0.75 of the committee's weight is observed, and the largest
unobserved voter, PIR0, holds a tenth or more of it, so a failure to
certify can be attributed to a reporting voter's lateness or silence but
only inferred for the non-reporting weight.

## 3.2 The benchmarking cluster

The cluster is a network of 51 nodes run by the benchmarking team on one
instance type, c5d.2xlarge (8 vCPUs, 15.2 GiB), each with six upstream
peers in a fixed topology, an in-memory ledger, the node given two
capabilities, and tracing at debug level on the chain database, the
mempool, the Leios kernel and transaction submission. The code is the same
w42 revision the testnet ran during its first two windows. Every node is a
block producer with the same stake, so the committee is 51 voters of equal
weight and the quorum is 39 votes. A generator feeds every node with value
transactions of a fixed shape, different transactions to each node,
saturating the caps throughout a run. Table
3.4 lists the three runs the report uses.

| run | caps | transactions | certification gap | span (UTC) | RBs on the chain |
|---|---|---|---|---|---|
| 40 kB / 260 kB | 40 kB references, 260 kB closure | 200 B, one input, one output | 15 slots | 2026-10-17 22:01 to 10-18 15:40 (17.6 h) | 3,083 |
| 100 kB / 1 MB, 200 B | 100 kB references, 1 MB closure | 200 B, one input, one output | 14 slots | 2026-10-20 21:00 to 10-21 14:47 (17.8 h) | 3,079 |
| 100 kB / 1 MB, 374 B | the same | 374 B, two inputs, two outputs | 14 slots | 2026-10-21 16:39 to 10-22 09:50 (17.2 h) | 2,968 |

Table 3.4. The cluster runs. At 200 B the reference cap binds and the
closures stay well under their cap; at 374 B the closure cap binds, the
first run on any population where it did.

The cluster's instrument is the per-node trace database the team delivers
with each run, holding the same event families the testnet's agents ship;
the report builds it into the same layout and reads it with the same
instruments, and reconstructs the chain from the forge events. Every node
is observed, so the cluster's figures are complete where the testnet's are
sampled.

What the cluster can say is what the testnet cannot: the behaviour of the
pipeline under a controlled, saturating load, on uniform hardware, with
every node observed, so that a change between runs is attributable to the
parameter that changed. What it cannot say is anything about diversity.
Its stake is uniform, its topology fixed and shallow, its hosts identical,
and its load comes from one generator that submits different transactions
into every node's mempool, spending outputs created at genesis, 5.5
million of them, which the runs reuse almost never. A voter still
receives the other nodes'
transactions through diffusion, so what it already holds of an EB when it
is announced is decided by the race between the generator's injection and
the diffusion among peers, in time rather than in place, whereas on the
testnet it is decided by how far a node sits from the three injection
points.

## 3.3 The ledger benchmark

The third source is a benchmark of block application run by 26 stake pool
operators on their own machines between 7 and 18 October 2026, using the
consensus team's database analyser over one synthetic Praos chain of 768 kB
blocks (2,086 transactions of about 370 B each, no scripts). It times, per
transaction, the application of a block to the ledger in full and its
reapplication, with the UTxO set in memory and on disk, networking left
out. It exercises the Praos block-application path only, the one a node
runs when it adopts a block, and nothing of the Leios kernel's voting path.

What it can say is the one thing neither network can: how far the
operators' machines are apart. In-memory application spans a factor of six
across the 26 machines, and storage adds a spread of its own. The report
uses it in section 6 as the hardware axis against which the validation
costs measured on the networks are placed. It has a second role: per
transaction application and reapplication costs of this kind, obtained by
replaying mainnet blocks through the same ledger code, are the inputs of
the DeltaQ model of Leios, so section 7 reads the model's constants
against the networks' measured costs through it. What it cannot say is
anything about Leios itself, or about the machines that did not take part.

## 3.4 What each source can and cannot say

| | testnet | cluster | ledger benchmark |
|---|---|---|---|
| nodes | 83-89 reporting of 100-150 pools; operators and IOG | 51, all observed | 26 operator machines |
| hardware | unknown for operators; known for 13 IOG and PIR hosts | one instance type | each operator's own |
| stake | real distribution; a third to a half on 14 pools | uniform | none |
| topology | unknown for operators | fixed, six peers | none |
| load | one generator into three relays; not saturating for long | one generator into every node; saturating | one synthetic chain |
| what it establishes | behaviour on independent nodes with real stake weighting | attribution to a parameter under controlled load | the hardware spread of operators |
| what it leaves open | hardware and topology; 0.25-0.39 of the weight unobserved | diversity of any kind; its own validation speed | everything about Leios |

Table 3.5. The three sources side by side.

The report's method follows from the table. A stage's behaviour is
established on the testnet, where it is real, and attributed on the
cluster, where it is controlled; where the two populations disagree, the
disagreement is itself a finding and section 6 explains it; and the
benchmark places the operator hardware the testnet could not see.

# 4. Results by parameter set

The three parameter sets are presented from the smallest to the largest,
each on the populations that ran it. For each set, two tables: the
throughput ladder of section 2.3, one column per population and window,
and the stage table, one row per stage of the pipeline of section 2.1,
with what was expected, what was measured and why the two differ. The
ladders are computed from the chain alone; the stage rows from the nodes'
events, at the median reporting node unless stated, with the reporting
population of each column given in section 3's coverage table. No row
shows a median time: where most of the network has to be reached, the
median is not the number that matters, and the rows give the 90th and 95th
percentiles with the share of nodes that clear the deadline. The tables
are regenerated by `scripts/ladder_table.py` and `scripts/stage_table.py`.

## 4.1 40 kB references, 260 kB closures

The smallest set ran on the cluster at 200 B transactions and on the
testnet during the loaded hours of 2026-10-21 and 22, at 257 B. On the
cluster the reference cap binds (1,111 transactions, 222 kB closures); on
the testnet the closure cap does (about 1,000 transactions at 260 kB).
Every certified closure on the cluster was 222 kB; on the testnet the
median certified closure was 260 kB and the tenth percentile 153 kB.

Expected: a parameter ceiling of 8.6 to 8.8 kB/s, and everything
certified, since a closure of a thousand transactions validates well
inside the four-second window on any host measured, and 260 kB diffuses
in a fraction of the time available.

| rung, kB/s | cluster 40 kB / 260 kB, 200 B | testnet 40 kB / 260 kB, loaded hours |
|---|---|---|
| parameter ceiling | 8.6 (p = 0.488) | 8.9 (p = 0.513) |
| workload ceiling | 7.7 (reference cap at 200 B/tx) | 8.9 (payload cap at 257 B/tx) |
| observed spacing | 7.6 (1 RB / 20.7 s, p = 0.506) | 8.3 (1 RB / 22.9 s, p = 0.586) |
| voting-adjusted, full | 7.6 (s_full = 0.995) | 8.2 (s_full = 0.976) |
| load-adjusted | 7.5 (announcing 1.00, EB 1.00, plain RB 0.98) | 7.2 (announcing 0.99, EB 0.90, plain RB 0.82) |
| measured | 7.5 | 7.2 |

Table 4.1. The ladder at 40 kB / 260 kB. Cluster: the whole run, 17.6 h,
1,547 eligible EBs, 15-slot certification gap. Testnet: the three loaded
windows of 2026-10-21 12:00-13:00, 17:00-21:00 and 10-22 00:00-01:00 UTC,
548 eligible EBs, 14-slot gap. The gap difference moves only the
parameter ceiling: closures reached every cluster node by 3.2 s and the
tally its quorum by 4.2 s, so a 14-slot gap would have left the measured
rows unchanged. Transactions per second at the measured size: 37.4 and
28.1. In every ladder the transaction count of an EB is its reference
bytes over the width a reference takes, 36 B for a transaction under
256 B and 37 B from there on, measured on each window's certified EBs,
whose count the chain carries.

| stage | cluster 40 kB / 260 kB, 200 B | testnet 40 kB / 260 kB, loaded hours |
|---|---|---|
| body: p90 / p95; nodes with p90 under 3 s | 2.26 / 2.41 s; 100 % | 2.04 / 2.31 s; 93 % |
| closure: p90 / p95; nodes with p90 under 3 s / 7 s; not completed | 2.88 / 3.17 s; 67 % / 100 %; 0 % | 2.53 / 2.86 s; 86 % / 96 %; 6 % |
| applied share at the closure | 47 % | 16 % |
| validation, start to validated, p90 | 0.95 s, nodes' quartiles 0.91 to 0.98 | 0.49 s, nodes' quartiles 0.28 to 1.11 |
| vote tally reaches the quorum, p90 | 4.17 s, nodes' quartiles 4.15 to 4.17 | 3.84 s, nodes' quartiles 3.78 to 4.08 |
| vote rate on eligible EBs | 99.5 % | 93 % |
| quorums that became certificates | 100 %, 1,539 of 1,539 quorums seen | 99.8 %, 531 of 532 quorums seen |

Table 4.2. The stages at 40 kB / 260 kB. Cluster: all 51 nodes, equal
weight. Testnet: 83 reporting nodes from 83 pools of the 100 to 108 in the
committee, holding 0.73 to 0.75 of its weight (Table 3.3). "Not
completed" counts closures the node never finished fetching, which at
this set are the closures of EBs on losing forks or superseded within the
gap; a certified EB's closure completed at 99.5 % of the nodes.

Measured: the cluster carried its workload ceiling at observed spacing
times 0.995, every eligible EB but eight certified, and the testnet 7.2
kB/s, 81 % of its parameter ceiling, with 0.976 of its full EBs certified.
The testnet's gap to its ceiling is not the pipeline: the chain's own
spacing in six hours (one RB every 22.9 s instead of 20) and the load
inside the loaded hours (EBs at 0.90 of the cap, plain blocks at 0.85)
account for all but the 2.4 % the voting rung loses. Every stage is
inside its budget on both populations. The closure is at the median node
by 2.5 to 2.9 s, validation takes under a second after it, and the tally
reaches the quorum by 3.8 to 4.2 s against a deadline of 7 s, a margin of
three seconds on both.

The two populations differ where section 3 said they would. The cluster's
voters apply 47 % of each closure in full against 16 % on the testnet,
because the cluster's generator feeds every node its own transactions
while the testnet's feeds three relays, and the testnet's nodes have most
of each EB in their mempools when it is announced; that this costs the
cluster nothing here is because the count is small. The cluster's
reception comes in three tiers half a second apart (closure p90 of 2.7,
2.9 and 3.2 s), one hop's cost at this size in its fixed topology. On the
testnet the IOG and PIR hosts sit in the faster half of the fleet, with
closure p90 between 2.2 and 2.7 s against the fleet's 2.5 s median, and
86 % of all reporting nodes hold the closure within 3 s. The testnet's
seventeen failures are not near misses: thirteen drew votes from almost
no reporting voter, the signature of an EB announced on a fork the voters
had not adopted, two had the announcing RB arrive late, one is attributed
to unobserved weight and one is unexplained.

## 4.2 100 kB references, 1 MB closures

The middle set ran on the cluster only, twice: at 200 B transactions,
where the reference cap binds (2,777 transactions, 555 kB closures), and
at 374 B two-input transactions, where for the first time on any
population the closure cap bound, with certified closures of exactly 1 MB
from the median up (2,673 transactions). No testnet window exists at this
set with closures near the cap; the chain ran it with 204 B transactions
before its restart, bound by the reference cap at 567 kB, and that period
is not comparable on other grounds.

Expected: 27.9 kB/s on paper, 16.5 with the reference cap binding at
200 B; and, from the hosts' cost per transaction applied in full, measured
at 1.8 ms on this cluster, a share of the EBs failing, since validating
2,700 transactions from scratch takes longer than the four seconds between
the vote mark and the deadline, and the two-input transactions cost more
each at the same count.

| rung, kB/s | cluster 100 kB / 1 MB, 200 B | cluster 100 kB / 1 MB, 374 B |
|---|---|---|
| parameter ceiling | 27.9 (p = 0.513) | 27.9 (p = 0.513) |
| workload ceiling | 16.5 (reference cap at 200 B/tx) | 27.9 (payload cap at 374 B/tx) |
| observed spacing | 16.4 (1 RB / 20.8 s, p = 0.538) | 27.6 (1 RB / 20.8 s, p = 0.533) |
| voting-adjusted, full | 12.6 (s_full = 0.689) | 16.9 (s_full = 0.540) |
| load-adjusted | 12.2 (announcing 0.99, EB 0.97, plain RB 0.97) | 15.5 (announcing 0.99, EB 0.94, plain RB 0.98) |
| measured | 12.2 | 15.5 |

Table 4.3. The ladder at 100 kB / 1 MB, whole runs of 17.8 h and 17.2 h,
1,637 and 1,570 eligible EBs, 14-slot gap. Transactions per second at the
measured size: 60.7 and 41.3.

| stage | cluster 100 kB / 1 MB, 200 B | cluster 100 kB / 1 MB, 374 B |
|---|---|---|
| body: p90 / p95; nodes with p90 under 3 s | 2.90 / 3.07 s; 98 % | 2.60 / 2.96 s; 100 % |
| closure: p90 / p95; nodes with p90 under 3 s / 7 s; not completed | 3.77 / 4.02 s; 0 % / 100 %; 0 % | 3.54 / 3.96 s; 0 % / 100 %; 0 % |
| applied share at the closure | 38 % | 32 % |
| validation, start to validated, p90 | 4.48 s, nodes' quartiles 4.31 to 4.57 | 6.40 s, nodes' quartiles 6.12 to 6.51 |
| vote tally reaches the quorum, p90 | 6.73 s, nodes' quartiles 6.72 to 6.76 | 6.73 s, nodes' quartiles 6.71 to 6.76 |
| vote rate on eligible EBs | 77 % | 63 % |
| quorums that became certificates | 99.6 %, 1,128 of 1,132 quorums seen | 99.6 %, 820 of 823 quorums seen |

Table 4.4. The stages at 100 kB / 1 MB, all 51 nodes, equal weight.

Measured: 12.2 and 15.5 kB/s, with 0.689 and 0.540 of the full EBs
certified. The step from 260 kB to 555 kB closures paid in throughput, 7.5
to 12.2 kB/s, and the step to 1 MB paid again, to 15.5, but each took
certification further from its plateau. The loss is in one row. Every
closure is at every node before 4 s, and the body before 3; the applied
share is in the same range as the smaller run; but validation, which took
under a second at 1,110 transactions, takes 4.5 s at 2,777 and 6.4 s at
2,673 two-input transactions, past the four seconds available, and the
tally reaches the quorum at 6.7 s, with the deadline at 7. The vote rates
of 77 % and 63 % are the share of EBs each node validated in time, and
since every node is the same, the EBs that cross the deadline on one cross
it on most: every quorum seen became a certificate, and the failures are
EBs for which no quorum formed anywhere. The spread across nodes is
narrow (validation p90 from 4.0 to 5.0 s on the 200 B run, 5.7 to 7.1 on
the 374 B run), which is the uniform hardware.

The binding quantity is therefore the validation work of the EB on the
host, counted in transactions times the cost of each transaction's shape,
not in bytes: the 374 B run holds fewer transactions than the 200 B run
and loses more, because each transaction costs twice as much to apply.
Section 6 gives the cost per transaction per host and what the same EBs
would do on current-generation hosts, which the testnet measured at a
fraction of the cluster's cost per transaction; on those, most of this
loss would not occur. Section 5 takes up the other finding of these runs,
the certifying RB's cost at adoption, which grows with the closure.

## 4.3 308 kB references, 2 MB closures

The largest set ran on the testnet only, in two windows: the loaded hours
of 2026-10-24 to 26 at 318 B transactions, where the closure cap binds at
6,284 transactions, and the window of 2026-10-28 in which the generator
moved to transactions of about 1 kB while a second generator kept
submitting small ones. The second window is presented in 4.3.1 for the one
point it makes.

Expected, from 4.2: 53.5 kB/s on paper, and certification falling with EB
size, since 6,000 transactions are far beyond the 2,000 to 3,300 that the
hosts measured so far validate inside the window from scratch, and the
operator population spans a wider range of hosts than the cluster.

| rung, kB/s | testnet 308 kB / 2 MB, loaded hours | testnet 308 kB / 2 MB, 1 kB transactions |
|---|---|---|
| parameter ceiling | 53.5 (p = 0.513) | 53.5 (p = 0.513) |
| workload ceiling | 53.5 (payload cap at 318 B/tx) | - |
| observed spacing | 49.5 (1 RB / 25.5 s, p = 0.613) | 52.0 (1 RB / 22.6 s, p = 0.569) |
| voting-adjusted, mix | 25.9 (s_all = 0.485) | 25.8 (s_all = 0.454) |
| voting-adjusted, full | 9.9 (s_full = 0.138) | - |
| load-adjusted | 15.9 (announcing 0.98, EB 0.59, plain RB 0.90) | - |
| measured | 12.0 | 22.0 |

Table 4.5. The ladder at 308 kB / 2 MB. Loaded hours: the 25 even hours
from 2026-10-24 12:00 to 10-26 13:00 UTC, 2,128 eligible EBs, 1,033
certified. 1 kB window: the four even hours from 10-28 18:00 to 10-29
01:00 UTC, 361 eligible, 164 certified. Both voting-adjusted rungs are
shown because they differ here: "full" is the survival of EBs at the cap,
"mix" of all eligible EBs as forged. Both columns carry two transaction
sizes (Table 3.1). Three rungs read an EB's bytes from its references at
the mean size: the cap that binds, the threshold for a full EB and the
EBs' load factor. In the loaded hours the sizes are 247 and 506 B and
the closure cap binds for both, so the mean misreads the 506 B-heavy
EBs, a quarter of the transactions, as 0.6 to 0.8 of their bytes: the
full rung then counts the 247 B EBs of 6,200 transactions and up, the
ones costliest to validate, and the load-adjusted rung is an estimate
off by at most that quarter in a direction the chain does not record;
the measured rung, the certified closures' bytes, is exact. The rungs
are kept with that reading. In the 1 kB window the sizes are 220 and
1,024 B and bind different caps: a full 1 kB closure reads as 0.8 full
and a full small-transaction EB as 3.5 times the cap, so there the mean
gives no reading at all; those rungs are left out of its column and
4.3.1 reads the window by EB class. Transactions per second at the
measured size: 38.0 and 29.6.

| stage | testnet 308 kB / 2 MB, loaded hours | testnet 308 kB / 2 MB, 1 kB transactions |
|---|---|---|
| body: p90 / p95; nodes with p90 under 3 s | 3.09 / 4.28 s; 45 % | 2.36 / 3.35 s; 69 % |
| closure: p90 / p95; nodes with p90 under 3 s / 7 s; not completed | 3.90 / 5.37 s; 16 % / 73 %; 8 % | 3.26 / 4.17 s; 41 % / 82 %; 12 % |
| applied share at the closure | 22 % | 17 % |
| validation, start to validated, p90 | 3.51 s, nodes' quartiles 2.24 to 8.54 | 2.24 s, nodes' quartiles 1.46 to 3.52 |
| vote tally reaches the quorum, p90 | 6.94 s, nodes' quartiles 6.88 to 7.60 | 6.99 s, nodes' quartiles 6.97 to 7.10 |
| vote rate on eligible EBs | 73 % | 77 % |
| quorums that became certificates | 93 %, 1,033 of 1,107 quorums seen | 90 %, 164 of 182 quorums seen |

Table 4.6. The stages at 308 kB / 2 MB. Loaded hours: 89 reporting nodes
from 89 pools of the 145 to 148 in the committee, holding 0.63 of its
weight; 1 kB window: 85 nodes from 85 of 150 pools, 0.61 (Table 3.3). In
both, the largest weight not observed is PIR0's tenth. "Not completed"
is 1.6 % of nodes for a certified EB's closure; the 8 % and 12 % are the
closures of EBs that failed, were superseded within the gap, or sat on
losing forks, which nodes stop fetching.

Measured, in the loaded hours: 12.0 kB/s, 22 % of the parameter ceiling,
with 0.485 of the eligible EBs certified as forged and 0.138 of the full
ones. The ladder splits the loss in two. The EBs were at 0.59 of the cap
on average (the load-adjusted rung, 16 kB/s), because the operator
producers forge small EBs from thin mempools while the IOG and PIR
producers, whose mempools are at the injection points, forge full ones;
and of what was forged, half failed. The median certified closure was
765 kB with 2,400 transactions, the median failed EB had 4,900, and the
two populations barely overlap. Table 4.7 gives the closure stage by EB
size.

| EB size | EBs | certified | certified closure p50 | 90 % of nodes hold it by (p50 over EBs) | EBs held by 90 % within 7 s | by 95 % within 7 s |
|---|---|---|---|---|---|---|
| under 2,000 txs | 519 | 75 % | 313 kB | 3.05 s | 76 % | 62 % |
| 2,000-4,000 | 492 | 76 % | 865 kB | 5.72 s | 60 % | 29 % |
| 4,000-6,000 | 739 | 25 % | 1,707 kB | 11.27 s | 17 % | 5 % |
| 6,000 and up | 295 | 17 % | 1,668 kB | 15.88 s | 6 % | 3 % |

Table 4.7. Closure diffusion by EB size, loaded hours: for each eligible
EB, the time after its slot by which 90 % and 95 % of the reporting nodes
that heard it announced held its closure, then its distribution over EBs.
Sizes by reference count; the certified closure's median bytes for each
bin.

The stage rows say where the loss is. The closure is at the median node
by 3.9 s, later than at any smaller set but inside the window for most
EBs under 4,000 transactions; above that, the closures of 1.7 MB reach 90 %
of the nodes only by 11 to 16 s, past the deadline, and both the fetch
and the validation behind it are the reason. Validation after the closure
takes 3.5 s at the median node, with the nodes' quartiles from 2.2 to 8.5
s, a spread of four times across the operator hardware where the cluster
had one of 1.2. The tally reaches the quorum at 6.9 s, at the deadline.
The vote rate at the median node is 73 %, but it is 80 to 90 % on the
IOG and PIR hosts and 68 % at the median operator node, and six operator
nodes match or beat the fastest IOG host at the closure (a p90 of 2.9 s),
while two of them validate faster than any IOG host. The 7 % of
quorums that did not become certificates are the forger's side: a quorum
reached at some nodes but not at the forger of the next RB before it
forged, or the forger outside the reporting population.

Of the eligible EBs that failed, 42 % failed because reporting voters
validated too late, 35 % because the weight outside both sources, mostly
PIR0's tenth, did not arrive in time to make up the quorum, 8 % because
the announcing RB itself arrived late at the voters, and 8 % because
reporting voters were silent. The first and the second are the same
mechanism seen from the two populations: at 4,000 transactions and above,
the quorum's margin of a quarter is spent by the slow voters, and the
unobserved weight decides the rest.

The operating point of this network at this set is therefore well under
the cap. Certification is flat at about three quarters up to 4,000
transactions, where the certified closures are 300 to 900 kB, and falls to
a quarter and below above it; the bytes carried per eligible EB, which is
size times survival, peak in the 2,000 to 4,000 bin of Table 4.7, where
three quarters of 865 kB closures certify against a quarter of the
1,707 kB ones in the bin above, and a closure over the peak costs more
than one under it, because a failed 1.5 to 2 MB EB returns its
transactions to the mempools, which refill the next EB to the same size.

### 4.3.1 The 1 kB-transaction window: transaction count, not bytes

From 2026-10-28 18:00 UTC the generator submitted transactions of about
1 kB carrying metadata, while a second generator kept submitting
transactions of 230 to 260 B. In every hour of the window, EBs of three
kinds were therefore eligible: closures made of the 1 kB transactions,
which fill the 2 MB cap at about 2,000 of them; closures of the small
transactions, which fill the reference cap at 8,555; and mixed ones. Table
4.8 gives each kind, with every eligible EB classed by its reference count
from the chain and the exact composition of every certified closure from
the chain database.

| EB class | eligible EBs | certified | certified closure p50 | transactions p50 (certified) | of which about 1 kB / small, p50 | closures that are mixed |
|---|---|---|---|---|---|---|
| under 2,500 references (1 kB closures) | 194 | 125 (64 %) | 1,999 kB | 1,946 | 1,845 / 38 | 104 of 125 |
| 2,500-6,000 references (mixed) | 124 | 38 (31 %) | 2,000 kB | 2,988 | 1,575 / 1,550 | 37 of 38 |
| 6,000 references and up (small transactions) | 43 | 1 (2 %) | 1,528 kB | 6,471 | 0 / 6,451 | 0 of 1 |

Table 4.8. The eligible EBs of the 1 kB window by class, four loaded
hours. The window ran on a mixed node build, two thirds of the operator
agents on the next revision and one third on the previous, the IOG
hosts on the next. Classes by reference count (36 B each); composition of the
certified closures from the transactions the certifying RB carries, each
with its size (db-sync). Regenerated by `scripts/eb_composition.py`.

The point is in the three classes of Table 4.9 whose closures arrived.
Closures of 2 MB certify at 66 % when they hold under 2,000 transactions,
51 % at 2,000 to 4,000 and 4 % at 4,000 to 6,000, and the closure stage
does not move between them: the 2 MB closures reach 90 % of the nodes in
3.3 to 3.5 s in all three classes, where closures of 865 kB holding 3,000
small transactions took 5.7 s in the loaded hours (Table 4.7). What moves
is the validation after the closure. Over every EB the nodes validated in
those hours, the median validation at a node takes 0.51 s under 2,000
transactions,
0.86 s at 2,000 to 4,000 and 1.65 s at 4,000 to 6,000, with the closure in
hand before the vote window opens in 84 to 91 % of the validations in all
three classes, so the larger counts carry the slower voters past the
deadline: 96 %, 91 % and 75 % of the validations complete within 7 s of
the slot. The last row of Table 4.9 is a different failure. Of its 43 EBs,
32 sit at the reference cap, 8,550 references and up, and their body never
reached the nodes: at the median such EB no reporting node received the
body, against 77 nodes for the 11 EBs of 6,000 to 8,549 references, of
which one certified. The EBs at the cap never entered the closure stage
and say nothing about validation. Their forgers are 19 pools that served
the body of none of their 45 eligible EBs in the window, 32 of them at
the cap and 13 below, while the 92 other pools served every body and
none of theirs was at the cap; the failure is the forging nodes', not
the body's size. What binds the pipeline at this set is
therefore what the voters validate, not the bytes they fetch. The count is
not the whole of it: in this window the closures with more transactions
are the ones holding the small transactions, and those spend old outputs
where the 1 kB transactions chain within the block, so each costs more to
apply, which section 7.2 measures. The transaction count and the origin
of the inputs move together here, and the window does not separate them.

| EB size | EBs | certified | certified closure p50 | 90 % of nodes hold it by (p50 over EBs) | EBs held by 90 % within 7 s | by 95 % within 7 s |
|---|---|---|---|---|---|---|
| under 2,000 txs | 94 | 66 % | 1,403 kB | 3.35 s | 81 % | 60 % |
| 2,000-4,000 | 198 | 51 % | 1,999 kB | 3.27 s | 82 % | 64 % |
| 4,000-6,000 | 26 | 4 % | 2,000 kB | 3.52 s | 96 % | 54 % |
| 6,000 and up | 43 | 2 % | 1,528 kB | never | 19 % | 9 % |

Table 4.9. Closure diffusion by EB size in the 1 kB window, as Table 4.7.
The "never" of the last row is 32 EBs at the reference cap whose body
never arrived at any reporting node and 11 EBs of 6,000 to 8,549
references that did.

The window carried 22 kB/s, nearly twice the loaded hours' 12 at the same
caps, with the same share of EBs certified (0.45 against 0.49): the
certified closures were simply larger, 2 MB at the median against 765 kB.
Of the failures, 58 % are attributed to the unobserved weight, 18 % are
EBs for which no vote was heard anywhere, 31 of those 35 being the
small-transaction EBs of 6,000 references and up, and 9 % the forger's
side.

## 4.4 Across the sets

Read down the three sets, the ladders say that the chain delivers its
parameter ceiling, less the chain's own spacing and the load's shortfall,
as long as the EBs validate inside the window: 81 to 87 % of the ceiling at
260 kB on both populations, and nothing lost to voting. From 555 kB
closures of small transactions upward, the voting rung takes a growing
share: 31 % on the cluster at 2,777 transactions, 46 % at 2,673 two-input
transactions, half or more on the testnet at 4,000 and above, where the
operator hardware spreads the validation time over a factor of four. In
every case the stage table puts the loss in the same two rows, validation
after the closure and the tally reaching the quorum at the deadline; the
closure's diffusion adds to it only on the testnet at 2 MB, on the
smallest EBs and on the largest, as section 8.1 reads per vote. The
quantity that moves between the sets is the validation work of an EB on a
host, in transactions and their shape, which section 6 measures per host,
and the quorum's margin, which the unobserved and the slow weight spend
together.

# 5. Leios on Praos

Leios leaves the Praos block in place and adds work to one kind of it: the
RB that carries a certificate makes a closure of transactions part of the
ledger, and no node can validate that RB, or build on it, without that
closure applied to its ledger state. Section 2.1 put this stage last in
the pipeline because it is the one place where Leios can cost Praos
something, and this section measures what it cost on the runs of
section 3. Two comparisons are made. Within each run, the certifying RB is
set against the full plain RB of the same nodes and the same hour, which
isolates the certificate's cost from the hour's load. Across runs, the
benchmarking team's Praos control, a release node on the same cluster and
workload, says where the Leios node's Praos path stood before any
certificate is involved. The tables are regenerated by
`scripts/praos_table.py`.

## 5.1 What is expected

A Praos block that arrives late does not cost a slot: the leader of the
next slot forges regardless, on whatever chain it holds. If that leader
has not adopted the previous block within the one second between the two
slots, it builds on the block before, the two RBs compete at the same
height, and the tiebreak orphans one of them. The cost of a slow block is
therefore a fork, not a missed slot, and the measure of it is the share of
consecutive-slot leader pairs that fork, together with the delay at which
the nodes adopt each kind of RB. Chain density, the RBs on the chain per
slot, falls by the orphans and by nothing else as long as every leader
forges.

Under load the full plain RB already takes most of that second: the
testnet's reporting hosts adopt a full 88 kB block about 1.1 s after its
slot, and so does the cluster, with a third of the adoptions inside the
slot. A certifying RB adds two steps on top of that path. The forger
resolves the closure and applies it before it can forge; each adopter
reapplies the closure inside chain selection. Both grow with the
transaction count of the closure, as the validation stage of section 4
does, and neither is paid by a plain RB. The expectation is therefore that
a certifying RB is adopted later than a full plain one by an amount that
grows with the closure, that consecutive-slot pairs fork more often when
the first RB certifies, that no leader slot is missed, and that the chain's
density falls by the forks.

## 5.2 The RBs that were compared

Under load nearly every RB announces an EB, and a certifying RB carries no
transactions of its own on either population (about 1 kB, header and
certificate), so the four possible kinds of RB reduce to two that matter:
the RB that certifies and announces, and the full plain RB that announces.
Table 5.1 gives the counts.

| window | certifies, announces | certifies, no EB | plain, announces: full / partial / small | plain, no EB: full / partial / small |
|---|---|---|---|---|
| cluster 40 kB / 260 kB, 200 B | 1,539 | 0 | 1,521 / 0 / 0 | 0 / 1 / 22 |
| testnet 40 kB / 260 kB, loaded hours | 527 | 2 | 331 / 22 / 55 | 0 / 5 / 2 |
| cluster 100 kB / 1 MB, 200 B | 1,128 | 0 | 1,916 / 0 / 0 | 0 / 0 / 35 |
| cluster 100 kB / 1 MB, 374 B | 820 | 0 | 2,125 / 0 / 0 | 0 / 1 / 22 |
| testnet 308 kB / 2 MB, loaded hours | 1,014 | 17 | 2,275 / 37 / 147 | 2 / 25 / 19 |
| testnet 308 kB / 2 MB, 1 kB transactions | 159 | 2 | 441 / 10 / 24 | 0 / 0 / 0 |

Table 5.1. RBs on the chain by kind, from the chain of each window. A
plain RB is full from 80 kB (the limit is 90,112 B), small under 20 kB,
partial between. A full plain RB that announces nothing is as rare as the
mempool makes it: with enough transactions to fill the RB there are enough
to announce an EB. The rows that follow compare the first column with the
full plain announcing RBs; the other kinds are too few to read and are
left out.

## 5.3 Adoption within a run

For each reporting node and each RB on the chain, the delay from the RB's
slot to the node's adoption of it; Table 5.2 gives the median and the 90th
percentile over all (node, RB) pairs and the share adopted within the
slot, for the certifying RB at the set's closure and for the full plain
RB of the same window.

| window | certifying RB (closure) | certifying RBs | adopted p50 / p90 | within 1 s | full plain RB, p50 / p90 | within 1 s | full plain RBs |
|---|---|---|---|---|---|---|---|
| cluster 40 kB / 260 kB, 200 B | closure 222 kB | 1,539 | 0.92 / 1.21 s | 61 % | 1.03 / 1.70 s | 46 % | 1,521 |
| testnet 40 kB / 260 kB, loaded hours | closure under 0.5 MB | 524 | 0.66 / 1.24 s | 78 % | 0.91 / 2.04 s | 58 % | 329 |
| cluster 100 kB / 1 MB, 200 B | closure 555 kB | 1,015 | 1.20 / 1.52 s | 9 % | 1.13 / 1.84 s | 31 % | 1,916 |
| cluster 100 kB / 1 MB, 374 B | closure 0.5-1 MB | 810 | 1.28 / 1.56 s | 3 % | 1.12 / 1.76 s | 32 % | 2,125 |
| testnet 308 kB / 2 MB, loaded hours | closure 1.5-2 MB | 156 | 1.57 / 2.42 s | 3 % | 1.17 / 2.49 s | 30 % | 2,185 |
| testnet 308 kB / 2 MB, 1 kB transactions | closure 1.5-2 MB | 122 | 0.62 / 1.55 s | 75 % | 0.62 / 2.12 s | 74 % | 438 |

Table 5.2. Adoption delay after the RB's slot, over all (node, RB) pairs
of the window: the cluster's 51 nodes, the testnet's reporting nodes
(Table 3.3). The certifying RB is read at the closure bin that holds the
set's typical closure; the testnet's 2 MB rows take the 1.5-2 MB bin.

At 260 kB the certifying RB is adopted earlier than a full plain one on
either population. Its body is about 1 kB against 88 kB, so it reaches
the nodes sooner (0.53 against 0.72 s on the testnet), and reapplying its
thousand already-validated transactions costs what applying the full
block's few hundred from scratch costs (0.06 s on the testnet, 0.10 and
0.11 s on the cluster), since reapplying a transaction skips the checks
its validation already made. From 555 kB closures of 200 B transactions
upward the reapply outgrows that advantage and the order reverses. On the cluster
the certifying RB's median moves from 0.92 to 1.20 and 1.28 s while the
full plain RB stays at 1.03 to 1.13 s, and the share adopted inside the
slot falls from 61 % to 9 and 3 %. On the testnet at 2 MB, the certifying
RB is adopted at 1.57 s against 1.17 s for the full plain RB, 3 % inside
the slot against 30 %. The inequality the section set out to test
therefore holds in both directions: a certified closure reapplies faster
than a full RB applies when it holds about a thousand transactions, and
slower from a few thousand up, and at 6,000 transactions it costs the
median adoption 0.4 s more than the fullest plain block.

The 1 kB window puts the cost on the transaction count rather than the
bytes: closures of 1.5 to 2 MB holding about 2,000 transactions are
adopted at 0.62 s, where closures of the same bytes holding 6,000 took
1.57 s in the loaded hours, and the full plain RB of that window is
adopted at the same 0.62 s. The window ran on a mixed node build (Table
4.8): the equality within the window, on one set of nodes and one hour,
does not depend on it, while the comparison across periods could owe
part of its difference to a change between the builds.

Where the time goes is visible on the IOG and PIR hosts' traces at 2 MB,
which time each step of the forge and adoption paths
(`scripts/forge_path.py` at the forger, the adoption-path query at the
adopters). Every forge with a loaded mempool pays 0.50 s to snapshot it,
plain or certifying, so a full plain RB leaves the forger 0.53 s after
its slot starts; resolving and applying the closure adds 0.04 to 0.19 s
as the closure grows from 0.3 to 1.9 MB, at 34 to 41 µs per transaction,
so a certifying RB at 2 MB leaves at 0.70 s. Each adopter then reapplies
the closure inside chain selection, 0.24 s at 2 MB against 0.05 s to
apply a full plain RB, and the relays forward the body before validating
it, so a hop adds its transfer and no validation. The difference between
the two kinds in Table 5.2 is the sum of those two steps.

## 5.4 Forks

A consecutive-slot leader pair is two leaders in slots s and s + 1. The
pair stays on the chain if the second leader had adopted the first RB
within the second and built on it; otherwise the two RBs compete at the
same height and one is orphaned. Table 5.3 counts the pairs of each
window, on the chain and forked, by the kind of the pair's first RB, which
is the one the second leader had to adopt.

| window | share forked among all consecutive-slot pairs | among the pairs led by a certifying RB | among the pairs led by a plain RB |
|---|---|---|---|
| cluster 40 kB / 260 kB, 200 B | 62 of 137 (45 %) | 18 of 64 (28 %) | 44 of 73 (60 %) |
| testnet 40 kB / 260 kB, loaded hours | 5 of 31 (16 %) | 1 of 10 (10 %) | 4 of 21 (19 %) |
| cluster 100 kB / 1 MB, 200 B | 122 of 173 (71 %) | 56 of 67 (84 %) | 66 of 106 (62 %) |
| cluster 100 kB / 1 MB, 374 B | 129 of 182 (71 %) | 50 of 53 (94 %) | 79 of 129 (61 %) |
| testnet 308 kB / 2 MB, loaded hours | 46 of 122 (38 %) | 22 of 43 (51 %) | 24 of 79 (30 %) |
| testnet 308 kB / 2 MB, 1 kB transactions | 5 of 25 (20 %) | 1 of 5 (20 %) | 4 of 20 (20 %) |

Table 5.3. Consecutive-slot leader pairs: the forked pairs over all the
pairs of that kind, on the chain and forked together. A forked pair is an
orphan adopted by two or more observed nodes whose competitor on the chain
sits one slot before or after it; the pair's first RB, the one the second
leader had to adopt, is read from the chain when it won and from the
orphan's fetched size when it lost (a certifying RB fetches at about
1 kB). A plain first RB is of any size here; under load nearly all of
them are full (Table 5.1). The share of all RBs orphaned is in Table 5.4.

The forked share follows the adoption delay. At 260 kB a pair whose first
RB certifies forks less often than one whose first RB is plain, on both
populations, as the certifying RB is adopted earlier. From 555 kB closures
upward the certifying first RB forks more often than the plain one, and on
the cluster, where every leader is in the same data centre and a plain
RB already forks 60 % of its pairs, 84 to 94 % of the pairs led by a
certifying RB fork. On the testnet at 2 MB the two shares are 51 % and
30 %. The plain RB's own forked share rises with the load as well, from 19
to 30 % on the testnet and 60 % on the cluster, consistent with the hosts
validating closures when the next header arrives; the pairs are too few
to separate that from the certificate's share.

Which RB of a forked pair loses differs between the populations (the
saved pairs outputs count both): on the cluster the first RB loses about
as often as the second (57 against 65 of the 122 pairs at 1 MB, the
tiebreak deciding), while on the testnet the first RB loses 44 of its 46
forked pairs. The data does not say why; it may be a difference in the
chain-selection tiebreak between the builds or the networks.

## 5.5 Missed slots and chain density

Table 5.4 gives, per window, the leader slots of the observed hosts and
how many were forged, the RBs on the chain against the count the slot
lottery would give at f = 0.05, and the orphans seen by two or more
observed nodes.

| window | observed hosts: leader slots / forged | RBs on the chain | expected at f = 0.05 (sd) | chain density | orphans seen by two or more observed hosts |
|---|---|---|---|---|---|
| cluster 40 kB / 260 kB, 200 B | all 51 nodes: 3,233 / 3,233 | 3,083 | 3,198 (1.8 %) | 0.96 | 150 |
| testnet 40 kB / 260 kB, loaded hours | 13 reporting hosts: 369 / 369 | 944 | 1,080 (3.0 %) | 0.87 | 23 |
| cluster 100 kB / 1 MB, 200 B | all 51 nodes: 3,291 / 3,291 | 3,079 | 3,203 (1.8 %) | 0.96 | 212 |
| cluster 100 kB / 1 MB, 374 B | all 51 nodes: 3,175 / 3,175 | 2,968 | 3,093 (1.8 %) | 0.96 | 207 |
| testnet 308 kB / 2 MB, loaded hours | 13 reporting hosts: 1,185 / 1,185 | 3,536 | 4,500 (1.5 %) | 0.79 | 101 |
| testnet 308 kB / 2 MB, 1 kB transactions | 13 reporting hosts: 168 / 168 | 636 | 720 (3.7 %) | 0.88 | 15 |

Table 5.4. Leader slots, RBs and chain density. Chain density is RBs on
the chain per slot over f; the expected count is f times the window's
slots, with the standard deviation of the lottery. On the testnet only the
13 IOG and PIR producers log their leader slots and only the reporting
nodes' adoptions reveal an orphan.

No observed host missed a leader slot in any window: every leader slot of
the cluster's 51 nodes and of the testnet's 13 IOG and PIR producers has
its forged RB. On the cluster, where every node is observed, the chain's
density is accounted for exactly: the lottery gave 3,233, 3,291 and 3,175
leader slots, all forged, and the orphans are the whole difference to the
chain, 4.6 % of the forged RBs at 260 kB and 6.4 to 6.5 % at 1 MB; density
sits at 0.96 on all three runs. On the testnet the chain's density in the
loaded hours is 0.87 at 260 kB and 0.79 at 2 MB, and the observed orphans
account for about 2 % of the expected count in each; the remaining gap,
10 to 19 % of the expected count, is beyond the lottery's spread and the
logs cannot attribute it. It belongs to the pools outside the 13 observed
producers, as stake that was not forging or leader slots those pools
missed, and the same periods' trickle hours show a gap of the same order,
densities of 0.87 at 260 kB, 0.83 at 2 MB and 0.94 in the 1 kB period
against 0.87, 0.79 and 0.88 loaded, so it is not read as a cost of the
load. What the testnet does show about Praos is the forks of Table 5.3
and the delays of Table 5.2.

## 5.6 The Praos control

The benchmarking team compared a Praos run of the release node against
two Leios cluster runs on the same cluster and the same value-only
workload of two-input, two-output transactions of 374 B, submitted on the
control at 12 per second to 52 machines, which fills the Praos block. The
control ran on node 11.1.1 on 2026-09-05, the Leios runs on Leios builds
of node 11.2.0.164 on 2026-10-21 and 23; the 100 kB / 1 MB run is the one
read in section 4 as the cluster 100 kB / 1 MB, 374 B run, and the
40 kB / 260 kB run at 374 B is not otherwise read in this report. Table 5.5 reproduces the figures
that bear on this section, from the team's report of 2026-10-27.

| | Praos control | Leios 40 kB / 260 kB, 374 B | Leios 100 kB / 1 MB, 374 B |
|---|---|---|---|
| node, cluster start | 11.1.1, 2026-09-05 | 11.2.0.164, 2026-10-23 | 11.2.0.164, 2026-10-21 |
| RB size, mean | 88,956 B | 42,688 B | 65,120 B |
| RBs certifying the predecessor's EB | 0 | 0.527 | 0.273 |
| height and slot battles per RB | 0.00091 | 0.00524 | 0.0218 |
| leadership to forged | 0.0008 s | 0.349 s | 0.586 s |
| slot start to header announced | 0.063 s | 0.395 s | 0.690 s |
| adopted by half the cluster | 0.61 s | 0.83 s | 1.28 s |
| adopted by 90 % of the cluster | 1.07 s | 1.14 s | 1.63 s |
| adopted by the whole cluster | 1.11 s | 1.21 s | 1.79 s |
| process CPU, share of one core | 2.4 % | 7.8 % | 22.9 % |
| kernel resident set | 8.2 GB | 11.6 GB | 12.2 GB |

Table 5.5. The benchmarking team's Praos control against its two Leios
runs, values as printed in the team's comparison (means over the run and
the cluster; the adoption rows are the time since the slot start at which
the given share of the cluster had adopted the block). The control's
blocks are all full plain blocks; the Leios runs' mean RB size is lower
because the certifying RBs carry no transactions.

Three readings. The forge path of the Leios node is slower before any
certificate: a Praos block is forged 0.001 s after the leadership check
and its header announced 0.06 s after the slot starts, while the Leios
node's plain and certifying RBs together take 0.35 and 0.59 s from
leadership to forged, which is the mempool snapshot of section 5.3, paid
on both kinds. Adoption by half the cluster takes 0.61 s on Praos against
0.83 s at 260 kB and 1.28 s at 1 MB, and by 90 % of the cluster 1.07
against 1.14 and 1.63 s; the 260 kB run, whose certifying RBs are adopted
earlier than its plain ones (Table 5.2), is 0.2 s behind the control at
the median and 0.07 s at the 90th percentile, so most of that run's gap
is the forge path, not the certificate. Height and slot battles per RB
rise from 0.0009 on the control to 0.005 at 260 kB and 0.022 at 1 MB, a
factor of 6 and 24. The
control is a single run of an older release at Praos's own load, and
these figures are read as the order of the cost, not its measure.

## 5.7 What this says and what would change it

Leios costs Praos nothing in slots and something in forks, and the
something is the time to reapply the certified closure at adoption: its
transaction count times the ledger's cost per reapplied transaction,
which on these value transactions is tens of microseconds. At a thousand
transactions the certifying RB is the faster block, at a few thousand it
is the slower one by 0.1 to 0.4 s at the median, and the consecutive-slot
pairs it leads fork accordingly, up to the whole of them on the cluster at
1 MB. A transaction mix with a higher cost per reapplied transaction moves
the crossover down in count by the same factor. Underneath both kinds the Leios node's forge path
is half a second behind the release node's on every full block, which is
the larger part of the gap at 260 kB and shared equally by plain and
certifying RBs. The certificate's own cost is two reapplications of a
closure that every voter validated at the vote window, 14 to 100 slots
before the RB arrived, so the state the certifying RB leads to was
computable in advance; an implementation that keeps the vote-time ledger
state for adoption would remove most of the certificate's share, and
section 8 takes that up with the other levers. The forge path's half
second belongs to the build measured, not to the protocol: an
implementation change can remove it (see section 9.3).

# 6. Cross-cutting explanations

Section 4 located the loss of each parameter set in two rows of its stage
table, the time the voters take to validate an EB once they hold its
closure and the time the vote tally takes to reach the quorum, and
section 5 the cost of the certifying RB at adoption. This section explains
those rows with four quantities that cut across the sets: what a
transaction costs a voter to validate, how much of each EB the voters had
already seen, how the EB reaches the nodes of each population, and what
the nodes' memory and sustained CPU are. Each is measured on the report's
own windows and runs; the models' and the ledger benchmark's figures for
the same quantities are set against these in section 7, and what could
change them in section 8. The tables are regenerated by
`scripts/cost_table.py` and `scripts/diffusion_table.py`.

## 6.1 The cost of validating a transaction

A voter validates an EB's closure transaction by transaction: the ones it
has validated before, at admission to its mempool or in an earlier EB, are
reapplied, the state update without the checks; the rest are applied in
full. The validation time of an EB is therefore the EB's transaction count
times a cost that depends on how many of them the voter had already
validated, on the transactions' shape, and on the host. Tables 6.1a to 6.1e read it
directly from the validation records: per host, on the EBs of one window,
the validation time per EB (the time after the later of the closure's
arrival and the slot plus 3 s), grouped by the share of the EB's
transactions the voter had to apply in full. The transaction count is held
fixed: each table takes the window's most common 500-transaction size
class, so that a cell compares EBs of one size and the rise along a row is
the applied share alone. The IOG and PIR hosts are shown by instance class,
the IOG producers behind their relays apart from the PIR hosts in the open
network; the operators as the median and quartile nodes of one node set.

**Table 6.1a.** testnet 40 kB / 260 kB, loaded hours (257 B, one input, no scripts): EBs of 1,000 to 1,500 transactions, the window's most common size class, 617 EBs; a cell in which a host has fewer than 30 records is marked tentative.

| validation time per EB, s (median; records in brackets) | applied share under 10 % | applied share 10 to 30 % | applied share 30 to 50 % | applied share 50 to 70 % | applied share 70 % and over |
|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current: IOG1, IOG3 | 0.09 to 0.09 (779) | 0.11 to 0.12 (177) | 0.13 to 0.18 (107) | 0.15 to 0.17 (50, tentative) | 0.17 to 0.18 (34, tentative) |
| r8id.xlarge, 4 vCPU, current: IOG2 | 0.10 (403) | 0.14 (59) | 0.14 (50) | 0.17 (36) | 0.18 (27, tentative) |
| c8id.xlarge, 4 vCPU, current: PIR1, PIR10, PIR3, PIR4, PIR8 | 0.10 to 0.11 (1614) | 0.12 to 0.14 (453) | 0.15 to 0.19 (368) | 0.17 to 0.25 (231, tentative) | 0.20 to 0.62 (210, tentative) |
| c5d.2xlarge, 8 vCPU, three older: PIR7, PIR9 | 0.16 to 0.16 (376) | 0.20 to 0.22 (207) | 0.29 to 0.30 (210) | 0.31 to 0.32 (134) | 0.37 to 0.88 (227) |
| c6id.2xlarge, 8 vCPU, two older: PIR2, PIR5, PIR6 | 0.13 to 0.17 (706) | 0.17 to 0.22 (306) | 0.25 to 0.28 (294) | 0.28 to 0.35 (187) | 0.31 to 0.44 (243) |
| operator nodes, the 51 with 20+ EBs of this size in every group, median node | 0.32 | 0.45 | 0.53 | 0.59 | 0.65 |
| lower quartile node | 0.19 | 0.25 | 0.30 | 0.32 | 0.37 |
| upper quartile node | 0.54 | 0.68 | 0.84 | 0.94 | 0.99 |

A voter that holds nine tenths of an EB of this size validates it in a
tenth of a second on the hosts and a third of a second at the median
operator node; one that holds less than a third, in 0.2 to 0.9 s on the
hosts and 0.65 s at the median operator node. Every cell is well inside
the window.

**Table 6.1b.** testnet 308 kB / 2 MB, loaded hours (247 B and 506 B, the same one-input transaction with two metadata sizes, 318 B on average, no scripts): EBs of 4,500 to 5,000 transactions, the window's most common size class, 367 EBs; a cell in which a host has fewer than 30 records is marked tentative.

| validation time per EB, s (median; records in brackets) | applied share under 10 % | applied share 10 to 30 % | applied share 30 to 50 % | applied share 50 to 70 % | applied share 70 % and over |
|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current: IOG1, IOG3 | 0.40 to 0.43 (417) | 1.22 to 1.32 (132) | 2.13 to 2.25 (93) | 2.90 to 3.18 (52, tentative) | 3.69 to 3.92 (22, tentative) |
| r8id.xlarge, 4 vCPU, current: IOG2 | 0.37 (275) | 1.35 (46) | 2.40 (25, tentative) | - | - |
| c8id.xlarge, 4 vCPU, current: PIR1, PIR10, PIR3, PIR4, PIR8 | 0.43 to 0.54 (924) | 1.31 to 1.64 (327) | 2.36 to 2.74 (244) | 3.58 to 3.71 (157, tentative) | 4.60 to 4.98 (111, tentative) |
| c5d.2xlarge, 8 vCPU, three older: PIR7, PIR9 | 0.86 to 0.92 (302) | 2.05 to 2.54 (142) | 4.05 to 4.09 (114) | 5.57 to 5.68 (73, tentative) | 7.11 to 7.95 (90) |
| c6id.2xlarge, 8 vCPU, two older: PIR2, PIR5, PIR6 | 0.66 to 0.81 (545) | 1.87 to 2.08 (196) | 3.16 to 3.44 (158) | 4.52 to 4.72 (111, tentative) | 5.43 to 5.97 (58, tentative) |
| operator nodes, the 13 with 20+ EBs of this size in every group, median node | 1.45 | 3.19 | 6.17 | 8.94 | 10.53 |
| lower quartile node | 0.95 | 2.06 | 3.69 | 5.14 | 6.57 |
| upper quartile node | 2.01 | 5.57 | 10.89 | 14.86 | 19.01 |

A voter applying a tenth of the 2 MB window's common EB validates it in
0.4 s on the current-generation hosts and 1.5 s at the median operator
node; one applying half needs 2.1 to 2.7 s on those hosts, 3.2 to 4.1 s
on the older ones and 6.2 s at the median operator node; one applying
more than two thirds, where the cells are populated, 3.7 to 8 s on the
hosts and 10.5 s at the median operator node, past the four-second
window. The upper-quartile operator node is at 11 s applying half the EB
and 19 s applying more than two thirds. The certified EBs of this class
are mostly closures in which the 506 B kind dominates (37 of 57 in the
loaded hours; 13 are pure 247 B), so this table reads the heavier mix;
section 7 separates the two kinds.

**Table 6.1c.** testnet 308 kB / 2 MB, 1 kB transactions (about 1 kB with metadata, and 235 to 260 B, mixed): EBs of 1,500 to 2,000 transactions, the window's most common size class, 178 EBs; a cell in which a host has fewer than 30 records is marked tentative.

| validation time per EB, s (median; records in brackets) | applied share under 10 % | applied share 10 to 30 % | applied share 30 to 50 % | applied share 50 to 70 % | applied share 70 % and over |
|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current: IOG1, IOG3 | 0.16 to 0.19 (151) | 0.33 to 0.34 (64) | 0.47 to 0.47 (45, tentative) | 0.46 to 0.64 (40, tentative) | 0.46 to 0.63 (28, tentative) |
| r8id.xlarge, 4 vCPU, current: IOG2 | 0.16 (74) | 0.31 (26, tentative) | 0.40 (20, tentative) | 0.38 (20, tentative) | 0.41 (23, tentative) |
| c8id.xlarge, 4 vCPU, current: PIR1, PIR10, PIR3, PIR4, PIR8 | 0.16 to 0.21 (341) | 0.29 to 0.38 (162, tentative) | 0.52 to 0.57 (121, tentative) | 0.50 to 0.79 (110, tentative) | 0.65 to 0.83 (86, tentative) |
| c5d.2xlarge, 8 vCPU, three older: PIR7, PIR9 | 0.32 to 0.34 (136) | 0.58 to 0.61 (72) | 0.79 to 0.81 (50, tentative) | 1.02 to 1.08 (34, tentative) | 0.96 to 1.54 (36, tentative) |
| c6id.2xlarge, 8 vCPU, two older: PIR2, PIR5, PIR6 | 0.27 to 0.30 (217) | 0.46 to 0.52 (94, tentative) | 0.64 to 0.75 (64, tentative) | 0.70 to 0.92 (53, tentative) | 0.65 to 1.19 (60, tentative) |
| operator nodes, the 8 with 20+ EBs of this size in every group, median node | 0.37 | 0.57 | 0.79 | 0.88 | 1.00 |
| lower quartile node | 0.34 | 0.50 | 0.70 | 0.82 | 0.81 |
| upper quartile node | 0.82 | 1.29 | 1.68 | 1.96 | 2.06 |

This window's common EBs are the closures made of the metadata
transactions (Table 4.8). A voter applying a tenth of one validates it in
0.16 to 0.34 s on the hosts and 0.37 s at the median operator node; one
applying half, in 0.4 to 0.8 s and 0.8 s; the window is seven hours and
most cells beyond a tenth applied are tentative.

**Table 6.1d.** cluster 100 kB / 1 MB, 200 B (200 B, one input, one output): EBs of 2,500 to 3,000 transactions, the window's most common size class, 1478 EBs; a cell in which a host has fewer than 30 records is marked tentative.

| validation time per EB, s (median; records in brackets) | applied share under 10 % | applied share 10 to 30 % | applied share 30 to 50 % | applied share 50 to 70 % | applied share 70 % and over |
|---|---|---|---|---|---|
| all nodes, the 51 with 20+ EBs of this size in every group, median node | 0.48 | 1.30 | 2.29 | 3.26 | 4.36 |
| lower quartile node | 0.44 | 1.26 | 2.22 | 3.20 | 4.27 |
| upper quartile node | 0.64 | 1.44 | 2.35 | 3.38 | 4.55 |

**Table 6.1e.** cluster 100 kB / 1 MB, 374 B (374 B, two inputs, two outputs): EBs of 2,500 to 3,000 transactions, the window's most common size class, 1105 EBs; a cell in which a host has fewer than 30 records is marked tentative.

| validation time per EB, s (median; records in brackets) | applied share under 10 % | applied share 10 to 30 % | applied share 30 to 50 % | applied share 50 to 70 % | applied share 70 % and over |
|---|---|---|---|---|---|
| all nodes, the 51 with 20+ EBs of this size in every group, median node | 0.84 | 2.10 | 3.88 | 5.54 | 7.43 |
| lower quartile node | 0.47 | 2.06 | 3.75 | 5.36 | 7.14 |
| upper quartile node | 0.94 | 2.22 | 3.98 | 5.70 | 7.60 |

On the cluster, where every node is the same host, the rise is a straight
line from 0.5 to 4.4 s per EB at 200 B and from 0.8 to 7.4 s at 374 B,
the last two cells of each run past the four-second window, and the
quartile nodes within a tenth of the median. The line is the content
dependence as well: the two runs differ only in the transaction, and two
inputs with two outputs cost 1.6 to 1.8 times one input with one output
at every applied share.

Tables 6.1a to 6.1e. Validation time per EB by the share of the EB the
voter had not validated before, per window, on the window's most common
EB size class. A record is one voter validating one EB, certified or not; the
applied share is the transactions it applied in full over the EB's
total. The IOG and PIR hosts' cells are the range of the hosts' medians,
with the records in brackets; a cell in which a host has fewer than 30
records is marked tentative, one with fewer than 10 on every host is left
blank. The operators' rows are the median node and the quartile nodes
across the nodes with 20 or more records in every bin, the same nodes in
every column. The cluster rows are the whole population, uniform hosts.

Across the five tables, every row rises with the applied share, on every
host and in every window, and the hosts keep one order in every window
and every column: the current-generation hosts at four vCPUs fastest
(c8id.xlarge and r8id.xlarge, 0.37 to 0.54 s on the 2 MB window's common
EB at a tenth applied), the c6id.2xlarge hosts at eight vCPUs 1.4 to 1.7
times slower, the c5d.2xlarge hosts at eight vCPUs 1.7 to 2.0 times
slower, the ratios holding at every applied share. Two things in that
order are separated by the tables. The two older generations, both at
eight capabilities, differ by 10 to 20 %, the size of one generation
step. The gap to the current generation at four capabilities is the CPU
rather than the capability count: the cluster's c5d nodes at two
capabilities pay the same per transaction as the testnet's c5d hosts at
eight (section 7.3). Within the current generation, the IOG producers with four upstream
peers sit at the fast end of the range of the PIR hosts with 90 to 160
peers, the slowest PIR host up to a quarter above them in the loaded
windows and the two ranges overlapping in the 1 kB window, so the peer
count costs the validator at most that much. The operators' nodes, whose
hardware is unknown, spread from the fastest hosts' level at the lower
quartile to two to three times the median at the upper quartile, in
every bin.

The voting path is the expensive one. The same transactions pass through
the node once more when the certifying RB is adopted, and section 5
measured that reapplication at a small fraction of what the voter pays
per transaction even when it holds nearly all of the EB; the difference is
the voting loop's own per-transaction term, measured per host in section
7 against the ledger's figures.

## 6.2 Mempool coverage

The applied share is not a property of the EB: it is the difference
between what the producer put in the EB and what each voter had validated
before the closure arrived, in its mempool or through an earlier EB, and
it decides whether the voter validates in time. Table 6.2 gives the
outcome on the cluster, where every voter is observed: the EBs that
failed to certify, by the mean share of their transactions the voters
applied in full.

| run | share of the EB's transactions the voters applied in full | EBs | fail as recorded |
|---|---|---|---|
| cluster 100 kB / 1 MB, 200 B | under 30 % | 607 | 3 % |
| cluster 100 kB / 1 MB, 200 B | 30 to 40 % | 227 | 5 % |
| cluster 100 kB / 1 MB, 200 B | 40 to 50 % | 261 | 24 % |
| cluster 100 kB / 1 MB, 200 B | 50 to 60 % | 220 | 62 % |
| cluster 100 kB / 1 MB, 200 B | 60 to 70 % | 113 | 80 % |
| cluster 100 kB / 1 MB, 200 B | 70 % and over | 200 | 96 % |
| cluster 100 kB / 1 MB, 374 B | under 30 % | 728 | 9 % |
| cluster 100 kB / 1 MB, 374 B | 30 to 40 % | 271 | 61 % |
| cluster 100 kB / 1 MB, 374 B | 40 to 50 % | 244 | 86 % |
| cluster 100 kB / 1 MB, 374 B | 50 to 60 % | 148 | 97 % |
| cluster 100 kB / 1 MB, 374 B | 60 to 70 % | 93 | 99 % |
| cluster 100 kB / 1 MB, 374 B | 70 % and over | 82 | 100 % |

Table 6.2. EBs failing to certify by the share of their transactions the
voters applied in full, the two cluster runs at 100 kB / 1 MB; an EB
fails when fewer than 39 of the 51 voters had it validated by 7 s.

An EB whose transactions most voters had already validated certifies at
either transaction size; one that is half applied fails three times in
five at 200 B and almost always at 374 B. Over all the validations of a window,
one per node and EB whether the EB certified or not, the median applied
share is 35 % on the cluster and 1 to 8 % on the testnet, where the operator
producers forge from mempools the generator fills more slowly, so the
testnet's EBs are mostly validated before the closure arrives and its
loss sits in the slow tail of hosts
and nodes rather than in coverage; the cluster's generator feeds every
node a different set of transactions, and coverage is what its runs
measure. How the load is submitted therefore sets the certification rate
as much as the hosts do, which section 8 takes up.

## 6.3 Diffusion by population

Table 6.3 counts the nodes of each population by their own 90th
percentile of the closure age, the time after the EB's slot at which
the node held every transaction.

| nodes by their own p90 of the closure age | cluster 40 kB / 260 kB, 200 B | testnet 40 kB / 260 kB, loaded hours | cluster 100 kB / 1 MB, 200 B | cluster 100 kB / 1 MB, 374 B | testnet 308 kB / 2 MB, loaded hours | testnet 308 kB / 2 MB, 1 kB transactions |
|---|---|---|---|---|---|---|
| under 2 s | 0 | 0 | 0 | 0 | 0 | 0 |
| 2 to 3 s | 34 | 71 | 0 | 0 | 14 | 35 |
| 3 to 4 s | 17 | 5 | 51 | 51 | 31 | 18 |
| 4 to 7 s | 0 | 4 | 0 | 0 | 20 | 17 |
| 7 to 15 s | 0 | 3 | 0 | 0 | 13 | 11 |
| 15 to 60 s | 0 | 0 | 0 | 0 | 11 | 4 |
| 60 s and over | 0 | 0 | 0 | 0 | 0 | 0 |
| nodes | 51 | 83 | 51 | 51 | 89 | 85 |
| median node p90 | 2.88 s | 2.53 s | 3.77 s | 3.54 s | 3.90 s | 3.26 s |
| median node never completed % | 0.0 % | 6.3 % | 0.0 % | 0.0 % | 8.1 % | 12.5 % |

Table 6.3. Nodes per bin of their own closure p90, per population; nodes
with 50 or more received EBs.

On the cluster every node holds every closure within 4 s at every set,
and the population moves as one block from 2.9 to 3.8 s as the closure
grows from 222 to 555 kB. On the testnet the body of the population moves
the same way, from 2.5 to 3.9 s at the median node, but a tail does not:
at 2 MB, 24 of 89 nodes have a p90 beyond 7 s and 11 beyond 15 s, where
the cluster has none. Table 6.4 says what the tail is, by the number of
peers that delivered each node's announcements.

| window | peers delivering the node's announcements | nodes | closure p90, median node | closure p90, 90th-percentile node | body p90, median node | never completed, median node | vote rate, median node | vote rate, 10th-percentile node | share of the committee's weight |
|---|---|---|---|---|---|---|---|---|---|
| testnet 40 kB / 260 kB, loaded hours | 1 upstream peer | 18 | 3.00 s | 7.31 s | 2.38 s | 6.3 % | 92 % | 68 % | 0.10 |
| testnet 40 kB / 260 kB, loaded hours | 2 to 3 | 13 | 2.63 s | 2.85 s | 2.02 s | 6.2 % | 93 % | 93 % | 0.07 |
| testnet 40 kB / 260 kB, loaded hours | 4 to 10 | 3 | 2.36 s | 2.40 s | 1.87 s | 6.7 % | 93 % | 92 % | 0.27 |
| testnet 40 kB / 260 kB, loaded hours | 11 to 30 | 4 | 2.34 s | 2.41 s | 1.95 s | 6.1 % | 93 % | 93 % | 0.02 |
| testnet 40 kB / 260 kB, loaded hours | 31 and more | 45 | 2.37 s | 2.79 s | 2.00 s | 6.3 % | 93 % | 84 % | 0.28 |
| testnet 308 kB / 2 MB, loaded hours | 1 upstream peer | 20 | 9.30 s | 19.23 s | 5.10 s | 4.7 % | 51 % | 21 % | 0.10 |
| testnet 308 kB / 2 MB, loaded hours | 2 to 3 | 13 | 4.33 s | 4.40 s | 3.11 s | 4.7 % | 84 % | 84 % | 0.06 |
| testnet 308 kB / 2 MB, loaded hours | 4 to 10 | 3 | 3.02 s | 3.11 s | 2.65 s | 8.4 % | 90 % | 90 % | 0.21 |
| testnet 308 kB / 2 MB, loaded hours | 11 to 30 | 1 | 3.25 s | 3.25 s | 2.81 s | 10.4 % | 76 % | 76 % | 0.01 |
| testnet 308 kB / 2 MB, loaded hours | 31 and more | 52 | 3.38 s | 11.44 s | 2.90 s | 11.9 % | 74 % | 23 % | 0.25 |
| testnet 308 kB / 2 MB, 1 kB transactions | 1 upstream peer | 23 | 5.87 s | 15.20 s | 3.44 s | 12.7 % | 69 % | 22 % | 0.11 |
| testnet 308 kB / 2 MB, 1 kB transactions | 2 to 3 | 13 | 4.68 s | 4.76 s | 2.34 s | 12.6 % | 77 % | 76 % | 0.06 |
| testnet 308 kB / 2 MB, 1 kB transactions | 4 to 10 | 3 | 2.93 s | 3.00 s | 2.21 s | 13.5 % | 80 % | 80 % | 0.20 |
| testnet 308 kB / 2 MB, 1 kB transactions | 11 to 30 | 4 | 2.87 s | 3.01 s | 2.21 s | 12.6 % | 79 % | 75 % | 0.02 |
| testnet 308 kB / 2 MB, 1 kB transactions | 31 and more | 42 | 2.87 s | 5.72 s | 2.25 s | 12.5 % | 79 % | 56 % | 0.20 |

Table 6.4. The testnet's nodes grouped by the number of peers that
delivered their EB announcements in the window, with the group's closure
and body p90 at its median node, its never-completed share at the median
node, its vote rate at the median node and at the 10th-percentile node,
and the share of the committee's weight its pools hold. For the IOG and
PIR hosts the delivering peer is not in the records the table is built
from; their counts come from the monitoring's per-peer announcement
events: each IOG producer has four upstream peers, its three relays and
one relay of the networking team that is a peer of all three producers
and announces nearly every EB to them; the PIR hosts, in the open
network, have 91 to 164.

Two tails, of different kinds. The producers fed by a single relay, a
fifth of the nodes and a tenth of the committee's weight, are the one
group whose closure time grows with the closure: half a second behind the
others at 260 kB, six seconds at 2 MB, three in the 1 kB window, with the
body late as well, and they vote on half the EBs at 2 MB where the other
groups vote on two thirds or more, their tail node on a fifth. Their
limit is the one relay that is their whole supply, and section 8's two
diffusion levers, forwarding the closure as it arrives and scheduling
what a relay sends, are aimed at them. Nodes with two or more upstream
peers show no size dependence at the median node, 2.3 s at 260 kB and
3.4 at 2 MB whether they have 3 peers or 40, so the network as a whole
was not short of bandwidth at these loads; but the largest group has a
tail of its own, its 90th-percentile node at 11 s and its 10th-percentile
node voting on a quarter of the EBs at 2 MB, as low as the single-relay
group's. The second tail is of that kind: a single node with about a
hundred upstream peers whose closure time also follows the bytes (2.6 s
at 260 kB, 19 s at 2 MB) and whose process averages 0.7 of a core over
whole minutes against 0.2 for the median node, a node saturated by what a
hundred peers send it, which no diffusion lever addresses and fewer peers
would.

## 6.4 Memory and sustained CPU

Memory and sustained CPU come from the nodes' own metrics, which average
over a minute (the testnet) or a second (the cluster) and across all
cores, so they show the sustained load and the memory and not whether a
core was saturated during a validation; Table 6.5 gives them per
population.

| population | nodes | resident set at the node's peak, GB: p10 / median / p90 / max | GC live data at the peak, GB, median node | process CPU, cores, median node's median interval | GC share, median node |
|---|---|---|---|---|---|
| cluster 40 kB / 260 kB, 200 B | 51 | 12.5 / 12.9 / 13.3 / 13.5 | 9.0 | 0.10 | 0.10 |
| testnet 40 kB / 260 kB, loaded hours (operator nodes) | 81 | 1.1 / 1.5 / 3.4 / 18.3 | 0.8 | 0.12 | 0.02 |
| cluster 100 kB / 1 MB, 200 B | 51 | 13.4 / 13.8 / 14.3 / 14.4 | 9.4 | 0.22 | 0.08 |
| cluster 100 kB / 1 MB, 374 B | 51 | 13.6 / 14.1 / 14.5 / 14.7 | 9.4 | 0.23 | 0.08 |
| testnet 308 kB / 2 MB, loaded hours (operator nodes) | 90 | 1.6 / 2.5 / 6.8 / 20.8 | 1.0 | 0.20 | 0.03 |
| testnet 308 kB / 2 MB, 1 kB transactions (operator nodes) | 89 | 1.4 / 2.1 / 5.5 / 18.8 | 0.9 | 0.31 | 0.03 |

Table 6.5. Memory and CPU per population: the node's resident set at its
peak sample, the GC live data, the process CPU as cores over the sampling
interval, and the GC share of the process CPU time. The IOG and PIR hosts
over the 2 MB window: resident set 1.7 to 2.2 GB at the median and 1.9 to
3.5 at the peak on hosts of 8 to 33 GB, 0.08 to 0.18 cores; the nodes
above the operators' 90th percentile are operator nodes.

Leios's own working set at 2 MB closures is a couple of gigabytes on both
testnet populations, with the operators' spread from 1.6 to 6.8 GB at the
tenth and ninetieth percentiles and a few nodes far above. The cluster is
the figure that bears on a mainnet node: its synthetic ledger is
mainnet-sized, a million delegations and four million stuffed UTxO
entries held in memory, and its nodes sit at 13.8 GB resident, 9.4 GB of
live data, on hosts of 15.2 GiB; the testnet's ledger is small and says
nothing about that. Sustained CPU is 0.2 of a core at the median node of
every population, and the host series of the IOG and PIR hosts show them
4 to 8 % busy; the saturation that matters, one core for the seconds of a
validation, is below these series' resolution and is measured by the
validation times of Tables 6.1a to 6.1e instead.

Three things the metrics leave unexplained. A tenth of the operator nodes sit above 6 GB
resident, up to 21 GB, with nothing in the data to account for it. Three
PIR hosts show five-minute peaks of the host CPU near full busy that the
node's own counter does not, so that load is not the node's. The
operators' host memory is not scraped, so their resident set has no RAM
figure to be read against.

# 7. Models against measurements: DeltaQ and the CIP cost model

Section 6 measured what a voter pays to validate an EB on the report's
populations. Two other sources put a figure on the same work: the ledger
benchmark the operators ran on their own machines, and the two models the
proposal rests on, the DeltaQ model of certification and the CIP's cost
model. This section sets the three against each other on one quantity,
the cost of one transaction, on both paths the node runs it through: the
voting path, where the voter validates the closure before the vote, and
the adoption path, where the certified closure is applied to the chain.
None of the three sources exercises a script: every transaction measured
here, on the benchmark, the testnet and the cluster, is a value transfer
without Plutus, and the models' constants are read with that in mind.
Section 7.1 gives the benchmark, 7.2 and 7.3 the measurements on the
testnet and the cluster, 7.4 sets the two against the benchmark path by
path, and 7.5 and 7.6 read the CIP's and the DeltaQ model's constants
against the result. The tables are regenerated by
`scripts/benchmark_table.py` and `scripts/cost_table.py`.

## 7.1 The ledger benchmark

The benchmark is the ledger-operations mode of
[db-analyser](https://ouroboros-consensus.cardano.intersectmbo.org/docs/references/consensus_tools#db-analyser),
the consensus layer's chain-database tool, run by 26 operators and the
benchmarking team on their own machines over one chain fragment of
768 kB blocks holding 2,086 transactions each, about 368 B per
transaction with two inputs, two outputs and one signature, every
transaction spending outputs of earlier blocks and none chaining within
its block, replayed with the UTxO set in memory and again on disk. It times the ledger's
block application: applying a block in full, with every check, and
reapplying it, the state update alone, which is the work the node does on
the adoption path for a certified closure. It does not run the voting
loop, and whether the machines were idle during the run is not recorded.
Table 7.1 gives the steady-state medians by processor model, every cost
in microseconds per transaction.

| processor (machines); every cost in microseconds per transaction | apply, on disk | apply, in memory | reapply, in memory | reapply, on disk |
|---|---|---|---|---|
| AMD EPYC 4584PX 16-Core (2) | 118 to 130 | 84 to 93 | 23 to 26 | 55 to 68 |
| 12th Gen Intel Core i7-1260P (1) | 102 | 100 | 24 | 39 |
| AMD Ryzen 9 5950X 16-Core (1) | 159 | 121 | 32 | 72 |
| AMD Ryzen 9 5900X 12-Core (1) | 188 | 121 | 32 | 71 |
| AMD EPYC-Genoa (1) | 187 | 141 | 42 | 75 |
| AMD Ryzen 7 5700U (1) | 174 | 148 | 49 | 72 |
| Intel Core i7-6700 @ 3.40GHz (1) | 187 | 154 | 41 | 68 |
| not stated (the reference host) (1) | 205 | 168 | 47 | 85 |
| Intel Xeon Gold 6240 @ 2.60GHz (3) | 199 to 205 | 174 to 179 | 47 to 49 | 73 to 76 |
| AMD EPYC 7T83 64-Core (2) | 220 to 224 | 179 to 180 | 47 to 49 | 85 to 91 |
| AMD EPYC (with IBPB) (4) | 226 to 412 | 181 to 340 | 60 to 117 | 109 to 176 |
| Intel Xeon E5-2623 v3 @ 3.00GHz (1) | 327 | 203 | 60 | 196 |
| Intel Core (Broadwell, no TSX, IBRS) (2) | 542 to 634 | 227 to 300 | 74 to 94 | 289 to 295 |
| Intel Core i7-3630QM @ 2.40GHz (1) | 302 | 228 | 69 | 131 |
| AMD EPYC 3251 8-Core (1) | 290 | 265 | 81 | 113 |
| not stated (2) | 424 to 497 | 316 to 420 | 66 to 99 | 161 to 164 |
| Intel Xeon E5-2696 v2 @ 2.50GHz (1) | 553 | 346 | 104 | 307 |
| Intel Xeon Silver 4214 @ 2.20GHz (1) | 1052 | 526 | 120 | 492 |

| over the 27 machines, microseconds per transaction | min | lower quartile | median | upper quartile | max |
|---|---|---|---|---|---|
| apply, on disk | 102 | 188 | 224 | 374 | 1052 |
| apply, in memory | 84 | 151 | 180 | 294 | 526 |
| reapply, in memory | 23 | 44 | 49 | 84 | 120 |
| reapply, on disk | 39 | 72 | 91 | 162 | 492 |

Table 7.1. The ledger benchmark by processor model: the survey of
October 2026, 26 operators' machines and the benchmarking team's
reference host, db-analyser at one pin over the fragment described above,
medians of the steady state, in microseconds per transaction for apply
and reapply alike. A model's row is the range over its machines. The
columns pair each reading with its neighbour: apply on disk next to
apply in memory, then reapply in memory next to reapply on disk. The
machines' logical CPU counts and virtualisation, as they report them,
are in the expanded output of the printer
(`scripts/benchmark_table.py --full`).

The ledger's own cost of a two-input transaction spans six times across
the operators' machines, 84 to 526 µs to apply in memory with the median
machine at 180; reapply spans the same way at about a quarter of the
cost, and keeping the UTxO on disk adds from a few percent to more than
double.

One processor model of the survey matches hardware the report measures
directly. The Xeon Gold 6240 is a Cascade Lake processor, Intel's name
for its 2019 generation of server chips. The c5d.2xlarge instance type,
which PIR7 and PIR9 on the testnet and every node of the cluster run,
is built on the same generation: the cluster's nodes report Xeon
Platinum 8000 processors of Cascade Lake and of the step before it,
which shares its core. The survey's
three Xeon Gold 6240 machines apply at 174 to 179 µs, and section 7.4
sets that figure against the testnet's and the cluster's readings on
the same hardware, path by path. The Xeon Silver 4214 is of the same
generation and is the slowest machine of the survey, so the generation
alone does not fix the cost; no stated model is of the generations the
c8id, r8id and c6id hosts run, so those classes have no benchmark
figure.

The operators who ran the benchmark are part of the population of
section 3's testnet, 26 of its operators, so Table 7.1 shows on the
ledger alone the kind of spread the operator rows of section 6 carry.

## 7.2 What the node pays at the vote

The voter's cost per transaction is read from the same validation records
as Tables 6.1a to 6.1e, one host validating one EB, on the EBs of one
size class. An EB of which the host applied no transaction, because it
had validated them all before, gives the cost per reapplied transaction:
the validation time over the transaction count. An EB of which it
applied half or more gives the cost per applied transaction: the time
net of the reapplied transactions at that rate, over the applied count.
Each reading is the median over the host's EBs, and the tables give the
number of EBs behind each one.

The testnet's load needs a word before the tables, because the tables
split it. Section 3 described the load as the output of two generators.
Both submit the same one-input, one-output value transfer, with the
metadata that gives each window its transaction sizes, and they differ
in what they do with a transaction's outputs. The first reuses them as
soon as it has submitted the transaction, so chains of dependent
transactions build up in its mempool and land in one EB together; most
of its transactions spend an output created in the same block. The
second waits until the transaction is confirmed two blocks deep, then
puts its outputs at the back of a queue of funding inputs, so its
outputs are spent only once they are on the chain and never in the
block that creates them. The chain shows closures of both kinds in
every window.

The measurements put the voter's cost per applied transaction on that
difference and not on the transaction's size: the 1 kB window's 1,024 B transaction,
four times the bytes of the 247 B one, applies at the same rate once
its closures are grouped by kind. Furthermore, within closures of the
247 B transaction alone the cost falls step by step as the share of
same-block inputs rises; both readings are given after the tables. The tables therefore split the certified closures in two
groups: chained closures, in which 80 % or more of the transactions
spend an output of the same EB, and old-input closures, in which half
or fewer do; the closures in between are left out. The two lines (80 % and half) are where the closures fall into two
clear groups and each group keeps enough EBs to measure on; the 50 % line
understates the old-input cost a little on some hosts, but no placement
of the lines closes the gap perfectly.

**Table 7.2a.** testnet 40 kB / 260 kB, loaded hours (257 B, one input, no scripts): EBs of 1,000 to 1,499 transactions: chained closures, certified closures in which 80 % or more of the inputs spend an output of the same block, 147 EBs; old-input closures, certified closures in which 50 % or less of the inputs spend an output of the same block, 156 EBs; a host cell resting on fewer than 10 EBs reads too few.

| host class (instance, vCPU, generation) | hosts | chained closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | old-input closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) |
|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current (IOG) | IOG1, IOG3 | 0.16 to 0.17 (16 to 21) | 79 to 84 (62 to 67) | too few EBs | 88 to 91 (107 to 144) |
| r8id.xlarge, 4 vCPU, current (IOG) | IOG2 | 0.20 (33) | 92 (60) | too few EBs | 98 (131) |
| c8id.xlarge, 4 vCPU, current (PIR) | PIR1, PIR10, PIR3, PIR4, PIR8 | 0.18 to 0.24 (19 to 35) | 82 to 93 (32 to 69) | too few EBs | 91 to 109 (73 to 145) |
| c6id.2xlarge, 8 vCPU, two older (PIR) | PIR2, PIR5, PIR6 | 0.27 to 0.34 (28 to 60) | 116 to 153 (20 to 55) | 0.69 to 0.81 (14 to 53) | 126 to 163 (46 to 120) |
| c5d.2xlarge, 8 vCPU, three older (PIR) | PIR7, PIR9 | 0.33 to 0.37 (54 to 71) | 135 to 141 (15 to 21) | 0.65 to 1.01 (31 to 36) | 147 to 148 (48 to 94) |
| operators (21 nodes with enough EBs under both selections): lower quartile / median / upper quartile node |  | 0.41 / 0.90 / 1.19 | 242 / 494 / 642 | 0.99 / 1.77 / 2.69 | 226 / 508 / 669 |

**Table 7.2b.** testnet 308 kB / 2 MB, loaded hours (247 B and 506 B, the same one-input transaction with two metadata sizes, 318 B on average, no scripts): EBs of 2,000 to 4,999 transactions: chained closures, certified closures in which 80 % or more of the inputs spend an output of the same block, 263 EBs; old-input closures, certified closures in which 50 % or less of the inputs spend an output of the same block, 179 EBs; a host cell resting on fewer than 10 EBs reads too few.

| host class (instance, vCPU, generation) | hosts | chained closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | old-input closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) |
|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current (IOG) | IOG1, IOG3 | 0.18 (25 to 39) | 79 to 81 (153 to 166) | too few EBs | 78 to 79 (101 to 134) |
| r8id.xlarge, 4 vCPU, current (IOG) | IOG2 | 0.19 (39) | 82 (164) | too few EBs | 78 (122) |
| c8id.xlarge, 4 vCPU, current (PIR) | PIR1, PIR10, PIR3, PIR4, PIR8 | 0.21 to 0.23 (36 to 57) | 80 to 102 (119 to 164) | too few EBs | 80 to 98 (80 to 139) |
| c6id.2xlarge, 8 vCPU, two older (PIR) | PIR2, PIR5, PIR6 | 0.31 to 0.32 (50 to 73) | 118 to 138 (108 to 152) | too few EBs | 119 to 133 (74 to 118) |
| c5d.2xlarge, 8 vCPU, three older (PIR) | PIR7, PIR9 | 0.33 to 0.37 (51 to 76) | 142 to 151 (103 to 126) | too few EBs | 147 to 151 (79 to 98) |
| operators (8 nodes with enough EBs under both selections): lower quartile / median / upper quartile node |  | 0.26 / 0.45 / 0.68 | 126 / 212 / 304 | 1.21 / 1.88 / 3.74 | 129 / 219 / 309 |

Tables 7.2a and 7.2b. The cost per transaction at the vote by host class
and input origin. A host class's cell is the range of its hosts'
medians, with the EBs behind each reading in brackets; the operators'
row is the quartile nodes over one node set, the nodes with 10 or more
EBs behind the apply reading and 20 or more behind the reapply reading
under both selections, so that its two halves compare the same nodes.
The cells that read too few, and the EBs of the class each host
validated, are in the expanded output of the printer
(`scripts/cost_table.py shape --full`); every such cell points the same
way as the cells shown.

The current-generation hosts give no old-input apply reading in either
window because an old-input closure almost never reaches them with half
or more of its transactions unvalidated: they had already validated
those transactions, through their mempools or an earlier EB, and
reapply them. The chained closures are the ones the hosts meet
unvalidated. Why the two kinds reach the hosts differently is open; the
note at the end of this subsection records it.

The reapply cost does not depend on where the inputs come from, and the
apply cost does. In the 260 kB window (Table 7.2a), where both kinds
have enough EBs on the older hosts, the c5d hosts reapply at 135 to
148 µs per transaction under both selections and apply at 0.33 to
0.37 ms on chained closures against 0.65 to 1.01 ms on old-input ones,
two to three times more; the c6id hosts and the operators' quartile
nodes repeat the pattern.

The split by input origin, and the flat reapply cost, hold on larger
EBs. In the 2 MB window (Table 7.2b), with
2,000 to 5,000 transactions per EB, the hosts' chained cost is the one
of the 260 kB window, and the same per EB size class up to 7,000
transactions (the output of `scripts/cost_table.py series`), so on
chained closures the cost per transaction does not grow with the EB.

The gap between the two kinds is there too: the operators' median node pays four times
more per applied transaction on old-input closures than on chained
ones, 1.88 against 0.45 ms. The hosts'
old-input cells rest on too few EBs; in the expanded output they point
the same way.

As said before the tables, the origin of the inputs decides the cost
within one kind as well: on closures of the 247 B transaction alone,
the apply cost falls three times from the closures with almost no
same-block inputs to the closures made of them, and the reapply cost
does not move (the within-kind output of `scripts/cost_table.py kind`).
IOG3, which keeps the UTxO set on disk, reads the same costs as IOG1 in
memory under every selection, so the difference is not a disk read.

A deployment pays the chained cost or the old-input cost according to
how its transactions are built, and this report does not settle that.
The deployment should be prepared for the costlier one, old inputs.
The chained figures are a floor: the cost the loop reaches only when a
transaction's inputs arrive in the same closure.

On the testnet the transaction kind and the path to the voters move together, since the
chaining generator submits to the hosts and the other does not, so the
two are not separated here; a run with one generator spending old
outputs and submitting to the hosts would separate them.

## 7.3 The cluster against the testnet

The cluster's nodes are c5d.2xlarge, the instance class of PIR7 and
PIR9 on the testnet, so its readings compare with those two hosts like
with like. Table 7.3 gives the cluster's readings of the two costs of
Tables 7.2a and 7.2b, on every node of each run.

**Table 7.3.** the cluster runs, c5d.2xlarge at two capabilities, every node: the lower quartile, median and upper quartile node of the run's most common EB size class.

| run | EBs | per applied transaction, milliseconds | per reapplied transaction, microseconds |
|---|---|---|---|
| cluster 40 kB / 260 kB, 200 B (200 B, one input, one output) | 1,000 to 1,499 transactions, 1,636 EBs | 0.89 / 0.91 / 0.93 | 148 / 152 / 155 |
| cluster 100 kB / 1 MB, 200 B (200 B, one input, one output) | 2,500 to 2,999 transactions, 1,478 EBs | 1.81 / 1.85 / 1.92 | 140 / 144 / 149 |
| cluster 100 kB / 1 MB, 374 B (374 B, two inputs, two outputs) | 2,500 to 2,999 transactions, 1,105 EBs | 3.28 / 3.42 / 3.49 | 158 / 163 / 166 |

Table 7.3. The cost per transaction at the vote on the cluster runs,
read as in Tables 7.2a and 7.2b: the quartile nodes of all 51 on the
run's most common EB size class. The cluster is not split by input
origin: every run is an old-input population.

The cluster's inputs are old by construction. Its generator draws on
5.5 million outputs created at genesis and reused almost none of them
by the end of any run, so nearly every input is an entry of the UTxO
set that no transaction of the run had touched: the testnet's old-input
case throughout.

The cluster confirms the testnet's old-input reading on the same
hardware. Its nodes reapply at the rate of PIR7 and PIR9, and on the
40 kB / 260 kB run they apply at 0.91 ms per transaction against the
two hosts' 0.65 to 1.01 ms on old-input closures of the same EB class
(Table 7.2a): the two hosts differ from each other more than either
differs from the cluster. The cluster's nodes run with two
capabilities, the threads the node may use, where the hosts run with
eight, and the per-transaction cost is the same: the validation of a
closure runs on one core, so the extra threads do not help it.

The cluster adds a reading the testnet cannot give: on old-input
closures the apply cost grows with the EB. Within one run it rises by
4 % at 200 B and 10 % at 374 B between the 2,000 and the 2,500 class
(the size-series output of `scripts/cost_table.py series`), where the
testnet's chained closures hold flat.

The second input costs almost as much as the first: the 374 B
transaction with two inputs applies at 3.42 ms, 1.8 times the one-input
one. Section 7.4 sets both populations against the ledger benchmark.

The node's code suggests why the old-input cost grows with the EB and
the chained one does not; section 9 measures the effect of an
optimisation of that code.

## 7.4 Two paths, two costs

A node processes the same transaction twice, on two validation paths.
On the voting path a voter validates the closure of an EB before it
votes. On the adoption path, once the EB is certified and its RB
reaches the node, chain selection applies the whole closure to the
ledger state. Sections 7.2 and 7.3 measured the voting path; section 5
timed the adoption path.

Both paths end in the same two ledger calls per transaction: apply,
which validates a transaction in full, for a transaction the node has
not validated before, and reapply, which only updates the state with
the checks skipped, for one it has. The ledger benchmark of section 7.1
times those two calls and nothing else. Each path, however, does work
of its own around the calls: it resolves the transaction's inputs,
builds the state the call runs against and keeps the books of the
closure as it goes, and the voting path does this transaction by
transaction in a loop. The report's measurements time the path as the
node runs it, that work included.

The benchmark and the measurements therefore time different things,
and the difference is the point: the benchmark gives the cost of the
ledger call alone, the lowest a path could reach, and the measurement
gives what the path costs as observed, so their ratio on the same
hardware is the path's own overhead. The survey offers that hardware
in one place: its three Xeon Gold 6240 machines are of the c5d
generation (section 7.1), so the testnet's PIR7 and PIR9 and the
cluster's nodes can be read against that row of Table 7.1.

The adoption path adds little. Section 5 timed it on the hosts'
traces: the forger and each adopter spend about 40 µs per transaction
of a 2 MB closure, and the cluster's runs adopt their certifying RBs at
69 to 114 µs per closure transaction (the adoption-path output of each
run), within a factor of two of the benchmark's reapply on the same
generation, 47 to 49 µs. The ledger benchmark therefore describes the
adoption path.

The voting path adds much more. The benchmark's transaction has two
inputs and spends outputs of earlier blocks, so the one reading of the
same shape is the cluster's two-input run (Table 7.3): there the loop
applies at nineteen times the ledger's apply and reapplies at three
times the ledger's reapply.

Everything between one and nineteen is the loop's own work around the
ledger call, and that is what makes the two figures useful together.
The loop's cost is what a voter pays per transaction today, and it
cannot fall below the ledger call inside it, so the ledger's cost is
the least the loop could ever cost. Section 8 analyses what reducing
the voting path's overhead would do for certification.

The other readings are not set against the benchmark. The testnet's
and the cluster's 200 B run are on one-input transactions, a different
shape; the comparison on the testnet's hosts would need a run of
two-input transactions that do not chain. The chained case has no
benchmark figure, and the other host classes no matching model in the
survey.

## 7.5 The CIP's cost model

The CIP's cost model, the
[compute cost estimation per node](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/cost-estimate/01-compute-cpu.md)
in the Leios repository, with its constants fitted on mainnet in the
second technical report, has two terms a voter pays. Applying a
transaction costs 0.6201 ms whatever its size, the mean CPU time of a
full apply over mainnet's blocks with their average script load folded
in. Reapplying a closure costs 0.3539 ms per EB plus 0.00002151 ms per
byte. For a transaction of the testnet's size, 318 B, in a closure of a
few thousand, that comes to 0.62 ms to apply and about 7 µs to reapply,
the per-EB constant adding a tenth of a microsecond to each. Scripts
are charged separately, 0.9487 ms per billion Plutus steps, when a
budget is modelled explicitly.

The measured apply cost brackets the model's figure. On every host
class the chained cost sits under it and the old-input cost above it,
0.65 ms and up on the testnet's older hosts and 0.91 ms and up on the
cluster, for transactions that run no script at all.

The model's reapply term describes the ledger's reapply, and it fits
the adoption path, which costs within five times it per transaction,
not the voting path, which costs ten to twenty times it. The voting
loop has no term in the model.

Two readings of the model follow. Its apply figure, read as the
ledger's cost on a mainnet mix, is exceeded by the old-input
measurements without any script. With the validation overhead of
section 7.3 removed, the voter's cost would be more in line with it
(section 9). The reapply gap would remain, so the voting path would
need a term of its own for it, with values by host class. The script
cost is unmeasured by every source here. The CIP's per-step figure is
the only number for it.

## 7.6 The DeltaQ model's inputs

The DeltaQ model of certification, the
[improved ΔQ model for Linear Leios EB diffusion](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/deltaq/improved-leios/report.md)
in the Leios repository, predicts from the voter's side whether an EB
of a given closure size certifies within the vote window. It takes
three inputs from the voter. Two are costs, 0.507 ms to apply a
transaction and 0.070 ms to reapply one, transaction-weighted means
over a mainnet block set, script costs included at their mainnet
frequency. The third is how much of the closure the
voter has to fetch and apply because it is not in its mempool: a sixth
by default, with an empirical estimate on mainnet of about 0.06. With
those inputs the model finds the voter's CPU time small next to the
fetch of the missing transactions, and certification certain at 2 MB.

Against the testnet's hosts the two costs are placed well enough. The
reapply figure is within a factor of two of every host class, and the
apply figure falls between the two measured cases, above the chained
cost and under the old-input cost on every host class with a reading.

Against the cluster, the controlled population, every input is on the
optimistic side. The model's apply, 0.507 ms, is under the cluster's
0.91 ms on the 260 kB run and 1.85 ms on the 1 MB run of the same
one-input transaction (Table 7.3); its reapply, 70 µs, is half the
cluster's; and its missing share, one sixth of the closure, is half the
32 to 38 % the cluster's voters apply at the closure (Table 4.4).

Its verdict fares the same way. The model finds certification certain
at 2 MB; the cluster certified 69 % of its full EBs with 555 kB closures
and 54 % with 1 MB closures (Table 4.3, the voting-adjusted rung).

On the testnet the missing share is the median voter's, not the
failing voter's. The median voter applies 1 to 8 % of an EB
(section 6.2), which is the model's share; the operator nodes that
apply a quarter to all of an EB are the ones past the deadline
(Tables 6.1a to 6.1e).

The model's verdict therefore holds for a voter that holds most of the
closure and pays the chained cost. The voters that decide certification
on these populations pay the old-input cost on a third to half of the
closure, a case the model's inputs do not describe.

This report's inputs to that model are the apply and reapply costs of
Tables 7.2a, 7.2b and 7.3 by host class and input origin and the
applied shares of Table 4.4 and section 6.2. A run of the model on them
is a check of the model against the populations measured: its
certification verdict per closure size set against the measured rates
of Tables 4.3 and 4.5. A second run at the chained apply cost, the voter's
cost once the overhead of section 7.3 is removed, would estimate what
that change buys (section 9).

# 8. What binds certification, and what would move it

Sections 4 to 7 measured where the testnet and the cluster stand: at
260 kB closures nearly every EB certifies, at 1 and 2 MB about half do.
Two things decide whether a voter makes the deadline. The first is the
time it spends validating the closure before it votes, which is the
larger part of the loss at 1 and 2 MB and is measured per transaction
and per host. The second is when the closure reaches it, which is the
first cause of a late vote on the testnet's smaller EBs and what remains
once the validation cost is removed. This section turns those
measurements into a statement about the protocol's feasibility: what
binds certification at the measured sizes, which of the changes
available to the implementation and the operators would move it, and by
how much, in the report's own units. The validation levers are priced by
repricing the records. The arrival levers are left open: forwarding the
closure as it arrives, scheduling what a relay sends and the number of
upstream peers each have a measured gap to close, and none has a
measured gain yet.

Section 8.1 reads the two
budgets a voter has to meet inside the vote window; 8.2 prices the two
levers the report can price, the voters' hardware and the voting loop's
own cost, by repricing the measured records; 8.3 states what the
measurements rule out as a lever; 8.4 lists the levers the report cannot
price and the questions they leave; 8.5 reads the result against the
targets of section 1. The tables are regenerated by
`scripts/cost_table.py` from the repricing outputs. Section 9 reports a
change to the loop that removes its own cost and where it has run.

## 8.1 Two budgets in one window

A voter has seven seconds from the EB's slot to vote, and it validates
the closure in the last four of them: validation starts at the 3 s mark
or when the closure arrives, whichever is later, and the vote must be
cast by 7 s (section 2). The window therefore holds two budgets. The
first is the closure's arrival: every second it takes past the 3 s mark
is a second less to validate in. The second is the validation itself,
the cost per transaction of section 7 times the share of the closure the
voter has to apply (section 6.2), plus the reapply of the rest.

Tables 8.1 and 8.2 read the two budgets per vote. For every EB and
every node that scheduled a vote on it, the record gives when the node
held the closure, when it finished validating, and whether the vote was
in time. The shares are over the voters of each EB, so a voter that
never validated the EB is counted as lost, not left out. Two sets are
shown: the testnet's 2 MB window, which 8.2 reprices, and the cluster run
with two-input transactions, which section 9 compares against the change
to the loop.

| set | EB size, txs | EBs | voters per EB | closure by 3 s / after 3 s / after 7 s or never | validation within 4 s / longer / never |
|---|---|---:|---:|---:|---:|
| testnet 308 kB / 2 MB, loaded hours | under 2,000 | 907 | 70 | 73 / 13 / 13 % | 84 / 0 / 15 % |
| testnet 308 kB / 2 MB, loaded hours | 2,000 to 4,000 | 900 | 70 | 68 / 22 / 10 % | 83 / 5 / 12 % |
| testnet 308 kB / 2 MB, loaded hours | 4,000 to 6,000 | 1,190 | 68 | 62 / 21 / 17 % | 66 / 16 / 18 % |
| testnet 308 kB / 2 MB, loaded hours | 6,000 and up | 531 | 66 | 52 / 26 / 22 % | 71 / 6 / 23 % |
| cluster 100 kB / 1 MB, 374 B | under 2,000 | 192 | 51 | 50 / 49 / 1 % | 83 / 7 / 10 % |
| cluster 100 kB / 1 MB, 374 B | 2,000 to 4,000 | 2,881 | 51 | 81 / 19 / 0 % | 65 / 33 / 2 % |

Table 8.1. Where the voters lost the EB, by EB size. The voters of an EB
are the nodes that scheduled a vote on it, and on the cluster the nodes
that accepted its announcement, the build having no vote-scheduled
event. The shares are pooled over the set's votes in the bin and each
group adds to 100 %. Closure: the time after the EB's slot at which the
node held the whole closure. Validation: the time from the later of the
closure and the 3 s mark to the validated event, as Table 4.6. EB size
in transactions, from the body hits on the testnet and the body's bytes
over 36 B per reference on the cluster.

| set | EB size, txs | EBs | voted in time / too late | late: closure arrived after 7 s / validation past 7 s / never validated | EBs with late voters over a quarter | certified, of the EBs the chain could certify |
|---|---|---:|---:|---:|---:|---:|
| testnet 308 kB / 2 MB, loaded hours | under 2,000 | 907 | 83 / 16 % | 13 / 1 / 1 % | 19 % | 77 % |
| testnet 308 kB / 2 MB, loaded hours | 2,000 to 4,000 | 900 | 79 / 19 % | 10 / 8 / 1 % | 26 % | 73 % |
| testnet 308 kB / 2 MB, loaded hours | 4,000 to 6,000 | 1,190 | 62 / 37 % | 16 / 20 / 1 % | 72 % | 26 % |
| testnet 308 kB / 2 MB, loaded hours | 6,000 and up | 531 | 65 / 34 % | 22 / 12 / 0 % | 76 % | 17 % |
| cluster 100 kB / 1 MB, 374 B | under 2,000 | 192 | 76 / 24 % | 1 / 13 / 9 % | 36 % | 68 % |
| cluster 100 kB / 1 MB, 374 B | 2,000 to 4,000 | 2,881 | 63 / 37 % | 0 / 35 / 2 % | 50 % | 51 % |

Table 8.2. The outcome of the same votes. A late vote is attributed to
one cause: the closure came after the 7 s deadline or never; the closure
was in hand and the validation finished past the deadline; the
validation never finished. The remainder to 100 % are votes rejected as
already known and, on the testnet, EBs the node found invalid, at most
2 % in any row. A voter whose chain tip moved to the next RB before it
voted is not a voter of the EB and is in neither count. An EB whose
late voters exceed a quarter of its voters cannot reach the quorum
among the reporting voters. The last column is the certified share of
the EBs whose next RB came 14 slots or more after the announcing one,
the ones the chain could certify, as section 4's tallies.

On the testnet's 2 MB window both budgets are spent, and which one
depends on the EB's size. On the EBs under 2,000 transactions nearly
every late vote is the closure's arrival: 13 % of the votes are late
because it arrived after 7 s or never, 1 % because the validation ran past the
deadline. On the EBs of 4,000 to 6,000 the validation is the larger
cause, 20 % against 16 %, and the late voters exceed the quorum's margin
on 72 % of the EBs where they did on 19 % of the small ones. The
certified share drops in step, from 77 % to 26 %. The other two rows
read the same way, with one difference on the largest EBs: there a
closure that arrives late is never validated at all, so diffusion
leads again.

On the cluster the arrival budget is partly spent and the validation
budget is where the votes are lost. No closure of the 2,000 to 4,000 EBs
arrives after the deadline, but 19 % arrive after the 3 s mark, so a
fifth of the voters start validating late. The validation itself takes
longer than its 4 s on 33 % of the votes, whenever the closure arrived,
and 35 % of the votes are late with the closure in hand, one node in
three past the deadline on the typical EB. The late voters exceed the
margin on half of the EBs. The certified share of 51 % follows.

The four sets not shown add no third pattern. At 260 kB, on the testnet
and on the cluster alike, 97 to 100 % of the votes are in time and
certification is at its ceiling. The 200 B cluster run repeats the 374 B
run with a smaller loss: no closure arrives late, 21 % of the votes are
late for validation, 69 % of the EBs certify. The 1 kB window loses the
same share of its 2,000 to 4,000 EBs to validation as the
small-transaction window, 9 % against 8 %, with four times the bytes per
transaction. That is section 7's reading once more: the count binds,
not the bytes.

When the validation budget is lifted, the arrival budget is what
remains, and 8.2 measures how much of the failure it holds once the
voters' cost is priced.

## 8.2 The levers the report can price

Two levers act on the validation budget: faster hardware at the voters,
and the removal of the voting loop's own cost. Both have a measured
price per transaction. The hardware lever's is the cost per transaction
by host class of Tables 7.2a and 7.2b. The loop lever's is the gap
between the chained and the old-input apply cost, which section 9.1
traces to one step of the loop.

To read what each lever would buy, this section reprices the recorded
validations at the lever's cost per transaction and reads the votes
again. A record is one voter validating one EB:
how many transactions it applied, how many it reapplied, and when the
closure arrived. The repricing keeps the
counts and the arrival and changes the cost per transaction, so each
voter's validation time becomes the chosen class's apply cost times the
applied count plus its reapply cost times the reapplied count. The vote
rule then says which votes are in time.

On the cluster every node is observed, so the quorum says which EBs
certify and the throughput follows.

On the testnet 40 % of the committee weight sends no logs and
cannot be repriced, so the reading stops at the votes: how
many of the reporting voters' votes are in time, and why the rest are
late. No certification rate is projected from them. The unobserved
voters run the same software on a similar spread of hardware, so either
lever moves them in the same direction as the reporting ones, and the
per-vote reading says whether a lever removes validation as a cause of
late votes or leaves it one.

The hardware lever is measured by repricing every vote at one host
class's costs, from the oldest class the report measured, c5d, to the
current generation. The apply cost taken is the class's old-input
cost, the most expensive one measured, which section 7.2 says to plan
on; so each class's row is its pessimistic case.

The loop lever is measured by repricing the same votes at the class's
chained apply cost instead, reapply unchanged. Section 9.1 traces the
gap between the two apply costs to the loop's pass over the closure's
input table, so the chained cost is the apply cost without that pass
(measurement made in section 9).

**Table 8.3a.** testnet 308 kB / 2 MB, loaded hours (247 B and 506 B, the same one-input transaction with two metadata sizes, 318 B on average, no scripts).

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 72.9 % | 10.2 % | 3.5 / 6.2 | 0.78 / 3.81 / 116.3 |
| closures as recorded, hosts at least current generation | 80.3 % | 2.8 % | 5.0 / 6.8 | 0.42 / 1.69 / 35.2 |
| old-input, current generation | 75.7 % | 7.4 % | 3.9 / 6.4 | 0.54 / 3.12 / 8.9 |
| old-input, c6id | 70.7 % | 12.4 % | 3.4 / 6.0 | 0.78 / 4.43 / 12.5 |
| old-input, c5d | 68.1 % | 15.0 % | 3.2 / 5.9 | 0.90 / 5.20 / 14.8 |
| loop's cost removed, current generation | 82.2 % | 0.9 % | 6.6 / 6.9 | 0.40 / 0.76 / 1.9 |
| loop's cost removed, c6id | 81.7 % | 1.4 % | 6.4 / 6.9 | 0.60 / 1.15 / 2.9 |
| loop's cost removed, c5d | 81.5 % | 1.6 % | 6.3 / 6.9 | 0.69 / 1.30 / 3.3 |

**Table 8.3b.** testnet 308 kB / 2 MB, 1 kB transactions (about 1 kB with metadata, and 235 to 260 B, mixed).

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 83.5 % | 8.0 % | 2.8 / 6.1 | 0.71 / 3.08 / 119.1 |
| closures as recorded, hosts at least current generation | 88.7 % | 2.7 % | 3.3 / 6.6 | 0.32 / 1.09 / 108.7 |
| old-input, current generation | 89.2 % | 2.2 % | 5.1 / 6.7 | 0.46 / 1.59 / 9.2 |
| old-input, c6id | 87.7 % | 3.8 % | 4.0 / 6.5 | 0.67 / 2.25 / 13.0 |
| old-input, c5d | 86.5 % | 4.9 % | 3.6 / 6.4 | 0.77 / 2.64 / 15.3 |
| loop's cost removed, current generation | 91.2 % | 0.3 % | 6.8 / 7.0 | 0.26 / 0.44 / 1.7 |
| loop's cost removed, c6id | 91.0 % | 0.4 % | 6.7 / 6.9 | 0.39 / 0.65 / 2.6 |
| loop's cost removed, c5d | 90.9 % | 0.5 % | 6.7 / 6.9 | 0.44 / 0.74 / 3.0 |

Tables 8.3a and 8.3b. The testnet votes repriced: 223,343 votes on
3,528 EBs from 87 nodes in the loaded hours, 42,795 on 606 EBs from 84
nodes in the 1 kB window. "As recorded" reads the recorded validation
times, Table 8.2 pooled over the window. "Closures as recorded, hosts
at least current generation" keeps each voter's recorded time and
scales down the voters slower than the current generation by the
hardware factor their reapply cost gives (section 7.2), leaving faster
voters as they were. The "old-input" rows rebuild every voter's time
from its record's counts at one host class, the current generation
(c8id, r8id), c6id or c5d: 20 ms per EB, the applied transactions at
the class's old-input apply cost and the reapplied ones at its reapply
cost (the 2 MB windows take the cluster's c5d reading of Table 7.3
scaled by the hardware factors, 1.85, 1.57 and 1.11 ms, and the reapply
costs of Table 7.2b); the "loop's cost removed" rows replace the apply
cost by the class's chained cost of Table 7.2b. "In time": the vote
cast by the deadline. "Out of time": the closure in hand by the
deadline and the vote past it, whatever the closure's arrival.
"Closure at": when those out-of-time votes' closures arrived after the
slot, which says whether they are long validations or late arrivals.
Two late shares no row moves and the table leaves out: the votes whose
closure arrived after the deadline or never, 15.0 % in the loaded hours
and 7.1 % in the 1 kB window, and the votes whose validation never
finished and so has no counts to reprice, 1.9 and 1.5 %; in 19.2 and
11.9 % of the votes the closure arrived between the 3 s mark and the
deadline, a shortened budget. "Validation": the time from the later of
the closure and the 3 s mark, over the votes; the maximum of the
recorded rows is one stalled validation.

Hardware alone removes two thirds of the validation loss. With every
voter at least at the current generation, the votes out of time fall
from 10 to 3 % on the 2 MB window, and the ones late for the closure's
arrival do not move. The 1 kB window reads the same.

The loop's cost removed takes validation out of the causes, on every
host class. On the 2 MB window the votes out of time fall from 10 % to
under 2 % at c5d as at the current generation, and no validation runs
longer than 3.3 s. The votes still out of time had their closure at
6.3 s at the median, a late arrival and not a long validation. The 1 kB
window reads the same.

**Table 8.3c.** testnet 308 kB / 2 MB, loaded hours (247 B and 506 B, the same one-input transaction with two metadata sizes, 318 B on average, no scripts), the EBs of 4,000 to 6,000 transactions.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 62.6 % | 18.8 % | 3.2 / 5.9 | 1.42 / 6.68 / 116.3 |
| closures as recorded, hosts at least current generation | 75.5 % | 5.9 % | 4.5 / 6.6 | 0.71 / 2.81 / 35.2 |
| old-input, current generation | 71.7 % | 9.7 % | 3.9 / 6.4 | 0.93 / 3.59 / 6.8 |
| old-input, c6id | 64.0 % | 17.4 % | 3.2 / 6.0 | 1.34 / 5.08 / 9.7 |
| old-input, c5d | 59.9 % | 21.5 % | 3.1 / 5.7 | 1.56 / 5.98 / 11.4 |
| loop's cost removed, current generation | 80.2 % | 1.2 % | 6.6 / 6.9 | 0.51 / 0.80 / 1.6 |
| loop's cost removed, c6id | 79.6 % | 1.8 % | 6.5 / 6.9 | 0.76 / 1.22 / 2.5 |
| loop's cost removed, c5d | 79.3 % | 2.1 % | 6.4 / 6.9 | 0.87 / 1.38 / 2.8 |

Table 8.3c. Table 8.3a on the 1,190 EBs of 4,000 to 6,000
transactions, the size at which validation becomes the first cause of a
late vote and the certified share falls (Table 8.2). Late in every row:
16.7 % of the votes for the closure's arrival, 1.9 % never validated.
The other size bins are in the saved output.

The loop's cost removed keeps validation inside its 4 s at every EB
size the window carried. Table 8.3c takes the EBs of 4,000 to 6,000
transactions, where validation is the first
cause of a late vote as recorded: 19 % of the votes out of time, the
validation at 6.7 s at the 90th percentile. With the loop's cost
removed the longest validation is 2.8 s, inside the 4 s on the oldest
class, and the 1 to 2 % still out of time had the closure at 6.4 s. The
largest EBs, 6,000 and up, read the same with the longest validation at
3.3 s.

At 260 kB neither budget binds: 97 % of the votes are in time in every
row (the per-vote output of that window).

On the cluster the same two levers read as certification and
throughput, since every node is observed. Table 8.4 gives the two
100 kB / 1 MB runs side by side: the hardware lever at two host
generations, the loop's cost removed on the run's own hosts, and a
fifth row for the lever 8.3 rules out.

| voters' speed | cluster 100 kB / 1 MB, 200 B: certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | cluster 100 kB / 1 MB, 374 B: certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 |
|---|---|---|---|---|---|---|---|---|
| as measured | 68.5 % | 12.2 | 60.8 | 6.07 / 8.10 | 51.6 % | 15.5 | 41.3 | 6.80 / 9.96 |
| hosts two generations newer (c6id) | 81.3 % | 13.7 | 68.4 | 5.65 / 7.40 | 61.0 % | 17.5 | 46.9 | 6.25 / 8.98 |
| hosts of the current generation | 97.4 % | 15.6 | 77.9 | 4.92 / 6.25 | 83.6 % | 22.5 | 60.3 | 5.36 / 7.31 |
| the loop's cost removed, on the run hosts | 99.2 % | 15.8 | 79.0 | 3.88 / 4.76 | 96.9 % | 25.5 | 68.3 | 4.09 / 4.80 |
| validation started at the closure arrival | 72.3 % | 12.6 | 63.1 | 5.74 / 8.02 | 57.2 % | 16.8 | 44.8 | 6.43 / 9.73 |

Table 8.4. The cluster records repriced on the two 100 kB / 1 MB runs, all 51 nodes
and the run's quorum of 39. Each record's validation time is split
between the two operations in proportion to the run's measured costs
(Table 7.3) and each part scaled: the hardware rows scale both by the
factors of Table 7.2 (0.85 for c6id, 0.6 for the current generation
against c5d), the row with the loop's cost removed scales the apply
part to the c5d hosts' chained cost of Table 7.2b and leaves reapply;
the last row keeps the costs and starts the validation when the closure
arrived instead of at the 3 s mark (8.3). "As measured" is the run's
certification read from the records. The quorum voter is the 39th
to validate. The 374 B run's row with the loop's cost removed uses the
one-input chained cost, since the two-input one is not measured.

The cluster says the same with no population spread. On the one-input
run, hosts of the current generation take certification from 69 to
97 %. The loop's cost removed alone, on the run's own c5d hosts, takes
it to 99 %, the run's workload ceiling (Table 4.3). The two-input run
reads 84 and 97 %.

The quorum voter, which as measured finishes at the
deadline's edge at the median and past it at the 90th percentile, has
validated by 4.8 s at the 90th percentile with the loop's cost removed.
The two seconds it no longer needs are margin for a closure arriving
later.

Table 8.5 puts the two levers together on the one-input run: the
loop's cost removed on each host generation in turn.

| voters' speed | cluster 100 kB / 1 MB, 200 B: certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 |
|---|---|---|---|---|
| as measured | 68.5 % | 12.2 | 60.8 | 6.07 / 8.10 |
| the loop's cost removed, on the run c5d hosts | 99.2 % | 15.8 | 79.0 | 3.87 / 4.75 |
| the loop's cost removed, on c6id hosts | 99.3 % | 15.8 | 79.0 | 3.78 / 4.66 |
| the loop's cost removed, on current-generation hosts | 99.4 % | 15.8 | 79.1 | 3.51 / 4.39 |

Table 8.5. The two levers combined on the one-input run: apply at each
class's chained cost and reapply at its reapply cost (Table 7.2b: 0.35
and 147 µs on c5d, 0.31 and 128 on c6id, 0.20 and 85 on the current
generation), relative to the run's 1.85 ms and 144 µs.

With the loop's cost removed, hardware buys margin rather than
certification at this EB size: the quorum voter finishes 0.4 s earlier
on current-generation hosts than on c5d. That margin is what a later
closure, a larger one, or one carrying script computation would draw
on; the script budgets of section 2.2 remain unmeasured, and this
margin is the room they would be set within. Table 8.6 sizes it in
transactions: what a voter applies in the window's 4 s, or in the 2 or
3 s a late closure leaves, at each class's apply cost, every
transaction applied and every input old.

| host class, apply cost per transaction | in 2 s | in 3 s | in 4 s |
|---|---|---|---|
| c5d, with the loop's cost (1.85 ms) | 1,100 | 1,600 | 2,200 |
| c5d, the loop's cost removed (0.35 ms) | 5,700 | 8,600 | 11,400 |
| c6id, with the loop's cost (1.57 ms) | 1,300 | 1,900 | 2,500 |
| c6id, the loop's cost removed (0.31 ms) | 6,500 | 9,700 | 12,900 |
| current generation, with the loop's cost (1.11 ms) | 1,800 | 2,700 | 3,600 |
| current generation, the loop's cost removed (0.20 ms) | 10,000 | 15,000 | 20,000 |

Table 8.6. Transactions applied per budget at each host class's apply
cost on old-input closures, the worst case, with the loop's cost (the
costs the 2 MB windows' repricing takes, Tables 7.2b and 7.3) and with
it removed (the chained cost of Table 7.2b); the budget over the cost,
rounded to hundreds. On the oldest class with the loop's cost removed
the 4 s budget covers 11,400 applied transactions against 2,200 with
it, more than the largest EB the 2 MB windows carried, and a closure
arriving at 5 s still leaves room for 5,700.

Two measured effects contribute to the voters' cost and are not levers
of the implementation. Transactions that spend outputs created in the
same EB cost a third to a half as much to apply (section 7.2), and a
voter that holds most of the closure before the EB arrives reapplies
instead of applying (section 6.2); both depend on how the load is built
and routed, not on the node, and the report plans without them. Where
they occur they are a benefit on top of the levers above, not part of
the feasibility argument.

## 8.3 What the measurements rule out

Starting validation when the closure arrives instead of at the 3 s mark
recovers little: on the cluster it moves certification from 69 to 72 %
on the one-input run and from 52 to 57 % on the two-input one
(Table 8.4, last row). The closure arrives close to the 3 s mark at most
voters, so the time gained is a fraction of a second against validation
times of three to five.

Memory and sustained CPU bind nothing at the measured sizes. The hosts'
resident set is 1.7 to 2.2 GB at the median on hosts of 8 to 33 GB, the
cluster's nodes hold a mainnet-sized ledger at 13.8 GB on hosts of
15.2 GiB without failing on memory, and the sustained CPU is 0.2 of a
core at the median node of every population (Table 6.5); what binds is
one core for the seconds of a validation, which the repricings price.

## 8.4 The levers the report cannot price

The arrival budget has levers of its own, each with a measured target
and no measured gain, so none has a row above.

Forwarding the closure as it arrives, before it is complete, and
scheduling what a relay sends are aimed at the nodes with a single
upstream relay. Their closure reaches the median such node at 9.3 s at
the 90th percentile at 2 MB, against 3 to 4.4 s for nodes with two or
more peers (Table 6.4).

The number of upstream peers is a lever in the other direction. The
node with about a hundred upstream peers sees the closure at 19 s at
2 MB and runs at 0.7 of a core, saturated by what its peers send
(section 6.3).

The EBs at the reference cap whose body reaches no reporting node are a
failure of the fetch logic that no voter speed touches (section 4.3.1).

The thread question is the largest unpriced lever on the validation
side. The validation of a closure runs on one core: the nodes' sustained
CPU is a fifth of a core (Table 6.5), and the cluster's nodes at two
capabilities pay the same per transaction as the testnet's hosts at
eight (section 7.3). Whether the loop can be parallelised is a question
about the ledger's apply, which runs transactions in sequence, and about
which of its parts, witness and signature checks among them, are
independent; the report has no measurement of it and makes no claim. A
reading of the apply path's parallelisable parts would come before any
number is put on it, and the loop in isolation (section 9.1) is where
that number could be taken without a deployment.

The closure forwarding and egress scheduling changes are the other
unpriced lever: the single-relay nodes' gap is measured and the changes
are not, so whether they recover it is a run to make.

## 8.5 What the measurements support

As far as the transactions measured here represent, the measurements
say three things about the protocol's feasibility at the sizes run.

At 260 kB closures the protocol certifies 97 % of its EBs on the testnet
as it is, with every voter class and every closure kind (section 4, and
the repricing of that window), and neither budget binds.

At 1 and 2 MB closures the validation budget binds today, and the
voting loop's own cost is the larger part of it. Removing that cost,
to the chained level the report has measured, takes the cluster from 69 to 99 %
certification at 1 MB on hosts three generations old, where the quorum
voter is then done by the middle of the window at the median.

On the testnet's 2 MB windows the same change removes validation as a
cause of late votes, from 10 % of the reporting voters' votes to under
2 % whatever the hardware.

With the loop's cost removed the closure's arrival is the constraint,
not CPU validation. On the 2 MB window the votes still late are the
closure's arrival, 15 of the 17 % late, and the levers for that are the
unpriced ones of 8.4.

In section 1's units, the cluster's 1 MB runs with the loop's cost
removed carry 16 and 26 kB/s, against a six-times target of 27 kB/s and
a ten-times target of 45 (Table 1.2). The testnet's 2 MB windows have
no repriced figure, since their reading is per vote; they stand at
their measured 12 and 22 kB/s (Table 4.5), and what a change to the
voters could add there is bounded by the closure's arrival, not by the
voters.

The comparison is in bytes per second at the measured transactions,
not at mainnet's mix. The transactions measured are one-input value
transfers without scripts. A like-for-like reading against mainnet
needs a run of mainnet-like transactions, which the report has not
made.

# 9. A change to the voting loop, and where it has run

The drafting of this report led to a review of the voting loop's code.
The source of the old-input cost section 7.3 measures was identified,
patched and measured. The patch reached one testnet host and one
cluster run when the previous sections were mostly complete, so this
section gives partial data on what section 8 claims the loop's cost
removed would buy: a preview of the patch's effect, not its assessment.
The change's effect on the testnet as a whole, and the cost a
deployment can tolerate once it is in, are left to further work.

## 9.1 The change

The voting loop carried the closure's input table inside the ledger
state and made a pass over the whole table after every applied
transaction: one entry per transaction on an old-input closure, the
heads of the chains on a chained one, and never on the reapply path,
which is why the old-input cost grows with the EB in section 7.3 and the
other two costs do not. The patch keeps the table outside the ledger
state and hands each transaction its own inputs, which removes that
pass; it is local to the loop. It is merged in
the consensus repository's Leios branch as
[commit 7b91f3619](https://github.com/IntersectMBO/ouroboros-consensus/commit/7b91f3619).
On the loop in isolation its cost per applied transaction is flat at
every closure size, at the chained level of Table 7.2b that section 8's
repricing takes.

## 9.2 One testnet host against its control

The change ran on one testnet host of the oldest class the report
measured, c5d, from the evening of 2026-11-08, with a second host of the
same class on the unchanged build as the control. Both are committee
members and validated the same EBs, so the transactions are identical
between them; the load was the one-input generator, a fifth of its
transactions padded with metadata, no scripts, as a sample of the
chain's transactions in the window confirms. Table 9.1 reads both hosts
over the 10,770 EBs announced in the 66 hours from the changed host's
restart, of which each validated about 9,500, the rest superseded by
the next RB before the vote.

| host, 2026-11-08 23:45 to 11-11 17:16 UTC | EBs validated | apply cost per transaction | reapply cost per transaction | EBs applying 500 or more with few reapplies: validation per applied transaction, p50 |
|---|---:|---:|---:|---:|
| the changed host | 9,492 | 0.34 ms | 0.20 ms | 0.36 ms |
| the control | 9,472 | 1.41 ms | 0.21 ms | 1.11 ms |
| Table 7.2b, c5d | | chained 0.35 / old-input 1.85 | 0.147 | |

Table 9.1. Each host's validation records regressed on the counts of
applied and reapplied transactions (validation time = apply cost ×
applied + reapply cost × reapplied + a constant), over the EBs it
validated in the window. The last column takes the EBs with 500 or more
applied transactions and fewer reapplied than a third of that, where the
validation is the apply cost, and divides the time by the applied count.

The changed host applies at the chained level of section 7, 0.34 to
0.36 ms per transaction on one-input transactions, and the control at
the old-input level, 1.1 to 1.4 ms, on the same transactions. Reapply
is unchanged within the noise on both.

The outcome follows the cost. Table 9.2 bins each host's EBs by the
transactions it applied.

| transactions applied in the EB | the changed host: EBs | validation p50 / p90 | per applied transaction, p50 | the control: EBs | validation p50 / p90 | per applied transaction, p50 |
|---|---:|---:|---:|---:|---:|---:|
| 100 to 500 | 1,166 | 0.37 / 0.84 s | 1.36 ms | 1,586 | 0.43 / 1.09 s | 1.68 ms |
| 500 to 1,000 | 667 | 0.55 / 1.02 s | 0.78 ms | 938 | 1.03 / 2.01 s | 1.44 ms |
| 1,000 to 2,000 | 688 | 0.83 / 1.23 s | 0.58 ms | 693 | 2.22 / 3.70 s | 1.65 ms |
| 2,000 and up | 607 | 1.32 / 2.13 s | 0.42 ms | 428 | 4.32 / 8.75 s | 1.70 ms |

Table 9.2. Validation time by applied count on the two hosts over the
window, each host binned by its own count since the two apply different
shares of the same EBs; the per-transaction figure is the validation
time over the applied count, so the reapplies are in it. The bins under
100 applied are left out, where a fixed cost and the reapplies dominate.

The changed host validated every EB of the window within 2.9 s, the
largest one, 7,983 transactions with 5,326 applied, in 2.87 s, and
voted on 9,439 of the 9,623 EBs it was to vote on. Of the 184 it
missed, 149 had their closure arrive after the deadline, and 35 had it
arrive inside the window but after 4.3 s, with the validation past the
deadline. The control missed 509 of 9,620: 141 with the closure late,
the same EBs as the changed host's within a few, and 368 with the
closure in hand and the validation past the deadline, its largest
validation 19.7 s on an EB of 8,555 transactions.

## 9.3 The cluster

The 100 kB / 1 MB run with two-input transactions of section 4.2
certified 52 % of its eligible EBs on the build of section 4, called
the unchanged build here. A new run with the same parameters, nodes
and workload was made on the changed build on 2026-11-09, over 16
hours. The changed build carries the patch of 9.1 and three weeks of
the Leios branch's own work. Tables 9.3 to 9.8 read the new run with
the instruments of sections 4, 5 and 8. The effects of these changes are
told apart at the end of this subsection.

Table 9.3 is the rerun's ladder beside the unchanged run's.

| rung, kB/s | cluster 100 kB / 1 MB, 374 B | cluster 100 kB / 1 MB, 374 B, changed build |
|---|---|---|
| parameter ceiling | 27.9 (p = 0.513) | 27.9 (p = 0.513) |
| workload ceiling | 27.9 (payload cap at 374 B/tx) | 27.9 (payload cap at 374 B/tx) |
| observed spacing | 27.6 (1 RB / 20.8 s, p = 0.533) | 27.2 (1 RB / 19.9 s, p = 0.494) |
| voting-adjusted, full | 16.9 (s_full = 0.540) | 27.0 (s_full = 0.992) |
| load-adjusted | 15.5 (announcing 0.99, EB 0.94, plain RB 0.98) | 26.6 (announcing 0.99, EB 1.00, plain RB 0.97) |
| measured | 15.5 | 26.6 |

Table 9.3. The ladder of the two-input run on the two builds, as Table
4.3. Changed build: the whole run, 2026-11-09 16:45 to 11-10 09:03 UTC,
1,446 eligible EBs, 1,434 certified, 14-slot gap. Transactions per
second at 374 B: 41.3 and 71.1.

The chain carried 26.6 kB/s against 15.5 on the unchanged build. That
is 95 % of the parameter ceiling. The voting rung no longer takes a
share: 0.992 of the full EBs certified, and every certified closure
was at the 1 MB cap. What remains between the ceiling and the chain is
the run's RB spacing.

Table 9.4 reads the stages of the pipeline on the two builds, as
section 4 does for every set.

| stage | cluster 100 kB / 1 MB, 374 B | cluster 100 kB / 1 MB, 374 B, changed build |
|---|---|---|
| body: p90 / p95; nodes with p90 under 3 s | 2.60 / 2.96 s; 100 % | 1.76 / 2.21 s; 100 % |
| closure: p90 / p95; nodes with p90 under 3 s / 7 s; not completed | 3.54 / 3.96 s; 0 % / 100 %; 0 % | 3.00 / 3.37 s; 47 % / 100 %; 0 % |
| applied share at the closure | 32 % | 43 % |
| validation, start to validated, p90 | 6.40 s, nodes' quartiles 6.12 to 6.51 | 1.14 s, nodes' quartiles 1.11 to 1.25 |
| vote tally reaches the quorum, p90 | 6.73 s, nodes' quartiles 6.71 to 6.76 | 4.55 s, nodes' quartiles 4.53 to 4.57 |
| vote rate on eligible EBs | 63 % | 99.8 % |
| quorums that became certificates | 99.6 %, 820 of 823 quorums seen | 99.6 %, 1,434 of 1,440 quorums seen |

Table 9.4. The stages of the two-input run on the two builds, as Table
4.4: all 51 nodes, equal weight.

Validation is the row that moved. It falls from 6.4 s to 1.1 s at the
90th percentile, and the nodes' spread shrinks from 0.4 s to 0.14 s.
The tally follows it, from the deadline's edge to 4.55 s. The vote rate
at the median node goes from 63 % to 99.8 %. Of the 137,053 votes
scheduled on the run, eligible EBs and superseded ones alike, 215 were
too late.

The voters applied more of each EB in full on the changed build, 43 %
against 32 %. They validated six times faster regardless.

The body and the closure also arrive earlier, by 0.8 s and 0.5 s at
the 90th percentile. That is not the patch. The attribution at the end
of this subsection says what it is.

Behind the validation row is the cost per transaction. Table 9.5 reads
it on the two builds as section 7 does.

| run | EBs | per applied transaction, milliseconds | per reapplied transaction, microseconds |
|---|---|---|---|
| cluster 100 kB / 1 MB, 374 B (374 B, two inputs, two outputs) | 2,500 to 2,999 transactions, 1,105 EBs | 3.28 / 3.42 / 3.49 | 158 / 163 / 166 |
| cluster 100 kB / 1 MB, 374 B, changed build (374 B, two inputs, two outputs) | 2,500 to 2,999 transactions, 1,421 EBs | 0.41 / 0.41 / 0.48 | 188 / 190 / 195 |

Table 9.5. The cost per transaction at the vote on the two builds, as
Table 7.3: the quartile nodes of all 51 on the run's most common EB
size class.

The apply cost on two-input transactions falls by a factor of eight,
from 3.42 to 0.41 ms at the median node.

The reapply cost rises by 15 %, from 163 to 190 µs. The patch touches
that path too: it hands every transaction its own inputs, reapplied
ones included. A cost per input would show more on these two-input
transactions than on the testnet's one-input ones, where 9.2 reads no
rise. The difference is not attributed here.

The run is also the first test of section 8's repricing. Section 8
priced this run with the loop's cost removed before the run existed
(Table 8.4). Table 9.6 sets that prediction against the outcome.

| | section 8's repricing, the loop's cost removed on the run hosts | the rerun on the changed build |
|---|---|---|
| apply cost per transaction | 0.65 ms | 0.41 ms |
| reapply cost per transaction | 163 µs | 190 µs |
| closure arrival, p90 | 3.54 s | 3.00 s |
| certification | 96.9 % | 99.2 % |
| measured, kB/s | 25.5 | 26.6 |
| quorum voter validated at, p50 / p90 | 4.09 / 4.80 s | 3.97 / 4.45 s |

Table 9.6. Section 8's repricing of the two-input run against the
rerun. The repricing row is Table 8.4's; the rerun's certification is
over its eligible EBs, its throughput Table 9.3's measured rung, and
its quorum voter the 39th voter to validate each EB, read as in
Table 8.4.

The prediction sits under the outcome on every line: by two points of
certification, by one kilobyte per second, and by a few tenths of a
second at the quorum voter. The first three rows say why. The
repricing charged apply at 0.65 ms where the run pays 0.41, the
pessimistic choice section 8 made. It held reapply where the run
pays 15 % more. And it kept the closure arrivals of the unchanged
build. The changed build moved them earlier for a reason outside the
patch.

That reason is in the Leios branch between the two builds. The
benchmarking team ran the same workload on the week 45 build without
the patch on 2026-11-06. Its report reads the forge, slot start to the
RB forged, at 30 ms at the median. The report of the 2026-11-09 run
with the patch reads the same 30 ms. On the unchanged build the forge
took 0.59 s from leadership to forged (Table 5.5).

That half second is the mempool snapshot cited on section 5.3. The branch's
mempool work merged on 2026-10-25 as
[commit 7ff142d5c](https://github.com/IntersectMBO/ouroboros-consensus/commit/7ff142d5c)
removes it. The patch does not touch the forge.

Certification did not move with the branch's work. The team's reports
count the announcements that came to carry a certificate. On the week
45 build without the patch that share is 26.0 %. With the patch it is
49.0 %, where the share of EBs eligible at all is 51 % on paper. The
unchanged build's run read 27.3 % of its RBs certifying (Table 5.5).
Three weeks of the branch left certification where it was. The patch
took it to the eligible share.

The two effects act on different stages, and they add through the one
window of 8.1. The forge change gives every voter half a second more.
The patch takes five seconds off the validation. Section 8's repricing
kept the old arrivals, so it measures the patch alone on this run:
96.9 % certification. The forge change is worth the two points above
it.

The forge change shows on the Praos side as well. Table 9.7 reads the
adoption of the certifying RB and of the full plain RB on the two
builds, as Table 5.2 does.

| window | certifying RB (closure) | certifying RBs | adopted p50 / p90 | within 1 s | full plain RB, p50 / p90 | within 1 s | full plain RBs |
|---|---|---|---|---|---|---|---|
| cluster 100 kB / 1 MB, 374 B | closure 0.5-1 MB | 810 | 1.28 / 1.56 s | 3 % | 1.12 / 1.76 s | 32 % | 2,125 |
| cluster 100 kB / 1 MB, 374 B, changed build | closure 1 MB | 1,433 | 0.51 / 0.75 s | 99 % | 0.59 / 1.17 s | 75 % | 1,493 |

Table 9.7. Adoption delay after the RB's slot on the two builds, as
Table 5.2: over all (node, RB) pairs of the run, the certifying RB read
at the closure bin that holds the run's typical closure.

The certifying RB is adopted at 0.51 s at the median on the changed
build against 1.28 s on the unchanged one. The full plain RB is
adopted at 0.59 s against 1.12 s. The team's report of the week 45
run without the patch reads the adoption of certificate-carrying
blocks at 0.51 s as well, so this gain is the branch's work too.

Table 9.8 reads the forks on the two builds, as Table 5.3 does.

| window | share forked among all consecutive-slot pairs | among the pairs led by a certifying RB | among the pairs led by a plain RB |
|---|---|---|---|
| cluster 100 kB / 1 MB, 374 B | 129 of 182 (71 %) | 50 of 53 (94 %) | 79 of 129 (61 %) |
| cluster 100 kB / 1 MB, 374 B, changed build | 19 of 142 (13 %) | 1 of 70 (1 %) | 18 of 72 (25 %) |

Table 9.8. Consecutive-slot leader pairs forked on the two builds, as
Table 5.3, by the kind of the pair's first RB.

The share of consecutive-slot pairs forked falls from 71 % to 13 %.
Among the pairs led by a certifying RB it falls from 94 % to 1 %. The
orphans on the chain halve, from 207 to 102 over the same number of
RBs. The cost to Praos that section 5 measures on the unchanged build,
the slower forge and the forks it causes, is not there on the changed
build.

## 9.4 What is not measured

The change has run on one testnet host and one cluster run. What it
does at the committee's scale is still section 8's repricing: the cost
per transaction is confirmed on one host, the votes of the committee
are not.

It has not run on a whole network at a set larger than 100 kB / 1 MB:
the cluster run is at that set, and the only host running it at
308 kB / 2 MB is the one testnet host. It has not run with
transactions of mainnet's mix, where the script's cost adds to the
input's.

The host that ran it is of the oldest class measured, so the current
generation's cost with the change is the repricing's figure and not a
reading.

Those measurements are further work.

# Appendix A. How each quantity was measured

This appendix states, for every quantity the report's tables and
figures rest on, which records it was read from, what marks its start
and its end, which records were kept or dropped, and how the result was
aggregated, so that a reviewer can judge the approach and not only the
numbers. It is written for sections 1 to 7 and grows with the sections
that follow. A.1 describes the sources and the records they hold, A.2
the conventions every entry shares, A.3 the quantities themselves, and
A.4 maps each quantity to the script or query that implements it.

## A.1 Sources and their records

**The testnet chain.** One row per RB on the final chain, from the
testnet explorer's block API: block number, slot, hash, time,
transaction count, size in bytes, whether the RB carries a certificate,
the hash and reference bytes of the EB it announces, the closure bytes
of the EB it certifies, and the vote share the explorer saw. For a
certifying RB the transaction count is the certified closure's. The cache
is refetched from the tip at each sync and a rolled-back tail is
replaced. Everything the report computes "from the chain alone" reads
this cache: the ladders, the sizes of EBs and closures, the
certification rate, the RB kinds and the pairs on the chain.

**The committee.** One seat per pool per epoch, ranked by active stake
descending with ties broken by the pool id, the seat's weight being the
pool's share of the total stake, together with the epoch's Leios
parameters (the reference and closure caps, the committee size, the
quorum threshold, the period lengths). The stake comes from the
explorer's stake distribution for the epochs up to 2026-10-27 and from a
db-sync instance from 2026-10-28, with the newest epoch common to both
recomputed and matched seat for seat before any later epoch was written.

**The operator telemetry.** An agent on each participating operator
node ships the node's event log and its metric scrapes to an archive.
The report reads one record per event: its time, its namespace, its
payload, and the pool and agent that sent it. The payload fields used are
named entry by entry in A.3. The metric scrapes give the node's build
version and revision, resident memory, CPU time and mempool content.

**The IOG monitoring.** The same node events for the 13 IOG and PIR
producers, in the IOG monitoring's log store, pulled per host and per
event family: the voting family (vote scheduled, EB validated, closure
acquired, body hits, not voted), the diffusion family (announcement
accepted, body acquired), the votes family (votes cast and votes
received with the running tally), the forge-loop events (leader, forged,
adopted, not adopted), the chain-selection and block-fetch events, and,
for the 2 MB period, the call traces of the forge loop and of chain
selection with each call's name, argument and duration. For each
testnet window the pulls are merged with the archive into one period
database in the archive's record layout, the one IOG host that also
sends to the archive being taken from the monitoring copy only, so that
every instrument reads both populations with one definition. Two
further pulls from the monitoring serve section 6 and are not merged
into the period databases: the per-peer announcement events (one event
per peer that announced an EB to the host, with the peer's connection
id), and the per-minute metric series of each host (the node's resident
memory, GC live data and CPU tick counters, and the host's CPU count,
total memory and CPU busy fraction). The hosts' instance types, vCPU
counts and CPU generations (Table 3.2) are held in a small table the
instruments read.

**The cluster runs.** The benchmarking team's archives hold every
node's traces in per-namespace tables with the node and the nanosecond
time of each event. The report rebuilds from them the two inputs the
testnet instruments take: the event records of the namespaces the
instruments read, with the node's name as pool and agent, and a chain
cache in the testnet's layout. The chain is reconstructed by taking the
highest block that became any node's tip and walking parents back to
the first block; RB sizes come from the forger's adoption event, EB
sizes and transaction counts from the EB forged event, the certificate
from the certified-and-announced event, and the closure bytes as the
transaction count times the run's transaction size (the mode of the
mempool's size increments). A plain RB's own transaction count is not
traced on the cluster and is estimated from its size.

**Mainnet.** Block headers of whole epochs from a public block API
(height, time, size, transaction count, forging pool) with each epoch's
protocol parameters, read for the congestion windows of section 1.

**The benchmarking team's comparison.** The figures of Table 5.5 are
taken as printed from the team's report of 2026-10-27, whose data
dictionary defines each of them; the report does not recompute them.

**The ledger benchmark survey.** The operators' submissions to the
ledger-operations survey of October 2026 (db-analyser at one pin over
one chain fragment, 26 operators' machines and the benchmarking team's
reference host), copied from the survey's results page with the machine
names removed: per machine the processor model, logical CPUs and
physical cores, virtualisation, the disk's write-cache mode, and the
read latency, apply and reapply costs per transaction with the UTxO set
in memory and on disk. Held as a small table the printer reads.

**db-sync.** The testnet's db-sync instance, reached through the
monitoring's data source, gives the certified closures what the chain
cache cannot: for every certifying RB of a window, the transactions it
carries with their sizes, and for every input the block in which the
spent output was created. The report keeps one row per certifying RB
(transaction count and bytes, the size percentiles and extremes, the
share of inputs spending an output of the same block and the median age
in blocks of the outputs spent); the 1 kB window's composition table of
section 4.3.1 is an earlier cut of the same query.

## A.2 Conventions

- **Slot clock.** The testnet's slot 0 is 2026-10-18 00:00 UTC and a
  slot is one second; a cluster run's slot 0 is the system start its
  nodes logged. "Age after the slot" is the event's time minus the start
  of the slot of the RB or EB concerned. The chain's block times agree
  with their slot numbers to the second in every window used (the spread
  between the two is zero). Node events carry the node's own clock; the
  diffusion ages are computed by the node itself against the slot start,
  and the adoption delays of section 5 subtract the slot start from the
  node's timestamp, so a node with a wrong clock would show as an outlier
  in both, and none did.
- **Loaded windows.** Each testnet window is the set of hours in which
  the load generator ran (Table 3.1), kept as a list of start and end
  times; an EB or RB belongs to a window by the time of its slot. Cluster
  runs are read whole. A window's transaction size (Table 3.1) is the
  bytes of its certified closures over their transaction count, the
  figure the ladder divides the byte cap by.
- **A node** is one reporting agent for one pool; one agent name can
  report for two pools and then counts twice.
- **Eligible EB.** An announced EB whose next RB on the chain is 14 or
  more slots later (15 on the cluster run of 2026-10-17, which ran with
  that gap). Only eligible EBs can be certified, and the certification
  rate is certified over eligible.
- **Certified EB.** The RB after the announcing one carries the
  certificate. **Closure** is the set of transactions the EB references;
  a node holds the closure when all of them are present.
- **Per node, then the median node.** The stage rows are computed per
  node first (a percentile or a share over that node's EBs), then
  summarised across nodes by the median and, where stated, the quartiles
  or the share of nodes clearing a deadline. Nodes with too few records
  for a percentile are left out, with the threshold given per entry.
- **Reporting coverage.** A pool is observed in a window when its own
  votes or vote refusals are in the data; the reporting weight is the
  share of the committee's weight those pools hold, computed per window
  against that window's total weight (a window that straddles an epoch
  holds two committees).
- **Percentiles** are the 90th and 95th unless stated, interpolated
  within the sorted values.

## A.3 The quantities

**Praos fullness and throughput on mainnet (section 1).** Fullness is a
block's size over the maximum block size of its epoch; a block is full
at 95 % of it. Carried bytes per second over a window is the sum of
block sizes over the window's seconds, against the Praos expectation of
the limit times the active slot coefficient. The congested windows are
found by binning blocks into hours and listing the fullest bins. Chain
density is RBs over seconds over 0.05.

**The ladder (sections 2 and 4).** All from the chain over the loaded
windows. The observed RB rate is RBs over the windows' seconds. The
announced count is RBs with an EB announcement, the eligible count those
with the gap, p observed = eligible over announced. The survival of the
mix is certified over eligible; the survival of full EBs is the same
ratio over EBs whose reference bytes are at least 99 % of the binding
capacity, which is the reference cap when the reference cap binds and
the closure cap over the transaction size when the closure cap does. The
transaction size is the certified closures' bytes over their
transactions. The load factors are the share of RBs announcing an EB,
the mean reference bytes over the binding capacity, and the mean plain
RB bytes over the 90,112 B limit. The measured rung is the certified
closures' bytes plus the plain RBs' bytes over the seconds. A rung's
transactions per second use the same quantities in transactions.

**EB and closure sizes (section 4).** From the chain: the eligible EBs'
reference bytes over 36 as a transaction count, and the certified
closures' bytes; percentiles over the window's EBs.

**Body and closure diffusion per node (section 4, two rows).** Per
node and EB, the first announcement accepted from a peer with its
announcement age, the first body acquired with its body age, and the
first closure acquired with its closure age, all ages as the node
reports them against the slot start. EBs the node forged itself are left
out, and so are pairs whose announcement age exceeds 60 s, since a node
catching up accepts old announcements and the age would then measure its
lag. Per node, over its EBs: the 90th and 95th percentiles of the body
age and of the closure age, the share of EBs with the stage complete
before 3 s and before 7 s, and the share of EBs whose closure never
arrived. Nodes with fewer than 50 EBs are dropped. The row gives the
median node's p90 and p95 and the share of nodes whose p90 is under the
deadline; "not completed" is the median node's never-arrived share.

**Applied share (section 4).** Per node and EB, the EB validated event's
counts of transactions applied in full and reapplied; per node, applied
over applied plus reapplied over all its EBs, for nodes with 100 or more
records; the row is the median node.

**Validation after the closure (section 4).** Per node and eligible EB,
the EB validated event's time minus the later of the closure's arrival
and the slot start plus 3 s (the vote window's opening), so the duration
counts only the time validation could have been running. Per node the
90th percentile over 100 or more records; the row is the median node
with the quartiles across nodes.

**Vote tally reaches the quorum (section 4).** Each vote a node receives
carries the node's running tally for the announcing RB. Per node and
eligible EB, the age after the slot at which that tally first reached
0.75 of the committee's weight (39 of 51 equal votes on the cluster).
Per node the 90th percentile over the EBs where its tally got there,
for nodes with 50 or more such EBs; the row is the median node with the
quartiles.

**Vote rate (section 4).** Per node, the EBs it received (as above) on
which it cast a vote, over the EBs it received less those it refused
because its chain tip did not announce the EB; the row is the median
node.

**Quorums that became certificates (section 4).** Over the window's
eligible EBs, those whose tally reached 0.75 at some reporting node,
and among them those the chain shows certified.

**Closure at 90 and 95 % of the nodes by EB size (section 4.3).** Per
eligible EB received by 40 or more reporting nodes (announcement age
within 60 s), the closure ages of those nodes sorted, and the age by
which 90 % and 95 % of them held the closure, a node that never
completed counting as infinite. EBs are binned by their reference count;
per bin, the median over EBs of the 90 % age, the share of EBs whose 90 %
and 95 % ages are under 7 s, and the certified closures' median bytes.
Per EB the nodes that received its body and that completed its closure
are counted as well, and the 6,000-and-up bin is split at the reference
cap, 8,550 references and up, with the median of those counts (4.3.1).
The forgers of those EBs are read by joining the window's EB
announcements to their slot leaders, fetched from db-sync, and to the
per-EB body counts: pools are grouped by whether they served the body of
every eligible EB they announced, of none, or of some, with the EBs at
the cap counted in each group.

**Validation by EB size class (section 4.3.1).** The records of the
validation entry, as for 6.1, every EB validated in the loaded hours,
binned by the EB's transaction count as the closure-tail sub-table: per
bin the
records and EBs, the median age of the closure's arrival and the share
of records with the closure in hand by the slot plus 3 s, the median
validation time after the later of the closure and the slot plus 3 s,
the median age at which the record was validated and the share validated
within 7 s of the slot. A node that never validated an EB has no record,
so the shares are of the validations that completed.

**Voter stages (section 8.1).** Per EB and per node that scheduled a
vote on it (on the cluster, per node that accepted its announcement,
the build having no vote-scheduled event), the record of the closure's
arrival, the validation and the vote's outcome, taken from the
vote-scheduled, closure-acquired, EB-validated and not-voted events over
the loaded hours; a node that refused the EB because its own chain tip
did not announce it, or found itself off the committee, is not a voter
of that EB. Each EB's shares are over its voters, so a voter that never
validated the EB counts as lost; a late vote is attributed to one cause,
the closure after the deadline or never, the validation past the
deadline, or the validation never finished. Binned by the EB's
transaction count from the body hits, or from the body's bytes at 36 B
per reference where the build has no body-hits event, with the EBs
whose late voters exceed a quarter of their voters and, from the chain
cache, the certified share of the EBs the chain could certify (the next
RB at the certification gap or beyond).

**Never-completed closures by fate (section 4).** Per node and EB heard
announced within 60 s, whether the closure and the body ever arrived,
split by what the chain did with the EB: certified, eligible but not
certified, superseded by a next RB inside the gap, or announced by an RB
that is not on the chain. Shares are of node-EB pairs over the period.

**EB classes and composition of the 1 kB window (section 4.3).** Every
eligible EB of the window classed by its reference count from the
chain; for the certified closures, the transactions of the certifying
RB from a db-sync instance with their sizes, counted as the 1 kB kind at
700 B and above and as the small kind under 400 B.

**Reporting coverage (sections 3 and 4).** As in A.2: per window, the
reporting nodes and the pools they report for, the pools in the
committee, and the share of the committee's weight held by the pools
whose votes or refusals are in the data.

**RB kinds (section 5).** From the chain: certifying or plain by the
certificate flag, announcing or not by the presence of an announced EB,
and a plain RB's fullness by its size, full from 80 kB and small under
20 kB.

**Adoption delay by RB kind (section 5).** Per node and RB on the final
chain, the node's first "added to current chain" event for that RB
minus the RB's slot start. A certifying RB is binned by the closure it
certifies, read as the closure bytes of its parent's EB; a plain RB by
its size. The figures are the median, the 90th percentile and the share
within 1 s over all node-RB pairs of the window. On the cluster the
switch-to-fork event counts as adoption too.

**Consecutive-slot pairs and forks (section 5).** On the chain, a pair
is two RBs at consecutive block heights whose slots are one apart. A
forked pair is an orphan, an RB that two or more observed nodes adopted
and that is not on the chain, whose competitor on the chain at the same
height sits exactly one slot before or after it. The pair's first RB is
the one in the earlier slot; its kind is read from the chain when it
won and, when it lost, from the orphan's size in the block-fetch
completion event, a certifying RB fetching at about 1 kB and a plain one
under load at 88 kB. Orphans adopted by a single node are left out as a
node on its own stale chain. On the cluster the orphan's size comes from
its forger's adoption event. The cluster archives also hold a resource
trace per node, one row per second with the resident set, the live
data and the cumulative CPU and GC centiseconds.

**Leader slots and chain density (section 5).** The observed hosts'
leader-slot and forged-RB events counted per window; on the testnet
only the 13 IOG and PIR producers log them. Chain density is the RBs on
the chain over the window's slots over 0.05, and the expected count is
the slots times 0.05 with the standard deviation of a Bernoulli draw.
The orphans of the pairs entry are counted per window.

**The forge path (section 5.3).** From the call traces of the three IOG
producers: for each RB the host forged that is on the chain, the
durations of the forge call and of its steps (the mempool snapshot, the
partition of the mempool, the block forging, the EB announcement),
keyed by the slot the call was made for, and the forged event's time
minus the slot start. The closure resolution step is read on all 13
hosts from the call keyed by the EB announcement it resolved, binned by
that closure's bytes, with the cost per transaction as the median
duration over the median transaction count of the bin. Medians and 90th
percentiles are pooled over the hosts' RBs in the loaded windows.

**The adoption path (section 5.3).** Per node and RB on the chain, the
block-fetch completion (body arrival), the chain-selection start (the
block popped from the queue) and the adoption, as ages after the slot
start, and the validation inside chain selection as the valid-candidate
event's time minus the popped time; on the IOG hosts that duration
equals the chain-selection call's own duration RB by RB. Medians and
90th percentiles over node-RB pairs; the cluster reads the same events
from its chain-database traces.

**Validation time by applied share (section 6.1).** The records of the
validation entry above, every EB a node validated whether it certified
or not, with the duration between 0 and 60 s and at least 100
transactions; the applied share is applied over applied plus reapplied.
The EBs are classed by their transaction count in steps of 500 and the
class holding the most distinct EBs is kept, so that every cell compares
EBs of one size. Records are binned by applied share (under 10 %, 10 to
30, 30 to 50, 50 to 70, 70 and over). For each IOG and PIR host the
median duration per bin, printed per instance class as the range of its
hosts' medians, with the records in brackets; a cell is marked tentative
when a host in it has fewer than 30 records and left blank when every
host has fewer than 10. For the operators, the nodes with 20 or more
records in every bin are kept, the same set in every column; per node
the median per bin, then the median and the quartiles across nodes. On
the cluster all 51 nodes form the one population.

**EBs failing by applied share (section 6.2).** On a cluster run, per
EB the mean over its voters of the applied share from the same records,
binned (under 30 %, then steps of 10 to 70 and over); per bin the EBs
and the share that failed to certify, an EB certifying when 39 or more
of the 51 voters had it validated by 7 s after the slot. The median
applied share quoted for a population is the median over all its
validation records.

**Nodes by their closure p90 (section 6.3).** The per-node closure
percentiles of the diffusion entry above (nodes with 50 or more EBs),
counted in bins of the node's own p90 (under 2 s, 2 to 3, 3 to 4, 4 to
7, 7 to 15, 15 to 60, 60 and over), with the median node's p90 and
never-completed share.

**Upstream-peer groups (section 6.3).** A node's upstream peers are the
distinct peers that delivered its EB announcements during the window,
counted from the peer field of its accepted-announcement events; for
the IOG and PIR hosts, whose events carry no peer, the same count is
taken from the monitoring's per-peer announcement events over the same
period. Nodes are grouped (1, 2 to 3, 4 to 10, 11 to 30, 31 and more)
and the group is described by its closure p90 at its median node and at
its 90th-percentile node, its body p90 and never-completed share at the
median node, its vote rate at the median and at the 10th-percentile
node, and the committee weight of its pools, the mean over the window's
committees of the pools' share.

**Memory and CPU (section 6.4).** Operators: from each node's metric
scrapes (about one per minute) the resident set at the node's median
and peak sample, the GC live data at its peak, the process CPU as cores
from the differences of the cumulative tick counter over intervals of
60 s or more (shorter intervals quantise), taking the node's median and
90th-percentile interval, with counters that imply more than 32 cores
dropped as a different unit, and the GC share as the positive
increments of the GC counter over those of the CPU counter; then the
distribution across nodes. IOG and PIR hosts: the same from the
monitoring's per-minute series, plus the host's total memory and its
five-minute CPU busy fraction. Cluster: the same from the per-second
resource trace.

**Node versions.** The build information metric of each node's
scrapes, per day, keeping the revision seen last on a day with an
upgrade.

**The ledger benchmark by processor (section 7.1).** The survey's rows
grouped by the processor model as reported; a model's cell is the range
over its machines, and the summary rows the minimum, quartiles, median
and maximum over all machines. The machines' logical CPU counts and
virtualisation are in the printer's expanded output.

**The cost per transaction at the vote (section 7.2).** The records of
the validation entry, as for 6.1, on the EBs of one size class and, on
the testnet, on the certified closures the db-sync rows select: by input
origin, the closures with 80 % or more of their inputs spending an
output of the same block (chained) and those with 50 % or less
(old-input), or by transaction size, the closures whose transactions all
lie in a band. A certifying RB is mapped to its EB through the chain
cache. Per host, the cost per reapplied transaction is the median over
the records in which the host applied no transaction of the closure of
the validation time over the transaction count; the cost per applied
transaction the median over the records in which it applied half or
more of the time net of the reapplied transactions at that rate, over
the applied count. Hosts are printed by instance class as the range of
their medians, with the number of EBs behind each reading in brackets;
a cell resting on fewer than 10 EBs on some host of the class reads
"too few EBs" in the report, its cost kept in the instrument's output
and the printer's expanded form; the operators' quartiles are
over one node set under both selections, the nodes with 10 or more EBs
behind the apply reading and 20 or more behind the reapply reading under
each, so that the two columns compare the same nodes. The cluster runs
(section 7.3) take the most common 500-transaction class and no
selection, every node in one population. The size series, read in the
prose of 7.2 and 7.3 and not a table of the report, repeats the
readings per EB size class on the 2 MB window with the chained closures
of 200 to 260 B transactions and on the cluster runs with the classes
they populate.

**The repricings (section 8).** Both repricings take the per-record validation
output of 6.1 and re-run the vote rule on altered validation times. On
the cluster, each record's time after its start (the later of the
closure's arrival and the 3 s mark) is split between the apply and the
reapply operations in proportion to the record's counts at the run's
measured costs (Table 7.3) and each part scaled by a factor: the
hardware factors of Table 7.2 on both, or the chained-to-old-input ratio
on the apply part alone (the loop fix); a row may start the validation
at the closure's arrival instead. A voter votes if its scaled time is
within 7 s of the EB's slot; an EB certifies with 39 voters, the run's
quorum. Per row the cluster repricing prints the time at which the
voter completing the quorum has validated (p50 and p90 over EBs) and
the EB's transactions scaled by the share of the window that voter
used, the closure arriving as it did; throughput is the ladder's
formula of 4.1 with the EB term at the certified bytes per eligible EB
and the plain-RB term at the certification share, pinned to the run's
measured figure, at the run's transaction size. On the testnet the
reporting voters hold 59 to 73 % of the committee weight and the rest
cannot be repriced, so the repricing reads the votes and projects no
certification: it takes the per-vote records of the voter stages above,
one per vote a node scheduled, and gives each a validation time per
row, the later of the closure's arrival and the 3 s mark plus a
duration. Rows: the recorded duration; every voter slower than the
current generation scaled down by the ratio of the class's to the
node's cost per reapplied transaction (the hardware factor, read on
reapply because it does not depend on the input origin; a node without
a reapply reading uses its apply cost, else is not moved); and the
pessimistic rebuild, the duration rebuilt as 20 ms plus the applied
transactions at a class's old-input apply cost and the reapplied ones
at the class's reapply cost, with the loop's cost removed as the same
rebuild at the class's chained apply cost. A vote whose closure arrived
after the deadline or never is late in every row; one whose validation
never finished has no counts and stays so. Per row and per EB size bin
it prints the votes in time, the votes out of time with the closure in
hand, when those votes' closures arrived (p50 and p90), and the
duration's p50, p90 and maximum over the votes.

**The changed host against its control (section 9.2).** From the
archived voting events of the two hosts, per host and EB the same
record as the validation pairs: the closure's arrival, the validated
time, the validation time after the later of the closure and the 3 s
mark, the applied and reapplied counts, and the vote's outcome. Per
host the least-squares fit of the validation time to the two counts
with a constant gives the apply and reapply cost per transaction, and
the EBs applying 500 or more with fewer reapplied than a third of that
give the validation time per applied transaction at the median. The
validation time by applied count bins each host's EBs by its own count,
since the two apply different shares of the same EBs. The votes are
counted over the EBs the host's chain tip still announced at the vote,
with the missed ones split by whether the closure arrived after the
deadline or the validation ran past it.

## A.4 Where each quantity is computed

The repository draws one boundary. Its inputs are the data sets of
DATA.md, each cited by source, period and checksum: the chain cache and
the committee, the period databases of the testnet windows with the IOG
monitoring merged in, the cluster runs' trace tables and reconstructed
chains, the archived monitoring pulls of the 2 MB period, and the
mainnet set. Acquiring and building them, which means reaching the
explorer, the telemetry archive, the IOG monitoring and the db-sync
instance, or transforming their raw files into those data sets, is done
outside the repository and is described in A.1, not shipped as code.
Inside the repository are the instruments, which read a data set and
write a saved output per window or run, the saved outputs themselves,
and the printers, which read the outputs and print the report's tables;
every number in a table is reproducible from the data sets by running
the instrument and then the printer. In the published copy the per-node
outputs of the testnet windows and the hosts table carry every node and
pool as a number (n1, n2, … and p1, p2, …, one number per node across
the windows) in place of the agent names, hostnames and pool ids, with
the operators' tickers emptied and the IOG and PIR labels kept; the
printers read them unchanged, and the mapping is held by the author and
available to reviewers on request.

| quantity | data set | instrument | printer |
|---|---|---|---|
| mainnet fullness, throughput, congested windows | mainnet set | `mainnet_praos.py`, `mainnet_windows.sh` | the same |
| the ladder, EB and closure sizes | chain cache, committee | the ladder and sizes computation (`ceiling`, `sizes`) | `ladder_table.py` |
| body and closure diffusion per node, vote rate | period database or cluster run, chain cache | `diffusion_nodes.py` | `stage_table.py` |
| applied share, validation after the closure | period database or cluster run | `validation_pairs.sql`, `cluster_validation_pairs.sql` | `stage_table.py` |
| vote tally reaches the quorum, quorums that became certificates | period database or cluster run, chain cache | `tally_quorum.sql`, `cluster_tally_quorum.sql` | `stage_table.py` |
| closure at 90 and 95 % of the nodes by EB size; the body and closure reach of the EBs at the reference cap | period database, chain cache | `closure_fleet.sql` | `stage_table.py`, `--classes` for the reference-cap split |
| the forgers of the EBs whose body reached no node, by pool | chain cache, the per-EB closure output, the window's slot leaders from db-sync | `eb_forgers.py` | read directly |
| validation by EB size class | the per-record validation output of a window | `validation_classes.py` | `stage_table.py --classes` |
| voter stages: where each voter lost the EB, the vote's outcome by cause, by EB size | period database or cluster run, chain cache | `voter_stages.sql`, `voter_stages.py` | `stage_table.py --voters` |
| never-completed closures by fate | period database, chain cache | `closure_never.sql` | read directly |
| reporting coverage | period database, committee | the voters table of the causes pass | `stage_table.py` |
| EB classes and composition of the 1 kB window | chain cache; the db-sync result as a saved output | `eb_composition.py` (chain half) | the same |
| RB kinds, leader slots and chain density | chain cache, the adoption and pairs outputs | | `praos_table.py` |
| adoption delay by RB kind | period database or cluster run, chain cache | `adoption_delay.sql`, `cluster_adoption.sql` | `praos_table.py` |
| consecutive-slot pairs and forks | period database or cluster run, chain cache | `consecutive_pairs.sql`, `cluster_forks.sql` | `praos_table.py` |
| the forge path | archived monitoring pulls, chain cache | `forge_path.py` | `praos_table.py` |
| the adoption path | period database or cluster run, chain cache | `adoption_path.sql`, `cluster_adoption_path.sql` | `praos_table.py` |
| the Praos control | the team's report | | `praos_table.py`, typed constants |
| validation time by applied share | the per-record validation output of a window or run, the hosts table | `validation_bins.py` | `cost_table.py bins` |
| EBs failing by applied share; the cluster records repriced on faster hosts and with the loop's cost removed | the per-record validation output of a cluster run, its ladder export | `host_speed.py` | `cost_table.py unseen`, `speed`, `combined` |
| the testnet votes repriced by host class, the pessimistic rebuild and the loop's cost removed, per vote and per EB size bin | the per-vote records of a window, the hosts table | `voter_reprice.py` | `cost_table.py votes` |
| the changed host against its control: the costs per transaction, the validation time by applied count, the votes cast and missed | the archived voting events of the four hosts | `loop_hosts.py` | the same |
| nodes by their closure p90, upstream-peer groups | the per-node diffusion outputs, the voters table; the archived per-peer announcement pulls | `diffusion_bins.py`, `peers_upstream.py` | `diffusion_table.py bins`, `upstream` |
| memory and CPU | the period database's metrics, the archived monitoring series, the cluster's resource trace; the hosts table | `resources.py` | `cost_table.py resources` |
| node versions | the period database's metrics | the node-versions query | read directly |
| the ledger benchmark by processor | the survey table | | `benchmark_table.py` |
| the cost per transaction at the vote, the size series | the per-record validation output of a window or run, the hosts table; the db-sync composition rows and the chain cache (testnet) | `validation_shape.py` | `cost_table.py shape`, `series` |
