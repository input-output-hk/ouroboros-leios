# 2. What is assessed and what to expect

This section describes the Leios pipeline as deployed on the measured
networks: its stages, the limits that bound it, and how a parameter
set's ceiling relates to what the chain carries. It holds no
measurements. It fixes the vocabulary with which section 4 is read.

## 2.1 The pipeline and its clock

Leios adds to Praos a second kind of block, the endorser block. The
ranking block (RB) remains the Praos block and the only one that
extends the chain. The endorser block (EB) is a list of transaction
references announced inside an RB. Its transactions, called its
closure, enter the ledger when a later RB carries a certificate from a
committee of stake pools that validated them. Between announcement and
certificate the pipeline has six stages, each with a clock of its own.

The first stage is the forger's snapshot. A pool elected for a slot
snapshots its mempool, builds the RB and announces with it an EB of
the snapshot's transactions that fit the caps. The snapshot has a time
budget, so the EB is bounded by the mempool's content and by that
budget, not only by the caps. As deployed, an RB that carries a
certificate carries no transactions of its own.

The second and third stages are diffusion. Every node fetches the EB
body, the reference list, and then assembles the closure from its own
mempool and from its peers.

The fourth stage is validation and voting. The committee, the pools
with the most stake with each vote weighted by stake, validates the
closure against the ledger state and votes. The vote is scheduled
three seconds after the EB's slot and must be cast by seven. A voter
that receives the closure after the deadline does not vote.

Validation applies every transaction of the closure to the ledger
state: in full for the ones the node has not seen, and as a cheaper
reapplication for the ones it validated at mempool admission or in an
earlier EB. Its cost therefore depends on how much of the EB the voter
had already validated.

The fifth stage is the tally. The EB is certifiable once the votes
reach the quorum, three quarters of the committee's weight. The
certificate can only go in an RB at least fourteen slots after the
announcing one, the certification gap. On paper the next RB comes that
late with probability 0.513, so about half of the announced EBs are
eligible for certification. The rest are superseded by the next
announcement.

The sixth stage is adoption. A node that receives a certifying RB must
hold the closure and apply its transactions before adopting the block.
That is more work than a plain Praos block takes, and if it delays
propagation the next slot leader may fork the chain. Section 5 is
about this stage.

Each stage has a deadline or a budget. The tables of section 4 have
one row per stage for that reason.

## 2.2 The constraint set

A Leios parameter set is more than the two caps that name it. Table
2.1 lists its parameters with the stage of 2.1 each one binds.

| parameter | what it bounds | stage it binds |
|---|---|---|
| reference cap (bytes of the EB body) | the number of transactions an EB may reference, at 36 or 37 B each | snapshot; body diffusion |
| closure cap (bytes of the EB's transactions) | the bytes an EB brings into the chain | closure diffusion; validation; adoption |
| reference-script cap | the bytes of reference scripts the closure may pull in | validation |
| Plutus steps and memory budgets | the script computation the closure may require | validation |
| timings L_hdr, L_vote, L_diff | when votes are cast and by when | validation and voting |
| certification gap | how far the next RB must be for a certificate to count | tally |
| committee size and quorum | how much stake must vote, and how it is spread | tally |
| the Praos block limit and f | the plain block's share and the RB rate | all, as the clock |

Table 2.1. The parameters of a Leios set and the stage each one binds.

The measurements exercise the two caps, the timings at their deployed
values, the certification gap at 14 slots and the committee with each
network's real stake. The Praos block limit and f stay at mainnet's
values. The script and reference-script budgets are left untouched:
every transaction measured carries no script.

Three conditions outside the parameter set bound the pipeline as much
as the parameters do: the hardware of the nodes, which decides how
fast a closure is validated; the mempool coverage, how much of an EB a
node already holds when it is announced, which decides how much of it
is applied in full; and the topology, which decides how fast bodies,
closures and votes travel. This report measures on the populations of
section 3 and states its results against them. It defines no
reference machine.

The script budgets are not independent of the byte caps. A voter must
have received and validated the closure by the deadline, so the
closure's arrival and its validation share the same seconds. Whatever
validation work a closure carries, script computation or more
transactions, must be paid for by a closure that arrives earlier, and
at a given bandwidth an earlier closure is a smaller one. At fixed
hardware, bandwidth and implementation, a larger script budget
therefore means a smaller closure. This report treats
the script budgets as values to be set conservatively alongside the
caps it measures, not as dimensions it has confirmed.

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
