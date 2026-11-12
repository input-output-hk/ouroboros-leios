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
