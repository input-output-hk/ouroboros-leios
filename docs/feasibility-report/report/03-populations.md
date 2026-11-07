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

<!-- note -->
No reference hardware has been defined for Leios yet. The report measures
on the populations it has: the operator nodes of the testnet, whose
hardware is unknown except through the ledger benchmark's spread and the
measured validation speeds; the IOG and PIR hosts, whose instance types
are known; and the cluster's uniform c5d.2xlarge hosts. Which of these, if
any, stands for the machine the parameters are set for is left open.
<!-- /note -->

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

<!-- note -->
The text names no operator node: where section 4 compares operator nodes
with the IOG and PIR hosts it gives counts. The per-node outputs behind
the tables carry agent names, pool ids and tickers, which are public, and
whether they are published as they are or pseudonymised is not decided;
until it is, they are left out of the public copy of the repository.
<!-- /note -->

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
