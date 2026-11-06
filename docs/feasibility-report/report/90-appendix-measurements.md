# Appendix A. How each quantity was measured

This appendix states, for every quantity the report's tables and
figures rest on, which records it was read from, what marks its start
and its end, which records were kept or dropped, and how the result was
aggregated, so that a reviewer can judge the approach and not only the
numbers. It is written for sections 1 to 6 and grows with the sections
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
| closure at 90 and 95 % of the nodes by EB size | period database, chain cache | `closure_fleet.sql` | `stage_table.py` |
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
| EBs failing by applied share | the per-record validation output of a cluster run, its ladder export | `host_speed.py` | `cost_table.py unseen` |
| nodes by their closure p90, upstream-peer groups | the per-node diffusion outputs, the voters table; the archived per-peer announcement pulls | `diffusion_bins.py`, `peers_upstream.py` | `diffusion_table.py bins`, `upstream` |
| memory and CPU | the period database's metrics, the archived monitoring series, the cluster's resource trace; the hosts table | `resources.py` | `cost_table.py resources` |
| node versions | the period database's metrics | the node-versions query | read directly |
