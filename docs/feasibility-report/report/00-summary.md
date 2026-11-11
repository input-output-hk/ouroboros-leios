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
| 100 kB / 1 MB, cluster | 27.9 | 12.2 and 15.5 | 69 % and 52 % | not confirmed as measured; the voting-loop patch of section 9 is the step |
| 308 kB / 2 MB, testnet | 53.5 | 12.0 and 22.0 | 49 % and 45 % | not confirmed as measured; with the patch, validation is no longer the limit and the closure's arrival on the testnet's topology is; a cluster run at this set on the patched build would settle it |

Table 0.1. The three sets against their parameter ceiling, the rate
with every EB full and certified; two windows or runs per set (Tables
1.4, 4.1, 4.3 and 4.5). An EB is eligible when the next RB leaves it
the certification gap; on the 2 MB set the EBs were at 0.6 of the cap
on average.

Leios is confirmed at twice the Praos ceiling. The six-times set
depends on the patch of section 9. The ten-times set depends on the
patch and on the closure's diffusion; the 2 MB set measured here is
within reach of both, and the ten-times line itself needs a closure of
about 1.7 MB, a smaller step than the one measured.

**The confirmed set.** At 40 kB / 260 kB, twice the Praos ceiling, every
stage of the pipeline is inside its budget on both populations and the
voting stage loses nothing. The cost to Praos is a forge path half a
second slower and a fork rate six times the control's, within the order
the control sets (section 5).

**What binds above it.** One stage: the validation of the closure at
the vote. From about 2,700 transactions per EB the voters need more
than the four seconds the window leaves, on the cluster's uniform hosts
and on the testnet's spread of operator hardware alike (section 4).

The cost is per transaction, not per byte. Closures of 2 MB certify at
66 % with 2,000 transactions and at 4 % with 4,000 to 6,000
(section 4.3.1).

On the testnet the closure's arrival is the second cause. Closures
above 1.5 MB reach most nodes after the deadline (section 4.3).

**The path upward.** The larger part of the validation cost is the
voting loop's own: a pass over the closure's input table after every
applied transaction, which section 8 priced and section 9 traced in the
code. A patch removing it has run on one testnet host and on one
cluster rerun (section 9).

Repriced at the cost that host reaches, the cluster goes from 69 to
99 % certification at 1 MB on the same hosts. On the testnet's 2 MB
windows validation stops being a cause of late votes at every host
class and EB size, the longest validation on the oldest class at
3.3 s (section 8). The testnet reading covers the voters that send
logs, 60 % of the committee weight; the rest runs the same software,
so the committee's gain is at least that.

What remains late on the testnet is the closure's arrival, a fifth of
the votes on the largest EBs, on a topology the cluster does not share.
Its levers, closure forwarding, egress scheduling and the upstream peer
count, have measured gaps and no measured gain yet (section 8.4), so
the testnet's share at 2 MB is open upward.

Hardware alone is worth less than the patch. With the patch in, it buys
margin rather than certification at these sizes (section 8.2).

The measurement that would settle the 2 MB set is a cluster run at it
on the patched build.

**What the measurements do not cover.** The transaction mix of mainnet,
with scripts and witnesses: no window or run in this report exercised
it, so the comparison with the targets of section 1 is in bytes per
second at the measured transactions, not at mainnet's mix. The
validation margin the patch opens is room for that computation; how
much of it is a measurement still to make.

The patched build at the committee's scale: it has run on one testnet
host, and the records of the cluster rerun were pending when this
report was written.

The models the proposal rests on, the DeltaQ model and the CIP's cost
model, charge apply at 0.5 to 0.6 ms per transaction, above what a
voter pays after the patch of section 9 and below what it paid before.
Their reapply cost and the share of the closure a voter applies remain
on the optimistic side of every measurement here (section 7).

The open points of each section are kept in place as notes to resolve.
