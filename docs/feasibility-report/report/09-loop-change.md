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
