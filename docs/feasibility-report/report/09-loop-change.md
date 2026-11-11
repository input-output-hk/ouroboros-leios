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
over the 252 EBs announced in the first eighty minutes after the
changed host's restart, of which each validated about 220, the rest
superseded by the next RB before the vote.

| host, 2026-11-08 23:45 to 11-09 01:04 UTC | EBs validated | apply cost per transaction | reapply cost per transaction | EBs applying 500 or more with few reapplies: validation per applied transaction, p50 |
|---|---:|---:|---:|---:|
| the changed host | 218 | 0.30 ms | 0.17 ms | 0.35 ms |
| the control | 220 | 1.66 ms | 0.19 ms | 1.40 ms |
| Table 7.2b, c5d | | chained 0.35 / old-input 1.85 | 0.147 | |

Table 9.1. Each host's validation records regressed on the counts of
applied and reapplied transactions (validation time = apply cost ×
applied + reapply cost × reapplied + a constant), over the EBs it
validated in the window. The last column takes the EBs with 500 or more
applied transactions and fewer reapplied than a third of that, where the
validation is the apply cost, and divides the time by the applied count.

The changed host applies at the chained level of section 7, 0.30 to
0.35 ms per transaction on one-input transactions, and the control at
the old-input level, 1.4 to 1.7 ms, on the same transactions. Reapply
is unchanged within the noise on both.

The outcome follows the cost. Table 9.2 bins each host's EBs by the
transactions it applied.

| transactions applied in the EB | the changed host: EBs | validation p50 / p90 | per applied transaction, p50 | the control: EBs | validation p50 / p90 | per applied transaction, p50 |
|---|---:|---:|---:|---:|---:|---:|
| 100 to 500 | 42 | 0.18 / 0.50 s | 0.59 ms | 42 | 0.46 / 0.88 s | 1.78 ms |
| 500 to 1,000 | 28 | 0.38 / 0.84 s | 0.55 ms | 27 | 1.30 / 1.91 s | 1.77 ms |
| 1,000 to 2,000 | 22 | 0.64 / 1.00 s | 0.42 ms | 25 | 2.05 / 2.80 s | 1.53 ms |
| 2,000 and up | 19 | 1.11 / 1.34 s | 0.38 ms | 13 | 4.17 / 6.95 s | 1.72 ms |

Table 9.2. Validation time by applied count on the two hosts over the
window, each host binned by its own count since the two apply different
shares of the same EBs; the per-transaction figure is the validation
time over the applied count, so the reapplies are in it. The bins under
100 applied are left out, where a fixed cost and the reapplies dominate.

The changed host validated every EB of the window within 1.8 s, the
largest one, 6,997 transactions with 2,787 applied, in 1.73 s, and
voted on 217 of the 219 EBs it was to vote on; the two it missed had
their closures arrive at 7.0 and 15.4 s after the slot, past the
deadline at any validation speed. The control missed ten of 221, nine
of them with the closure in hand by 5.8 s and the validation past the
deadline, its largest validation 7.76 s on an EB of 3,769 transactions.

## 9.3 The cluster

The 100 kB / 1 MB run with two-input transactions of section 4.2, which
certified 52 % of its EBs on the unchanged build, was rerun on the
changed build. The run's own tally puts certification close to all of
its EBs; its trace database, from which the validation times and the
ladder would be read with the instruments of sections 4 and 8, was not
available when this section was written.

<!-- note -->
The cluster rerun's figures are to be read from its trace database
when it is delivered: the certification rate over eligible EBs, the
apply and reapply costs on two-input transactions, which the report
has no measurement of (Table 7.2b has the one-input chained cost only),
and the ladder against the run's workload ceiling.
<!-- /note -->

## 9.4 What is not measured

The change has run on one testnet host and one cluster run. What it
does at the committee's scale is still section 8's repricing: the cost
per transaction is confirmed on one host, the votes of the committee
are not.

It has not run at parameter sets larger than 308 kB / 2 MB. It has not
run with transactions of mainnet's mix, where the per-transaction cost
is the script's and the witnesses' rather than the input's.

The host that ran it is of the oldest class measured, so the current
generation's cost with the change is the repricing's figure and not a
reading.

Those measurements are further work.
