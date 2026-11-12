# 0. Summary

This report measures the Leios pipeline on the public testnet and on
the benchmarking cluster at three parameter sets, named by the
reference list an endorser block may carry and the bytes of its
closure. Every transaction measured is a value transfer without
scripts. The standard is the proposal's: a parameter set confirmed
feasible, with a credible path upward.

| parameter set | ceiling, kB/s | measured, kB/s | certified of the eligible EBs |
|---|---:|---:|---:|
| 40 kB / 260 kB, cluster and testnet | 8.9 | 7.5 and 7.2 | 99 % and 97 % |
| 100 kB / 1 MB, cluster | 27.9 | 12.2 and 15.5; 26.6 on the latest build | 69 % and 52 %; 99 % on the latest build |
| 308 kB / 2 MB, testnet | 53.5 | 12.0 and 22.0 | 49 % and 45 % |

Table 0.1. The three sets against their parameter ceiling, the rate
with every EB full and certified; two windows or runs per set (Tables
1.4, 4.1, 4.3 and 4.5), and for the 100 kB / 1 MB set a third run on
the latest build at the time of this report (Table 9.3). An EB is
eligible when the next RB leaves it the certification gap; on the 2 MB
set the EBs were at 0.6 of the cap on average.

Leios is confirmed at twice the Praos ceiling on both populations. It
is confirmed at six times on the cluster on the latest build at the
time of this report. The testnet at that set is the next stage. The
ten-times set is not confirmed as measured. It depends on that build
and on the closure's diffusion, and sections 8 and 9 give evidence of
feasibility on the validation side. The ten-times line needs a closure
of about 1.7 MB, smaller than the 2 MB closures measured here.

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
