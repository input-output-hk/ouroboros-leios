EBs with records 1,628, records 81,233, quorum 39 voters; the run's costs per applied / reapplied transaction 1.85 ms / 144 us split each record's time between the two operations. Throughput by the ladder's formula with the EB term at the certified bytes (transactions x 200 B) and the plain-RB term at the certification share, pinned to the run's measured 12.2 kB/s and 60.7 tx/s.

| voters' speed | apply, reapply relative to the run's hosts | late votes | EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median |
|---|---|---|---|---|---|---|---|---|
| as measured | 1.00, 1.00 | 20.9 % | 1,115 | 68.5 % | 12.2 | 60.8 | 6.07 / 8.10 | 3,600 |
| the loop's cost removed, on the run c5d hosts | 0.19, 1.00 | 0.1 % | 1,615 | 99.2 % | 15.8 | 79.0 | 3.87 / 4.75 | 14,400 |
| the loop's cost removed, on c6id hosts | 0.17, 0.89 | 0.1 % | 1,616 | 99.3 % | 15.8 | 79.0 | 3.78 / 4.66 | 16,200 |
| the loop's cost removed, on current-generation hosts | 0.11, 0.59 | 0.0 % | 1,618 | 99.4 % | 15.8 | 79.1 | 3.51 / 4.39 | 24,900 |

As recorded: 20.9 % of the votes late, 1,115 EBs (68.5 %) with 39 or more voters validated by 7 s.

The quorum voter is the one whose validation completes the quorum (the 39-th earliest per EB); its closure start is the 39-th earliest start. The transactions it validates by the deadline are the EB's scaled by (deadline - start) / (validated - start), the closure arriving as it did.

| share of the EB's transactions the voters applied in full | EBs | fail: as measured | fail: the loop's cost removed, on the run c5d hosts | fail: the loop's cost removed, on c6id hosts | fail: the loop's cost removed, on current-generation hosts |
|---|---|---|---|---|---|
| under 30 % | 607 | 3 % | 1 % | 1 % | 1 % |
| 30 to 40 % | 227 | 5 % | 1 % | 1 % | 0 % |
| 40 to 50 % | 261 | 24 % | 1 % | 1 % | 0 % |
| 50 to 60 % | 220 | 62 % | 0 % | 0 % | 0 % |
| 60 to 70 % | 113 | 80 % | 1 % | 1 % | 1 % |
| 70 % and over | 200 | 96 % | 1 % | 1 % | 1 % |
