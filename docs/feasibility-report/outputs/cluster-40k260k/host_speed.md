EBs with records 1,639, records 81,859, quorum 39 voters; the run's costs per applied / reapplied transaction 0.91 ms / 152 us split each record's time between the two operations. Throughput by the ladder's formula with the EB term at the certified bytes (transactions x 200 B) and the plain-RB term at the certification share, pinned to the run's measured 7.5 kB/s and 37.4 tx/s.

| voters' speed | apply, reapply relative to the run's hosts | late votes | EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median |
|---|---|---|---|---|---|---|---|---|
| as measured | 1.00, 1.00 | 0.1 % | 1,636 | 99.8 % | 7.5 | 37.5 | 3.78 / 4.10 | 5,700 |
| hosts two generations newer (c6id) | 0.85, 0.85 | 0.0 % | 1,637 | 99.9 % | 7.5 | 37.5 | 3.66 / 3.95 | 6,700 |
| hosts of the current generation | 0.60, 0.60 | 0.0 % | 1,637 | 99.9 % | 7.5 | 37.5 | 3.47 / 3.70 | 9,500 |
| the loop's cost removed, on the run hosts | 0.38, 1.00 | 0.0 % | 1,637 | 99.9 % | 7.5 | 37.5 | 3.33 / 3.50 | 13,500 |
| validation started at the closure arrival | 1.00, 1.00 | 0.1 % | 1,636 | 99.8 % | 7.5 | 37.5 | 3.19 / 4.00 | 6,900 |

As recorded: 0.1 % of the votes late, 1,636 EBs (99.8 %) with 39 or more voters validated by 7 s.

The quorum voter is the one whose validation completes the quorum (the 39-th earliest per EB); its closure start is the 39-th earliest start. The transactions it validates by the deadline are the EB's scaled by (deadline - start) / (validated - start), the closure arriving as it did.

| share of the EB's transactions the voters applied in full | EBs | fail: as measured | fail: hosts two generations newer (c6id) | fail: hosts of the current generation | fail: the loop's cost removed, on the run hosts | fail: validation started at the closure arrival |
|---|---|---|---|---|---|---|
| under 30 % | 343 | 0 % | 0 % | 0 % | 0 % | 0 % |
| 30 to 40 % | 167 | 0 % | 0 % | 0 % | 0 % | 0 % |
| 40 to 50 % | 328 | 0 % | 0 % | 0 % | 0 % | 0 % |
| 50 to 60 % | 320 | 0 % | 0 % | 0 % | 0 % | 0 % |
| 60 to 70 % | 181 | 1 % | 0 % | 0 % | 0 % | 1 % |
| 70 % and over | 300 | 0 % | 0 % | 0 % | 0 % | 0 % |
