EBs with records 1,566, records 76,863, quorum 39 voters; the run's costs per applied / reapplied transaction 3.42 ms / 163 us split each record's time between the two operations. Throughput by the ladder's formula with the EB term at the certified bytes (transactions x 374 B) and the plain-RB term at the certification share, pinned to the run's measured 15.5 kB/s and 41.3 tx/s.

| voters' speed | apply, reapply relative to the run's hosts | late votes | EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median |
|---|---|---|---|---|---|---|---|---|
| as measured | 1.00, 1.00 | 35.4 % | 808 | 51.6 % | 15.5 | 41.3 | 6.80 / 9.96 | 2,600 |
| hosts two generations newer (c6id) | 0.85, 0.85 | 27.1 % | 956 | 61.0 % | 17.5 | 46.9 | 6.25 / 8.98 | 3,000 |
| hosts of the current generation | 0.60, 0.60 | 10.3 % | 1,309 | 83.6 % | 22.5 | 60.3 | 5.36 / 7.31 | 4,300 |
| the loop's cost removed, on the run hosts | 0.19, 1.00 | 0.2 % | 1,518 | 96.9 % | 25.5 | 68.3 | 4.09 / 4.80 | 10,300 |
| validation started at the closure arrival | 1.00, 1.00 | 29.3 % | 896 | 57.2 % | 16.8 | 44.8 | 6.43 / 9.73 | 2,900 |

As recorded: 35.4 % of the votes late, 808 EBs (51.6 %) with 39 or more voters validated by 7 s.

The quorum voter is the one whose validation completes the quorum (the 39-th earliest per EB); its closure start is the 39-th earliest start. The transactions it validates by the deadline are the EB's scaled by (deadline - start) / (validated - start), the closure arriving as it did.

| share of the EB's transactions the voters applied in full | EBs | fail: as measured | fail: hosts two generations newer (c6id) | fail: hosts of the current generation | fail: the loop's cost removed, on the run hosts | fail: validation started at the closure arrival |
|---|---|---|---|---|---|---|
| under 30 % | 728 | 9 % | 6 % | 4 % | 3 % | 7 % |
| 30 to 40 % | 271 | 61 % | 35 % | 5 % | 3 % | 39 % |
| 40 to 50 % | 244 | 86 % | 68 % | 16 % | 5 % | 80 % |
| 50 to 60 % | 148 | 97 % | 91 % | 32 % | 3 % | 95 % |
| 60 to 70 % | 93 | 99 % | 98 % | 63 % | 5 % | 98 % |
| 70 % and over | 82 | 100 % | 100 % | 87 % | 0 % | 100 % |
