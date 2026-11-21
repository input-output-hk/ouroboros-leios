EBs with records 1,628, records 81,233, quorum 39 voters; the run's costs per applied / reapplied transaction 1.85 ms / 144 us split each record's time between the two operations. Throughput by the ladder's formula with the EB term at the certified bytes (transactions x 200 B) and the plain-RB term at the certification share, pinned to the run's measured 12.2 kB/s and 60.7 tx/s.

| voters' speed | apply, reapply relative to the run's hosts | late votes | EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median |
|---|---|---|---|---|---|---|---|---|
| as measured | 1.00, 1.00 | 20.9 % | 1,115 | 68.5 % | 12.2 | 60.8 | 6.07 / 8.10 | 3,600 |
| hosts two generations newer (c6id) | 0.85, 0.85 | 11.5 % | 1,324 | 81.3 % | 13.7 | 68.4 | 5.65 / 7.40 | 4,200 |
| hosts of the current generation | 0.60, 0.60 | 1.7 % | 1,586 | 97.4 % | 15.6 | 77.9 | 4.92 / 6.25 | 5,900 |
| the loop's cost removed, on the run hosts | 0.19, 1.00 | 0.1 % | 1,615 | 99.2 % | 15.8 | 79.0 | 3.88 / 4.76 | 14,300 |
| validation started at the closure arrival | 1.00, 1.00 | 16.4 % | 1,177 | 72.3 % | 12.6 | 63.1 | 5.74 / 8.02 | 4,000 |

As recorded: 20.9 % of the votes late, 1,115 EBs (68.5 %) with 39 or more voters validated by 7 s.

The quorum voter is the one whose validation completes the quorum (the 39-th earliest per EB); its closure start is the 39-th earliest start. The transactions it validates by the deadline are the EB's scaled by (deadline - start) / (validated - start), the closure arriving as it did.

| share of the EB's transactions the voters applied in full | EBs | fail: as measured | fail: hosts two generations newer (c6id) | fail: hosts of the current generation | fail: the loop's cost removed, on the run hosts | fail: validation started at the closure arrival |
|---|---|---|---|---|---|---|
| under 30 % | 607 | 3 % | 2 % | 1 % | 1 % | 3 % |
| 30 to 40 % | 227 | 5 % | 2 % | 1 % | 1 % | 4 % |
| 40 to 50 % | 261 | 24 % | 10 % | 2 % | 1 % | 22 % |
| 50 to 60 % | 220 | 62 % | 28 % | 3 % | 0 % | 50 % |
| 60 to 70 % | 113 | 80 % | 47 % | 4 % | 1 % | 67 % |
| 70 % and over | 200 | 96 % | 74 % | 10 % | 1 % | 90 % |
