EBs with records 1,444, records 72,067, quorum 39 voters; the run's costs per applied / reapplied transaction 0.41 ms / 190 us split each record's time between the two operations. Throughput by the ladder's formula with the EB term at the certified bytes (transactions x 374 B) and the plain-RB term at the certification share, pinned to the run's measured 26.6 kB/s and 71.1 tx/s.

| voters' speed | apply, reapply relative to the run's hosts | late votes | EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median |
|---|---|---|---|---|---|---|---|---|
| as measured | 1.00, 1.00 | 0.1 % | 1,440 | 99.7 % | 26.6 | 71.2 | 3.97 / 4.45 | 11,000 |
| hosts two generations newer (c6id) | 0.85, 0.85 | 0.1 % | 1,440 | 99.7 % | 26.6 | 71.2 | 3.82 / 4.26 | 13,000 |
| hosts of the current generation | 0.60, 0.60 | 0.0 % | 1,440 | 99.7 % | 26.6 | 71.2 | 3.58 / 3.94 | 18,400 |
| validation started at the closure arrival | 1.00, 1.00 | 0.1 % | 1,440 | 99.7 % | 26.6 | 71.2 | 3.55 / 4.39 | 12,600 |

As recorded: 0.1 % of the votes late, 1,440 EBs (99.7 %) with 39 or more voters validated by 7 s.

The quorum voter is the one whose validation completes the quorum (the 39-th earliest per EB); its closure start is the 39-th earliest start. The transactions it validates by the deadline are the EB's scaled by (deadline - start) / (validated - start), the closure arriving as it did.

| share of the EB's transactions the voters applied in full | EBs | fail: as measured | fail: hosts two generations newer (c6id) | fail: hosts of the current generation | fail: validation started at the closure arrival |
|---|---|---|---|---|---|
| under 30 % | 395 | 0 % | 0 % | 0 % | 0 % |
| 30 to 40 % | 158 | 0 % | 0 % | 0 % | 0 % |
| 40 to 50 % | 236 | 0 % | 0 % | 0 % | 0 % |
| 50 to 60 % | 278 | 0 % | 0 % | 0 % | 0 % |
| 60 to 70 % | 168 | 0 % | 0 % | 0 % | 0 % |
| 70 % and over | 209 | 2 % | 2 % | 2 % | 2 % |
