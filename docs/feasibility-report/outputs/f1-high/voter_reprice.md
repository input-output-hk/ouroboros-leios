Votes 69,286 on 958 EBs from 79 nodes; deadline 7 s after the EB slot. Late in every row: 2.7 % of the votes whose closure arrived after the deadline or never, and 0.2 % whose validation never finished (no counts to reprice); 4.5 % of the votes had the closure arrive between the 3 s mark and the deadline, a shortened budget. Hardware row: 70 nodes slower than the current generation scaled down by their own reapply cost over the class's (97 us), 2 without a reading not moved. Rebuilt rows: 0.02 s per EB plus the applied transactions at the class's cost (old-input, or chained with the loop's cost removed) and the reapplied ones at its reapply cost; costs per class (ms / ms / us): current 0.50 / 0.19 / 88; two older 0.75 / 0.30 / 135; three older 0.83 / 0.35 / 140.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 96.6 % | 0.6 % | 3.6 / 6.6 | 0.25 / 0.92 / 15.6 |
| closures as recorded, hosts at least current generation | 97.0 % | 0.1 % | 6.4 / 6.9 | 0.11 / 0.23 / 3.6 |
| old-input, current generation | 97.1 % | 0.1 % | 6.9 / 7.0 | 0.12 / 0.40 / 0.7 |
| old-input, c6id | 97.0 % | 0.1 % | 6.7 / 6.9 | 0.17 / 0.60 / 1.0 |
| old-input, c5d | 97.0 % | 0.1 % | 6.6 / 6.9 | 0.18 / 0.65 / 1.1 |
| loop's cost removed, current generation | 97.1 % | 0.0 % | 6.9 / 7.0 | 0.12 / 0.18 / 0.3 |
| loop's cost removed, c6id | 97.1 % | 0.1 % | 6.9 / 7.0 | 0.17 / 0.28 / 0.5 |
| loop's cost removed, c5d | 97.1 % | 0.1 % | 6.9 / 7.0 | 0.17 / 0.31 / 0.6 |

EBs of under 2,000 transactions, 958 EBs; late in every row: 2.7 % of the votes for the closure's arrival, 0.2 % never validated; 4.5 % had the closure arrive between the 3 s mark and the deadline.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 96.6 % | 0.6 % | 3.6 / 6.6 | 0.25 / 0.92 / 15.6 |
| closures as recorded, hosts at least current generation | 97.0 % | 0.1 % | 6.4 / 6.9 | 0.11 / 0.23 / 3.6 |
| old-input, current generation | 97.1 % | 0.1 % | 6.9 / 7.0 | 0.12 / 0.40 / 0.7 |
| old-input, c6id | 97.0 % | 0.1 % | 6.7 / 6.9 | 0.17 / 0.60 / 1.0 |
| old-input, c5d | 97.0 % | 0.1 % | 6.6 / 6.9 | 0.18 / 0.65 / 1.1 |
| loop's cost removed, current generation | 97.1 % | 0.0 % | 6.9 / 7.0 | 0.12 / 0.18 / 0.3 |
| loop's cost removed, c6id | 97.1 % | 0.1 % | 6.9 / 7.0 | 0.17 / 0.28 / 0.5 |
| loop's cost removed, c5d | 97.1 % | 0.1 % | 6.9 / 7.0 | 0.17 / 0.31 / 0.6 |
