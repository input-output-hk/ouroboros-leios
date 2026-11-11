Votes 42,795 on 606 EBs from 84 nodes; deadline 7 s after the EB slot. Late in every row: 7.1 % of the votes whose closure arrived after the deadline or never, and 1.5 % whose validation never finished (no counts to reprice); 11.9 % of the votes had the closure arrive between the 3 s mark and the deadline, a shortened budget. Hardware row: 68 nodes slower than the current generation scaled down by their own reapply cost over the class's (90 us), 6 without a reading not moved. Rebuilt rows: 0.02 s per EB plus the applied transactions at the class's cost (old-input, or chained with the loop's cost removed) and the reapplied ones at its reapply cost; costs per class (ms / ms / us): current 1.11 / 0.20 / 85; two older 1.57 / 0.31 / 128; three older 1.85 / 0.35 / 147.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 83.5 % | 8.0 % | 2.8 / 6.1 | 0.71 / 3.08 / 119.1 |
| closures as recorded, hosts at least current generation | 88.7 % | 2.7 % | 3.3 / 6.6 | 0.32 / 1.09 / 108.7 |
| old-input, current generation | 89.2 % | 2.2 % | 5.1 / 6.7 | 0.46 / 1.59 / 9.2 |
| old-input, c6id | 87.7 % | 3.8 % | 4.0 / 6.5 | 0.67 / 2.25 / 13.0 |
| old-input, c5d | 86.5 % | 4.9 % | 3.6 / 6.4 | 0.77 / 2.64 / 15.3 |
| loop's cost removed, current generation | 91.2 % | 0.3 % | 6.8 / 7.0 | 0.26 / 0.44 / 1.7 |
| loop's cost removed, c6id | 91.0 % | 0.4 % | 6.7 / 6.9 | 0.39 / 0.65 / 2.6 |
| loop's cost removed, c5d | 90.9 % | 0.5 % | 6.7 / 6.9 | 0.44 / 0.74 / 3.0 |

EBs of under 2,000 transactions, 278 EBs; late in every row: 8.2 % of the votes for the closure's arrival, 1.5 % never validated; 14.7 % had the closure arrive between the 3 s mark and the deadline.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 86.8 % | 3.6 % | 3.8 / 6.6 | 0.49 / 1.80 / 34.6 |
| closures as recorded, hosts at least current generation | 89.5 % | 0.8 % | 6.3 / 6.9 | 0.23 / 0.62 / 22.8 |
| old-input, current generation | 89.0 % | 1.3 % | 6.3 / 6.9 | 0.37 / 1.45 / 2.2 |
| old-input, c6id | 88.4 % | 2.0 % | 6.0 / 6.8 | 0.53 / 2.04 / 3.2 |
| old-input, c5d | 87.7 % | 2.6 % | 5.8 / 6.7 | 0.61 / 2.40 / 3.7 |
| loop's cost removed, current generation | 90.1 % | 0.3 % | 6.9 / 7.0 | 0.20 / 0.32 / 0.5 |
| loop's cost removed, c6id | 89.9 % | 0.4 % | 6.8 / 6.9 | 0.29 / 0.49 / 0.8 |
| loop's cost removed, c5d | 89.9 % | 0.5 % | 6.8 / 6.9 | 0.32 / 0.55 / 0.9 |

EBs of 2,000 to 4,000 transactions, 266 EBs; late in every row: 5.3 % of the votes for the closure's arrival, 1.1 % never validated; 9.2 % had the closure arrive between the 3 s mark and the deadline.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 85.5 % | 8.0 % | 2.8 / 6.0 | 0.85 / 3.25 / 40.3 |
| closures as recorded, hosts at least current generation | 91.8 % | 1.8 % | 4.8 / 6.7 | 0.36 / 1.14 / 37.7 |
| old-input, current generation | 92.4 % | 1.1 % | 6.1 / 6.8 | 0.45 / 1.45 / 4.5 |
| old-input, c6id | 91.3 % | 2.2 % | 5.1 / 6.6 | 0.64 / 2.06 / 6.3 |
| old-input, c5d | 90.4 % | 3.2 % | 4.2 / 6.4 | 0.74 / 2.42 / 7.4 |
| loop's cost removed, current generation | 93.4 % | 0.2 % | 6.8 / 7.0 | 0.29 / 0.39 / 1.0 |
| loop's cost removed, c6id | 93.2 % | 0.3 % | 6.8 / 6.9 | 0.43 / 0.59 / 1.6 |
| loop's cost removed, c5d | 93.1 % | 0.4 % | 6.7 / 6.9 | 0.48 / 0.67 / 1.8 |

EBs of 4,000 to 6,000 transactions, 46 EBs; late in every row: 5.9 % of the votes for the closure's arrival, 2.8 % never validated; 8.5 % had the closure arrive between the 3 s mark and the deadline.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 68.8 % | 22.4 % | 2.5 / 4.4 | 1.62 / 8.05 / 81.1 |
| closures as recorded, hosts at least current generation | 83.6 % | 7.7 % | 2.8 / 5.8 | 0.65 / 3.38 / 67.9 |
| old-input, current generation | 85.8 % | 5.5 % | 3.0 / 6.4 | 0.74 / 2.99 / 6.2 |
| old-input, c6id | 79.5 % | 11.8 % | 2.7 / 5.1 | 1.09 / 4.24 / 8.7 |
| old-input, c5d | 74.5 % | 16.7 % | 2.5 / 4.7 | 1.26 / 4.98 / 10.3 |
| loop's cost removed, current generation | 90.8 % | 0.5 % | 6.7 / 6.9 | 0.47 / 0.72 / 1.4 |
| loop's cost removed, c6id | 90.5 % | 0.8 % | 6.5 / 6.9 | 0.71 / 1.10 / 2.2 |
| loop's cost removed, c5d | 90.4 % | 0.9 % | 6.4 / 6.9 | 0.81 / 1.25 / 2.4 |

EBs of 6,000 and up transactions, 16 EBs; late in every row: 20.9 % of the votes for the closure's arrival, 3.2 % never validated; 18.8 % had the closure arrive between the 3 s mark and the deadline.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 31.5 % | 44.4 % | 2.7 / 4.4 | 6.39 / 37.06 / 119.1 |
| closures as recorded, hosts at least current generation | 37.8 % | 38.1 % | 2.8 / 4.4 | 3.74 / 14.35 / 108.7 |
| old-input, current generation | 47.4 % | 28.5 % | 3.1 / 4.6 | 2.80 / 7.17 / 9.2 |
| old-input, c6id | 37.1 % | 38.9 % | 2.8 / 4.4 | 3.99 / 10.15 / 13.0 |
| old-input, c5d | 34.1 % | 41.9 % | 2.7 / 4.4 | 4.68 / 11.95 / 15.3 |
| loop's cost removed, current generation | 75.3 % | 0.7 % | 6.5 / 6.9 | 0.82 / 1.38 / 1.7 |
| loop's cost removed, c6id | 74.4 % | 1.5 % | 6.0 / 6.5 | 1.25 / 2.12 / 2.6 |
| loop's cost removed, c5d | 73.3 % | 2.6 % | 5.6 / 6.5 | 1.42 / 2.40 / 3.0 |
