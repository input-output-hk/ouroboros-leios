Votes 223,343 on 3,528 EBs from 87 nodes; deadline 7 s after the EB slot. Late in every row: 15.0 % of the votes whose closure arrived after the deadline or never, and 1.9 % whose validation never finished (no counts to reprice); 19.2 % of the votes had the closure arrive between the 3 s mark and the deadline, a shortened budget. Hardware row: 76 nodes slower than the current generation scaled down by their own reapply cost over the class's (87 us), 3 without a reading not moved. Rebuilt rows: 0.02 s per EB plus the applied transactions at the class's cost (old-input, or chained with the loop's cost removed) and the reapplied ones at its reapply cost; costs per class (ms / ms / us): current 1.11 / 0.20 / 85; two older 1.57 / 0.31 / 128; three older 1.85 / 0.35 / 147.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 72.9 % | 10.2 % | 3.5 / 6.2 | 0.78 / 3.81 / 116.3 |
| closures as recorded, hosts at least current generation | 80.3 % | 2.8 % | 5.0 / 6.8 | 0.42 / 1.69 / 35.2 |
| old-input, current generation | 75.7 % | 7.4 % | 3.9 / 6.4 | 0.54 / 3.12 / 8.9 |
| old-input, c6id | 70.7 % | 12.4 % | 3.4 / 6.0 | 0.78 / 4.43 / 12.5 |
| old-input, c5d | 68.1 % | 15.0 % | 3.2 / 5.9 | 0.90 / 5.20 / 14.8 |
| loop's cost removed, current generation | 82.2 % | 0.9 % | 6.6 / 6.9 | 0.40 / 0.76 / 1.9 |
| loop's cost removed, c6id | 81.7 % | 1.4 % | 6.4 / 6.9 | 0.60 / 1.15 / 2.9 |
| loop's cost removed, c5d | 81.5 % | 1.6 % | 6.3 / 6.9 | 0.69 / 1.30 / 3.3 |

EBs of under 2,000 transactions, 907 EBs; late in every row: 13.3 % of the votes for the closure's arrival, 2.3 % never validated; 12.5 % had the closure arrive between the 3 s mark and the deadline.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 83.5 % | 0.9 % | 5.9 / 6.9 | 0.20 / 0.82 / 12.2 |
| closures as recorded, hosts at least current generation | 84.2 % | 0.2 % | 6.8 / 7.0 | 0.11 / 0.24 / 4.2 |
| old-input, current generation | 83.9 % | 0.5 % | 6.5 / 7.0 | 0.13 / 0.67 / 2.4 |
| old-input, c6id | 83.7 % | 0.7 % | 6.3 / 6.9 | 0.19 / 0.95 / 3.4 |
| old-input, c5d | 83.6 % | 0.8 % | 6.1 / 6.9 | 0.21 / 1.11 / 4.0 |
| loop's cost removed, current generation | 84.2 % | 0.1 % | 6.9 / 7.0 | 0.12 / 0.20 / 0.6 |
| loop's cost removed, c6id | 84.2 % | 0.2 % | 6.9 / 7.0 | 0.17 / 0.29 / 0.9 |
| loop's cost removed, c5d | 84.2 % | 0.2 % | 6.9 / 7.0 | 0.20 / 0.33 / 1.0 |

EBs of 2,000 to 4,000 transactions, 900 EBs; late in every row: 10.4 % of the votes for the closure's arrival, 1.9 % never validated; 21.1 % had the closure arrive between the 3 s mark and the deadline.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 80.3 % | 7.4 % | 3.6 / 6.4 | 0.63 / 2.69 / 67.1 |
| closures as recorded, hosts at least current generation | 86.1 % | 1.6 % | 5.8 / 6.9 | 0.31 / 0.92 / 31.5 |
| old-input, current generation | 83.2 % | 4.5 % | 5.1 / 6.6 | 0.35 / 2.52 / 4.7 |
| old-input, c6id | 78.1 % | 9.6 % | 3.7 / 6.2 | 0.51 / 3.56 / 6.7 |
| old-input, c5d | 75.3 % | 12.4 % | 3.5 / 6.0 | 0.59 / 4.19 / 7.9 |
| loop's cost removed, current generation | 87.1 % | 0.6 % | 6.8 / 6.9 | 0.31 / 0.55 / 1.1 |
| loop's cost removed, c6id | 86.7 % | 1.0 % | 6.6 / 6.9 | 0.47 / 0.84 / 1.7 |
| loop's cost removed, c5d | 86.6 % | 1.1 % | 6.6 / 6.9 | 0.53 / 0.95 / 2.0 |

EBs of 4,000 to 6,000 transactions, 1,190 EBs; late in every row: 16.7 % of the votes for the closure's arrival, 1.9 % never validated; 20.2 % had the closure arrive between the 3 s mark and the deadline.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 62.6 % | 18.8 % | 3.2 / 5.9 | 1.42 / 6.68 / 116.3 |
| closures as recorded, hosts at least current generation | 75.5 % | 5.9 % | 4.5 / 6.6 | 0.71 / 2.81 / 35.2 |
| old-input, current generation | 71.7 % | 9.7 % | 3.9 / 6.4 | 0.93 / 3.59 / 6.8 |
| old-input, c6id | 64.0 % | 17.4 % | 3.2 / 6.0 | 1.34 / 5.08 / 9.7 |
| old-input, c5d | 59.9 % | 21.5 % | 3.1 / 5.7 | 1.56 / 5.98 / 11.4 |
| loop's cost removed, current generation | 80.2 % | 1.2 % | 6.6 / 6.9 | 0.51 / 0.80 / 1.6 |
| loop's cost removed, c6id | 79.6 % | 1.8 % | 6.5 / 6.9 | 0.76 / 1.22 / 2.5 |
| loop's cost removed, c5d | 79.3 % | 2.1 % | 6.4 / 6.9 | 0.87 / 1.38 / 2.8 |

EBs of 6,000 and up transactions, 531 EBs; late in every row: 22.0 % of the votes for the closure's arrival, 1.3 % never validated; 25.1 % had the closure arrive between the 3 s mark and the deadline.

| row | in time | out of time | closure at, s: p50 / p90 | validation, s: p50 / p90 / max |
|---|---|---|---|---|
| as recorded | 65.6 % | 11.0 % | 4.5 / 6.4 | 1.31 / 3.65 / 37.9 |
| closures as recorded, hosts at least current generation | 74.3 % | 2.3 % | 6.3 / 6.8 | 0.70 / 1.37 / 14.4 |
| old-input, current generation | 57.5 % | 19.1 % | 3.5 / 6.0 | 1.19 / 5.50 / 8.9 |
| old-input, c6id | 51.0 % | 25.7 % | 3.3 / 5.7 | 1.73 / 7.79 / 12.5 |
| old-input, c5d | 48.0 % | 28.6 % | 3.3 / 5.7 | 2.01 / 9.16 / 14.8 |
| loop's cost removed, current generation | 74.7 % | 1.9 % | 6.4 / 6.9 | 0.70 / 1.15 / 1.9 |
| loop's cost removed, c6id | 73.3 % | 3.3 % | 6.1 / 6.8 | 1.04 / 1.76 / 2.9 |
| loop's cost removed, c5d | 72.7 % | 3.9 % | 6.0 / 6.7 | 1.19 / 1.99 / 3.3 |
