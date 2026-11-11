EBs 548, of which the chain certified 531; validation records 41,699 from 78 nodes (78 pools); deadline 7 s after the EB slot. Calibrated threshold on the reporting weight 0.549 (the reporting voters hold 71 to 73 % of the committee): the rule agrees with the chain on 546 EBs (99.6 %) and certifies 533. Hardware factors from the hosts' measured cost per reapplied transaction, by class: current 98 us; two older 132 us; three older 150 us; 69 voters slower than the current generation, 2 without a reading. Rebuilt times: 20 ms per EB plus the applied transactions at the class's cost on old-input closures and the reapplied ones at its reapply cost, or the applied ones at the class's cost on chained closures (the loop fix); costs per class (ms / ms / us): current 0.50 / 0.19 / 88; two older 0.75 / 0.30 / 135; three older 0.83 / 0.35 / 140. Throughput scaled from the window's measured 7.2 kB/s and 28.1 tx/s by the transactions of the EBs certified.

| voters' speed and closures | EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median | with the loop fix: EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| as recorded | 533 | 97.3 % | 7.2 | 27.9 | 3.39 / 3.55 | 10,200 | - | - | - | - | - | - |
| closures as they were, every voter at least at the current generation | 533 | 97.3 % | 7.2 | 27.9 | 3.13 / 3.21 | 30,400 | - | - | - | - | - | - |
| every closure old-input, every voter at the current generation (c8id, r8id) | 533 | 97.3 % | 7.2 | 27.9 | 3.15 / 3.36 | 21,200 | 533 | 97.3 % | 7.2 | 27.9 | 3.12 / 3.17 | 30,600 |
| every closure old-input, every voter at the two generations older (c6id) | 533 | 97.3 % | 7.2 | 27.9 | 3.22 / 3.51 | 15,400 | 533 | 97.3 % | 7.2 | 27.9 | 3.17 / 3.26 | 20,900 |
| every closure old-input, every voter at the three generations older (c5d) | 532 | 97.1 % | 7.2 | 27.9 | 3.23 / 3.56 | 14,200 | 533 | 97.3 % | 7.2 | 27.9 | 3.18 / 3.29 | 19,500 |

The quorum voter is the one whose vote brings the reporting weight to the calibrated threshold; its closure start is its own. The transactions it validates by the deadline are the EB's scaled by (deadline - start) / (validated - start), the closure arriving as it did. Throughput by the ladder's formula with the EB term at the certified bytes (transactions x 257 B) and the plain-RB term at the certification share, pinned to the measured figure.

Of the 15 EBs not certified with the loop fix on current-generation hosts, 3 had the closure at 90 % of the reporting nodes by the deadline, 0 had it there only after the deadline, and 12 never had it there (closure_fleet_per_eb.csv).

| slow voters moved to the current generation, heaviest first | their weight | EBs certified | certification |
|---|---|---|---|
| 1 | 9 % | 533 | 97.3 % |
| 2 | 9 % | 533 | 97.3 % |
| 3 | 10 % | 533 | 97.3 % |
| 5 | 11 % | 533 | 97.3 % |
| 10 | 15 % | 533 | 97.3 % |
| 20 | 21 % | 533 | 97.3 % |
| all 69 | 49 % | 533 | 97.3 % |
