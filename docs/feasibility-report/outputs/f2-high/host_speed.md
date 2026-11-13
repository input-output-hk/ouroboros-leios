EBs 2,127, of which the chain certified 1,033; validation records 116,737 from 87 nodes (87 pools); deadline 7 s after the EB slot. Calibrated threshold on the reporting weight 0.446 (the reporting voters hold 61 to 61 % of the committee): the rule agrees with the chain on 1,857 EBs (87.3 %) and certifies 993. Hardware factors from the hosts' measured cost per reapplied transaction, by class: current 87 us; two older 129 us; three older 151 us; 77 voters slower than the current generation, 2 without a reading. Rebuilt times: 20 ms per EB plus the applied transactions at the class's cost on old-input closures and the reapplied ones at its reapply cost, or the applied ones at the class's cost on chained closures (the loop fix); costs per class (ms / ms / us): current 1.11 / 0.20 / 85; two older 1.57 / 0.31 / 128; three older 1.85 / 0.35 / 147. Throughput scaled from the window's measured 12.0 kB/s and 38.0 tx/s by the transactions of the EBs certified.

| voters' speed and closures | EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median | with the loop fix: EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| as recorded | 993 | 46.7 % | 12.0 | 37.8 | 5.54 / 12.74 | 6,200 | - | - | - | - | - | - |
| closures as they were, every voter at least at the current generation | 1,353 | 63.6 % | 18.1 | 56.9 | 4.05 / 7.23 | 19,400 | - | - | - | - | - | - |
| every closure old-input, every voter at the current generation (c8id, r8id) | 1,192 | 56.0 % | 14.9 | 46.9 | 4.66 / 8.75 | 9,000 | 1,464 | 68.8 % | 19.9 | 62.5 | 3.65 / 5.97 | 27,900 |
| every closure old-input, every voter at the two generations older (c6id) | 1,045 | 49.1 % | 12.8 | 40.2 | 5.19 / 10.60 | 6,400 | 1,435 | 67.5 % | 19.4 | 60.8 | 3.92 / 6.29 | 18,600 |
| every closure old-input, every voter at the three generations older (c5d) | 991 | 46.6 % | 12.0 | 37.6 | 5.51 / 11.73 | 5,400 | 1,421 | 66.8 % | 19.1 | 59.9 | 4.02 / 6.46 | 16,300 |

The quorum voter is the one whose vote brings the reporting weight to the calibrated threshold; its closure start is its own. The transactions it validates by the deadline are the EB's scaled by (deadline - start) / (validated - start), the closure arriving as it did. Throughput by the ladder's formula with the EB term at the certified bytes (transactions x 318 B) and the plain-RB term at the certification share, pinned to the measured figure.

Of the 663 EBs not certified with the loop fix on current-generation hosts, 41 had the closure at 90 % of the reporting nodes by the deadline, 376 had it there only after the deadline, and 246 never had it there (closure_fleet_per_eb.csv).

| slow voters moved to the current generation, heaviest first | their weight | EBs certified | certification |
|---|---|---|---|
| 1 | 1 % | 994 | 46.7 % |
| 2 | 1 % | 1,007 | 47.3 % |
| 3 | 2 % | 1,012 | 47.6 % |
| 5 | 3 % | 1,014 | 47.7 % |
| 10 | 5 % | 1,033 | 48.6 % |
| 20 | 10 % | 1,072 | 50.4 % |
| all 77 | 37 % | 1,353 | 63.6 % |
