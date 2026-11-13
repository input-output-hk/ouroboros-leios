EBs 361, of which the chain certified 164; validation records 23,220 from 84 nodes (84 pools); deadline 7 s after the EB slot. Calibrated threshold on the reporting weight 0.527 (the reporting voters hold 59 to 59 % of the committee): the rule agrees with the chain on 316 EBs (87.5 %) and certifies 179. Hardware factors from the hosts' measured cost per reapplied transaction, by class: current 89 us; two older 130 us; three older 158 us; 67 voters slower than the current generation, 7 without a reading. Rebuilt times: 20 ms per EB plus the applied transactions at the class's cost on old-input closures and the reapplied ones at its reapply cost, or the applied ones at the class's cost on chained closures (the loop fix); costs per class (ms / ms / us): current 1.11 / 0.20 / 85; two older 1.57 / 0.31 / 128; three older 1.85 / 0.35 / 147. Throughput scaled from the window's measured 22.0 kB/s and 29.6 tx/s by the transactions of the EBs certified.

| voters' speed and closures | EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median | with the loop fix: EBs certified | certification | kB/s | tx/s | quorum voter validated at, s: p50 / p90 | transactions that voter validates by the deadline, median |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| as recorded | 179 | 49.6 % | 22.0 | 27.1 | 6.10 / 11.60 | 3,100 | - | - | - | - | - | - |
| closures as they were, every voter at least at the current generation | 244 | 67.6 % | 31.5 | 38.8 | 3.99 / 6.69 | 11,400 | - | - | - | - | - | - |
| every closure old-input, every voter at the current generation (c8id, r8id) | 247 | 68.4 % | 32.3 | 39.9 | 4.31 / 6.54 | 7,900 | 264 | 73.1 % | 35.6 | 43.9 | 3.38 / 5.18 | 27,200 |
| every closure old-input, every voter at the two generations older (c6id) | 235 | 65.1 % | 29.8 | 36.8 | 4.79 / 7.32 | 5,400 | 260 | 72.0 % | 35.2 | 43.4 | 3.57 / 5.31 | 18,000 |
| every closure old-input, every voter at the three generations older (c5d) | 226 | 62.6 % | 28.5 | 35.1 | 5.07 / 7.71 | 4,600 | 259 | 71.7 % | 35.0 | 43.2 | 3.64 / 5.37 | 15,900 |

The quorum voter is the one whose vote brings the reporting weight to the calibrated threshold; its closure start is its own. The transactions it validates by the deadline are the EB's scaled by (deadline - start) / (validated - start), the closure arriving as it did. Throughput by the ladder's formula with the EB term at the certified bytes (transactions x 810 B) and the plain-RB term at the certification share, pinned to the measured figure.

Of the 97 EBs not certified with the loop fix on current-generation hosts, 17 had the closure at 90 % of the reporting nodes by the deadline, 35 had it there only after the deadline, and 45 never had it there (closure_fleet_per_eb.csv).

| slow voters moved to the current generation, heaviest first | their weight | EBs certified | certification |
|---|---|---|---|
| 1 | 7 % | 179 | 49.6 % |
| 2 | 8 % | 179 | 49.6 % |
| 3 | 8 % | 188 | 52.1 % |
| 5 | 9 % | 188 | 52.1 % |
| 10 | 12 % | 191 | 52.9 % |
| 20 | 16 % | 201 | 55.7 % |
| all 67 | 39 % | 244 | 67.6 % |
