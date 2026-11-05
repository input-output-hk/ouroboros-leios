Forge-loop calls per RB forged and on the chain, hosts n80, n81, n82, loaded windows of windows-f2-high.txt; p50 / p90 s.

| step | plain RB, 80-88 kB | certifies, closure < 0.5 MB | certifies, closure 0.5-1 MB | certifies, closure 1-1.5 MB | certifies, closure 1.5-2 MB |
|---|---|---|---|---|---|
| RBs | 644 | 80 | 94 | 54 | 43 |
| mempool-get-snapshot-for | 0.504 / 0.507 | - | - | - | - |
| mempool-get-snapshot-for-no-cache | - | 0.504 / 0.508 | 0.503 / 0.506 | 0.504 / 0.507 | 0.503 / 0.507 |
| partition-mempool | 0.506 / 0.512 | 0.544 / 0.569 | 0.588 / 0.623 | 0.643 / 0.704 | 0.681 / 0.733 |
| forge-block | 0.017 / 0.022 | 0.018 / 0.023 | 0.019 / 0.025 | 0.018 / 0.025 | 0.016 / 0.023 |
| on-forged-leios-eb | 0.083 / 0.110 | 0.072 / 0.103 | 0.075 / 0.097 | 0.065 / 0.099 | 0.068 / 0.085 |
| forge | 0.641 / 0.682 | 0.676 / 0.746 | 0.778 / 0.848 | 0.876 / 0.971 | 0.965 / 1.080 |
| ForgedBlock after slot start | 0.525 / 0.532 | 0.565 / 0.590 | 0.611 / 0.646 | 0.666 / 0.726 | 0.700 / 0.749 |

Closure resolution and application at forge (resolve-and-apply-leios-closure, argument = the EB announcement), 13 hosts, by the closure's size.

| closure | calls | closure p50 | transactions p50 | duration p50 / p90 | per transaction |
|---|---|---|---|---|---|
| certifies, closure < 0.5 MB | 98 | 0.30 MB | 972 | 0.040 / 0.064 s | 41 us |
| certifies, closure 0.5-1 MB | 121 | 0.71 MB | 2,246 | 0.084 / 0.119 s | 37 us |
| certifies, closure 1-1.5 MB | 69 | 1.16 MB | 4,046 | 0.138 / 0.201 s | 34 us |
| certifies, closure 1.5-2 MB | 63 | 1.87 MB | 4,890 | 0.189 / 0.248 s | 39 us |
