Operators' nodes, from their telemetry scrapes (about one per minute), 2026-10-24 12:00:00 to 2026-10-26 13:00:00 UTC.

| operator nodes, 90 nodes | p10 | median | p90 | max |
|---|---|---|---|---|
| resident set at the node's median sample, GB | 1.5 | 2.1 | 4.5 | 18.8 |
| resident set at the node's peak sample, GB | 1.6 | 2.5 | 6.8 | 20.8 |
| GC live data at the peak, GB | 0.7 | 1.0 | 2.1 | 19.2 |
| process CPU, cores, the node's median interval | 0.10 | 0.20 | 0.46 | 0.72 |
| process CPU, cores, the node's 90th-percentile interval | 0.14 | 0.32 | 0.76 | 1.12 |
| GC share of the process CPU time | 0.01 | 0.03 | 0.06 | 0.14 |

IOG and PIR hosts, from the per-minute series of the IOG monitoring, by instance class.

| host class | hosts | host memory, GB | resident set, median / peak, GB | GC live peak, GB | process CPU, cores, median / p90 interval | GC share | host CPU busy, median / peak (all cores, 5-minute rate) |
|---|---|---|---|---|---|---|---|
| c5d.2xlarge, 8 vCPU | PIR7, PIR9 | 16 to 16 | 2.1 to 2.2 / 3.0 to 3.2 | 1.2 to 1.2 | 0.17 to 0.18 / 0.38 to 0.44 | 0.01 to 0.01 | 0.05 to 0.05 / 0.10 to 0.11 |
| c6id.2xlarge, 8 vCPU | PIR2, PIR5, PIR6 | 16 to 16 | 2.1 to 2.2 / 2.9 to 3.5 | 1.1 to 1.3 | 0.14 to 0.17 / 0.31 to 0.43 | 0.01 to 0.01 | 0.04 to 0.04 / 0.09 to 0.87 |
| c8id.xlarge, 4 vCPU | IOG1, IOG3 | 8 to 8 | 1.7 to 1.7 / 1.9 to 2.0 | 1.0 to 1.1 | 0.08 to 0.10 / 0.21 to 0.23 | 0.01 to 0.01 | 0.05 to 0.05 / 0.12 to 0.13 |
| c8id.xlarge, 4 vCPU | PIR1, PIR10, PIR3, PIR4, PIR8 | 8 to 8 | 2.0 to 2.2 / 2.9 to 3.5 | 1.2 to 1.3 | 0.12 to 0.15 / 0.28 to 0.37 | 0.02 to 0.02 | 0.06 to 0.08 / 0.14 to 0.98 |
| r8id.xlarge, 4 vCPU | IOG2 | 33 | 1.7 / 1.9 | 1.0 | 0.08 / 0.22 | 0.01 | 0.05 / 0.13 |
