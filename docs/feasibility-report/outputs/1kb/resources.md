Operators' nodes, from their telemetry scrapes (about one per minute), 2026-10-28 18:00:00 to 2026-10-29 01:00:00 UTC.

| operator nodes, 89 nodes | p10 | median | p90 | max |
|---|---|---|---|---|
| resident set at the node's median sample, GB | 1.3 | 2.0 | 4.7 | 18.8 |
| resident set at the node's peak sample, GB | 1.4 | 2.1 | 5.5 | 18.8 |
| GC live data at the peak, GB | 0.7 | 0.9 | 1.3 | 21.1 |
| process CPU, cores, the node's median interval | 0.10 | 0.31 | 0.67 | 0.90 |
| process CPU, cores, the node's 90th-percentile interval | 0.18 | 0.48 | 0.94 | 1.42 |
| GC share of the process CPU time | 0.01 | 0.03 | 0.06 | 0.08 |

IOG and PIR hosts, from the per-minute series of the IOG monitoring, by instance class.

| host class | hosts | host memory, GB | resident set, median / peak, GB | GC live peak, GB | process CPU, cores, median / p90 interval | GC share | host CPU busy, median / peak (all cores, 5-minute rate) |
|---|---|---|---|---|---|---|---|
| c5d.2xlarge, 8 vCPU | PIR7, PIR9 | 16 to 16 | 2.9 to 3.3 / 3.1 to 3.9 | 1.2 to 1.4 | 0.28 to 0.32 / 0.52 to 0.63 | 0.01 to 0.02 | 0.06 to 0.06 / 0.10 to 0.12 |
| c6id.2xlarge, 8 vCPU | PIR2, PIR5, PIR6 | 16 to 16 | 2.8 to 3.5 / 3.0 to 4.0 | 1.0 to 1.3 | 0.26 to 0.33 / 0.45 to 0.66 | 0.01 to 0.01 | 0.05 to 0.06 / 0.10 to 0.12 |
| c8id.xlarge, 4 vCPU | IOG1, IOG3 | 8 to 8 | 1.7 to 2.2 / 1.8 to 2.3 | 0.9 to 1.2 | 0.12 to 0.14 / 0.27 to 0.32 | 0.02 to 0.02 | 0.05 to 0.06 / 0.11 to 0.13 |
| c8id.xlarge, 4 vCPU | PIR1, PIR10, PIR3, PIR4, PIR8 | 8 to 8 | 2.6 to 3.5 / 2.9 to 4.1 | 1.1 to 1.5 | 0.19 to 0.29 / 0.35 to 0.59 | 0.02 to 0.03 | 0.07 to 0.11 / 0.15 to 0.20 |
| r8id.xlarge, 4 vCPU | IOG2 | 33 | 1.5 / 1.6 | 0.9 | 0.12 / 0.30 | 0.02 | 0.06 / 0.12 |
