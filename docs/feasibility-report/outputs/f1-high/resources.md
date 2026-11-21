Operators' nodes, from their telemetry scrapes (about one per minute), 2026-10-21 12:00:00 to 2026-10-22 01:00:00 UTC.

| operator nodes, 81 nodes | p10 | median | p90 | max |
|---|---|---|---|---|
| resident set at the node's median sample, GB | 1.0 | 1.3 | 2.6 | 18.3 |
| resident set at the node's peak sample, GB | 1.1 | 1.5 | 3.4 | 18.3 |
| GC live data at the peak, GB | 0.6 | 0.8 | 1.4 | 12.7 |
| process CPU, cores, the node's median interval | 0.06 | 0.12 | 0.34 | 24.83 |
| process CPU, cores, the node's 90th-percentile interval | 0.09 | 0.20 | 0.57 | 55.39 |
| GC share of the process CPU time | 0.01 | 0.02 | 0.05 | 0.12 |

IOG and PIR hosts, from the per-minute series of the IOG monitoring, by instance class.

| host class | hosts | host memory, GB | resident set, median / peak, GB | GC live peak, GB | process CPU, cores, median / p90 interval | GC share | host CPU busy, median / peak (all cores, 5-minute rate) |
|---|---|---|---|---|---|---|---|
| c5d.2xlarge, 8 vCPU | PIR7, PIR9 | 16 to 16 | 1.5 to 1.5 / 1.8 to 1.8 | 0.9 to 1.0 | 0.11 to 0.12 / 0.21 to 0.23 | 0.01 to 0.01 | 0.03 to 0.03 / 0.05 to 0.06 |
| c6id.2xlarge, 8 vCPU | PIR2, PIR5, PIR6 | 16 to 16 | 1.4 to 1.5 / 1.6 to 1.9 | 0.9 to 1.0 | 0.10 to 0.14 / 0.17 to 0.31 | 0.01 to 0.01 | 0.02 to 0.03 / 0.05 to 0.08 |
| c8id.xlarge, 4 vCPU | IOG1, IOG3 | 8 to 8 | 1.0 to 1.1 / 1.2 to 1.2 | 0.7 to 0.8 | 0.05 to 0.05 / 0.11 to 0.11 | 0.01 to 0.01 | 0.03 to 0.03 / 0.06 to 0.06 |
| c8id.xlarge, 4 vCPU | PIR1, PIR10, PIR3, PIR4, PIR8 | 8 to 8 | 1.2 to 1.5 / 1.4 to 1.9 | 0.9 to 1.1 | 0.09 to 0.10 / 0.16 to 0.23 | 0.01 to 0.02 | 0.04 to 0.05 / 0.08 to 0.11 |
| r8id.xlarge, 4 vCPU | IOG2 | 33 | 1.0 / 1.2 | 0.8 | 0.05 / 0.12 | 0.01 | 0.04 / 0.07 |
