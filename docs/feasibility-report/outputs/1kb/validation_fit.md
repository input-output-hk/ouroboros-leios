| pooled over 39,035 records of 84 nodes | per applied transaction | per reapplied transaction | fixed per EB | residual | applied share, median record |
|---|---|---|---|---|---|
| fit | 3.28 ms | 0.644 ms | -1.24 s | 2.55 s | 8 % |

| per node, 80 nodes with 100 or more records | min | p25 | median | p75 | max |
|---|---|---|---|---|---|
| ms per applied transaction | 0.81 | 2.06 | 2.82 | 5.14 | 10.14 |
| ms per reapplied transaction | 0.142 | 0.390 | 0.542 | 1.128 | 3.584 |

| host class (instance, vCPU, generation) | hosts | EBs with 500+ applied, per host | ms per applied transaction | ms per reapplied transaction | fixed per EB |
|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current | IOG1, IOG3 | 135 to 177 | 1.87 to 1.87 | 0.405 to 0.616 | -1.97 to -1.68 s |
| r8id.xlarge, 4 vCPU, current | IOG2 | 170 | 1.88 | 0.530 | -1.89 s |
| c8id.xlarge, 4 vCPU, current | PIR1, PIR10, PIR3, PIR4, PIR8 | 126 to 252 | 1.71 to 2.15 | 0.413 to 0.617 | -2.24 to -1.66 s |
| c6id.2xlarge, 8 vCPU, two older | PIR2, PIR5, PIR6 | 174 to 240 | 2.63 to 2.86 | 0.730 to 0.820 | -2.86 to -2.48 s |
| c5d.2xlarge, 8 vCPU, three older | PIR7, PIR9 | 199 to 209 | 3.33 to 3.51 | 0.845 to 0.862 | -3.29 to -3.19 s |
