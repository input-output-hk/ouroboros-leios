| pooled over 67,570 records of 79 nodes | per applied transaction | per reapplied transaction | fixed per EB | residual | applied share, median record |
|---|---|---|---|---|---|
| fit | 1.06 ms | 0.218 ms | 0.07 s | 0.51 s | 1 % |

| per node, 78 nodes with 100 or more records | min | p25 | median | p75 | max |
|---|---|---|---|---|---|
| ms per applied transaction | 0.12 | 0.37 | 0.58 | 1.18 | 3.23 |
| ms per reapplied transaction | 0.013 | 0.102 | 0.168 | 0.369 | 0.697 |

| host class (instance, vCPU, generation) | hosts | EBs with 500+ applied, per host | ms per applied transaction | ms per reapplied transaction | fixed per EB |
|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current | IOG1, IOG3 | 44 to 64 | -0.02 to 0.59 | -0.126 to 0.486 | -0.35 to 0.21 s |
| r8id.xlarge, 4 vCPU, current | IOG2 | 75 | 0.29 | 0.132 | -0.06 s |
| c8id.xlarge, 4 vCPU, current | PIR1, PIR10, PIR3, PIR4, PIR8 | 45 to 185 | 0.07 to 0.77 | -0.122 to 0.247 | -0.30 to 0.16 s |
| c6id.2xlarge, 8 vCPU, two older | PIR2, PIR5, PIR6 | 85 to 224 | 0.75 to 1.56 | 0.260 to 0.635 | -0.96 to -0.23 s |
| c5d.2xlarge, 8 vCPU, three older | PIR7, PIR9 | 178 to 262 | 0.41 to 1.45 | 0.077 to 0.367 | -0.65 to 0.08 s |
