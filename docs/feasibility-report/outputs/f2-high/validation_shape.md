EBs of 2,000 to 4,999 transactions: chained closures, certified closures in which 80 % or more of the inputs spend an output of the same block, 263 EBs; old-input closures, certified closures in which 50 % or less of the inputs spend an output of the same block, 179 EBs; a host cell resting on fewer than 10 EBs is marked tentative.

| host class (instance, vCPU, generation) | hosts | chained closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | old-input closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | EBs validated per host |
|---|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current (IOG) | IOG1, IOG3 | 0.18 (25 to 39) | 79 to 81 (153 to 166) | 0.84 to 1.07 (1 to 6) tentative | 78 to 79 (101 to 134) | 259 to 260; 181 to 182 |
| r8id.xlarge, 4 vCPU, current (IOG) | IOG2 | 0.19 (39) | 82 (164) | 0.88 (3) tentative | 78 (122) | 260; 182 |
| c8id.xlarge, 4 vCPU, current (PIR) | PIR1, PIR10, PIR3, PIR4, PIR8 | 0.21 to 0.23 (36 to 57) | 80 to 102 (119 to 164) | 0.86 to 1.22 (2 to 21) tentative | 80 to 98 (80 to 139) | 259 to 266; 180 to 183 |
| c6id.2xlarge, 8 vCPU, two older (PIR) | PIR2, PIR5, PIR6 | 0.31 to 0.32 (50 to 73) | 118 to 138 (108 to 152) | 1.28 to 1.42 (3 to 16) tentative | 119 to 133 (74 to 118) | 261 to 263; 178 to 183 |
| c5d.2xlarge, 8 vCPU, three older (PIR) | PIR7, PIR9 | 0.33 to 0.37 (51 to 76) | 142 to 151 (103 to 126) | 1.63 to 1.66 (6 to 13) tentative | 147 to 151 (79 to 98) | 260 to 269; 183 to 184 |
| operators (8 nodes with enough EBs under both selections): lower quartile / median / upper quartile node | | 0.26 / 0.45 / 0.68 | 126 / 212 / 304 | 1.21 / 1.88 / 3.74 | 129 / 219 / 309 | 176 to 337; 123 to 243 |

