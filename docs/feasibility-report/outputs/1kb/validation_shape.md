EBs of 1,500 to 2,499 transactions: chained closures, certified closures in which 80 % or more of the inputs spend an output of the same block, 18 EBs; old-input closures, certified closures in which 50 % or less of the inputs spend an output of the same block, 51 EBs; a host cell resting on fewer than 10 EBs is marked tentative.

| host class (instance, vCPU, generation) | hosts | chained closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | old-input closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | EBs validated per host |
|---|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current (IOG) | IOG1, IOG3 | 0.16 to 0.19 (5 to 7) tentative | 80 to 89 (2 to 6) tentative | 0.59 (0 to 7) tentative | 88 to 91 (13 to 32) | 18; 51 |
| r8id.xlarge, 4 vCPU, current (IOG) | IOG2 | 0.20 (8) tentative | 84 (2) tentative | - (0) tentative | 83 (22) | 18; 51 |
| c8id.xlarge, 4 vCPU, current (PIR) | PIR1, PIR10, PIR3, PIR4, PIR8 | 0.24 to 0.34 (4 to 7) tentative | 79 to 104 (2 to 6) tentative | 0.67 to 0.77 (0 to 11) tentative | 82 to 98 (5 to 30) tentative | 18; 51 |
| c6id.2xlarge, 8 vCPU, two older (PIR) | PIR2, PIR5, PIR6 | 0.32 to 0.40 (4 to 8) tentative | 123 to 154 (2 to 9) tentative | 0.97 to 1.09 (0 to 15) tentative | 127 to 141 (7 to 22) tentative | 18; 51 |
| c5d.2xlarge, 8 vCPU, three older (PIR) | PIR7, PIR9 | 0.35 to 0.41 (5 to 7) tentative | 148 to 157 (3 to 5) tentative | 1.13 to 1.19 (1 to 12) tentative | 159 (8 to 10) tentative | 18; 51 |

