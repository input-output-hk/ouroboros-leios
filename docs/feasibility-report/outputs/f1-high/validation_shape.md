EBs of 1,000 to 1,499 transactions: chained closures, certified closures in which 80 % or more of the inputs spend an output of the same block, 147 EBs; old-input closures, certified closures in which 50 % or less of the inputs spend an output of the same block, 156 EBs; a host cell resting on fewer than 10 EBs is marked tentative.

| host class (instance, vCPU, generation) | hosts | chained closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | old-input closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | EBs validated per host |
|---|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current (IOG) | IOG1, IOG3 | 0.16 to 0.17 (16 to 21) | 79 to 84 (62 to 67) | 0.50 (0 to 8) tentative | 88 to 91 (107 to 144) | 145 to 147; 155 to 156 |
| r8id.xlarge, 4 vCPU, current (IOG) | IOG2 | 0.20 (33) | 92 (60) | 0.60 (1) tentative | 98 (131) | 147; 156 |
| c8id.xlarge, 4 vCPU, current (PIR) | PIR1, PIR10, PIR3, PIR4, PIR8 | 0.18 to 0.24 (19 to 35) | 82 to 93 (32 to 69) | 0.50 to 0.59 (0 to 37) tentative | 91 to 109 (73 to 145) | 145 to 147; 154 to 156 |
| c6id.2xlarge, 8 vCPU, two older (PIR) | PIR2, PIR5, PIR6 | 0.27 to 0.34 (28 to 60) | 116 to 153 (20 to 55) | 0.69 to 0.81 (14 to 53) | 126 to 163 (46 to 120) | 147; 156 |
| c5d.2xlarge, 8 vCPU, three older (PIR) | PIR7, PIR9 | 0.33 to 0.37 (54 to 71) | 135 to 141 (15 to 21) | 0.65 to 1.01 (31 to 36) | 147 to 148 (48 to 94) | 147; 156 to 157 |
| operators (21 nodes with enough EBs under both selections): lower quartile / median / upper quartile node | | 0.41 / 0.90 / 1.19 | 242 / 494 / 642 | 0.99 / 1.77 / 2.69 | 226 / 508 / 669 | 119 to 290; 118 to 307 |

