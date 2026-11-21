EBs of 5,500 to 6,999 transactions: chained closures, certified closures in which 80 % or more of the inputs spend an output of the same block, 70 EBs; old-input closures, certified closures in which 50 % or less of the inputs spend an output of the same block, 0 EBs; the db-sync composition holds 129 certified closures of the class, chained closures 114 (median transaction size 247 B) and old-input closures 0; a host cell resting on fewer than 10 EBs is marked tentative.

| host class (instance, vCPU, generation) | hosts | chained closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | old-input closures: per applied transaction, milliseconds (EBs per host) | per reapplied transaction, microseconds (EBs per host) | EBs validated per host |
|---|---|---|---|---|---|---|
| c8id.xlarge, 4 vCPU, current (IOG) | IOG1, IOG3 | 0.15 to 0.25 (1 to 2) tentative | 76 to 78 (38 to 61) | - | - | 70; - |
| r8id.xlarge, 4 vCPU, current (IOG) | IOG2 | 0.15 (1) tentative | 80 (61) | - | - | 70; - |
| c8id.xlarge, 4 vCPU, current (PIR) | PIR1, PIR10, PIR3, PIR4, PIR8 | 0.19 to 0.26 (1 to 16) tentative | 80 to 100 (26 to 61) | - | - | 70 to 71; - |
| c6id.2xlarge, 8 vCPU, two older (PIR) | PIR2, PIR5, PIR6 | 0.28 to 0.33 (3 to 18) tentative | 117 to 136 (21 to 51) | - | - | 70; - |
| c5d.2xlarge, 8 vCPU, three older (PIR) | PIR7, PIR9 | 0.37 to 0.42 (8 to 21) tentative | 141 to 144 (21 to 31) | - | - | 71; - |

