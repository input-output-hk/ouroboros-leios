| voter_ebs | voters | ebs  | voted | too_late |
|----------:|-------:|-----:|------:|---------:|
| 145761    | 51     | 3073 | 93124 | 52519    |
| EB size, txs | EBs | voters per EB | closure by 3 s / after 3 s / after 7 s or never | validation within 4 s / longer / never |
|---|---:|---:|---:|---:|
| under 2,000 | 192 | 51 | 50 / 49 / 1 % | 83 / 7 / 10 % |
| 2,000 to 4,000 | 2,881 | 51 | 81 / 19 / 0 % | 65 / 33 / 2 % |

| EB size, txs | EBs | voted in time / too late | late: closure arrived after 7 s / validation past 7 s / never validated | EBs with late voters over a quarter | certified, of the EBs the chain could certify |
|---|---:|---:|---:|---:|---:|
| under 2,000 | 192 | 76 / 24 % | 1 / 13 / 9 % | 36 % | 68 % |
| 2,000 to 4,000 | 2,881 | 63 / 37 % | 0 / 35 / 2 % | 50 % | 51 % |
