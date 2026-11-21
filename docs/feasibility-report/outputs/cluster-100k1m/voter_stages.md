| voter_ebs | voters | ebs  | voted  | too_late |
|----------:|-------:|-----:|-------:|---------:|
| 150734    | 51     | 3133 | 118432 | 32105    |
| EB size, txs | EBs | voters per EB | closure by 3 s / after 3 s / after 7 s or never | validation within 4 s / longer / never |
|---|---:|---:|---:|---:|
| under 2,000 | 74 | 51 | 61 / 37 / 2 % | 94 / 1 / 5 % |
| 2,000 to 4,000 | 3,059 | 51 | 76 / 24 / 0 % | 83 / 17 / 1 % |

| EB size, txs | EBs | voted in time / too late | late: closure arrived after 7 s / validation past 7 s / never validated | EBs with late voters over a quarter | certified, of the EBs the chain could certify |
|---|---:|---:|---:|---:|---:|
| under 2,000 | 74 | 88 / 9 % | 2 / 4 / 3 % | 18 % | 77 % |
| 2,000 to 4,000 | 3,059 | 78 / 22 % | 0 / 21 / 1 % | 33 % | 69 % |
