| voter_ebs | voters | ebs  | voted  | too_late |
|----------:|-------:|-----:|-------:|---------:|
| 137053    | 51     | 2810 | 136838 | 215      |
| EB size, txs | EBs | voters per EB | closure by 3 s / after 3 s / after 7 s or never | validation within 4 s / longer / never |
|---|---:|---:|---:|---:|
| under 2,000 | 10 | 51 | 96 / 3 / 1 % | 99 / 0 / 1 % |
| 2,000 to 4,000 | 2,800 | 51 | 90 / 10 / 0 % | 100 / 0 / 0 % |

| EB size, txs | EBs | voted in time / too late | late: closure arrived after 7 s / validation past 7 s / never validated | EBs with late voters over a quarter | certified, of the EBs the chain could certify |
|---|---:|---:|---:|---:|---:|
| under 2,000 | 10 | 99 / 1 % | 1 / 0 / 0 % | 0 % | 100 % |
| 2,000 to 4,000 | 2,800 | 100 / 0 % | 0 / 0 / 0 % | 0 % | 99 % |
