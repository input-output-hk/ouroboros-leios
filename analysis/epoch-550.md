# Cardano mainnet statistics near Epoch 550


## Snapshot at Epoch 550

To orient ourselves, we look at the situation around Epoch 550.


### Rewards and fees

```sql
select
   earned_epoch as "Epoch Earned"
  , sum(amount) / 1e6 as "Reward [ADA/epoch]"
  , fees / 1e6 as "Fees [ADA/Epoch]"
  from reward
  inner join ada_pots
    on earned_epoch = epoch_no - 1
  where earned_epoch between 545 and 553
  group by earned_epoch, epoch_no, fees
order by earned_epoch desc
;
```

```console
 Epoch Earned |  Reward [ADA/epoch]  |  Fees [ADA/Epoch]  
--------------+----------------------+--------------------
          553 | 7735676.599078000000 | 64560.236707000000
          552 | 7680902.523601000000 | 50927.072843000000
          551 | 7725866.765871000000 | 53017.461145000000
          550 | 7725300.464196000000 | 67431.504009000000
          549 | 7728511.864023000000 | 56324.445971000000
          548 | 7765678.546916000000 | 53136.772606000000
          547 | 7840690.098216000000 | 54873.551989000000
          546 | 7870624.686871000000 | 53377.937268000000
          545 | 7726349.523622000000 | 63417.467271000000
(9 rows)
```


### Treasury and reserve

```sql
select
    epoch_no "Epoch"
  , treasury / 1e6 "Treasury [ADA]"
  , reserves / 1e6 "Reserve [ADA]"
  , fees / 1e6 "Fees [ADA]"
  from ada_pots
  where epoch_no between 545 and 555
order by epoch_no desc
;
```

```console
 Epoch |   Treasury [ADA]    |    Reserve [ADA]    |     Fees [ADA]     
-------+---------------------+---------------------+--------------------
   554 | 1739008615.83819600 | 7227379990.26737400 | 64560.236707000000
   553 | 1734673185.49121300 | 7239343896.06511500 | 50927.072843000000
   552 | 1730343069.06313000 | 7251344361.79792400 | 53017.461145000000
   551 | 1726047077.83648300 | 7263297721.98475800 | 67431.504009000000
   550 | 1721027451.02057900 | 7275303870.39383600 | 56324.445971000000
   549 | 1716669382.76785800 | 7287372980.42086700 | 53136.772606000000
   548 | 1712261860.26103800 | 7299564319.47391400 | 54873.551989000000
   547 | 1707859322.62212200 | 7311783103.86243300 | 53377.937268000000
   546 | 1703528717.03830800 | 7323776141.50259800 | 63417.467271000000
   545 | 1699217928.89060500 | 7335771117.34635300 | 66943.752902000000
(10 rows)
```


### Disposition of rewards

```sql
select
    earned_epoch as "Epoch earned"
  , type as "Recipient"
  , sum(amount) / 1e6 as "Reward [ADA]"
  , sum(amount) / (select sum(amount) from reward where earned_epoch = 550) as "Reward [%/100]"
  from reward
  where earned_epoch = 550
  group by earned_epoch, type
;
```

```console
 Epoch earned | Recipient |     Reward [ADA]     |       Reward [%/100]       
--------------+-----------+----------------------+----------------------------
          550 | leader    | 1628532.454779000000 |     0.21080506348285927427
          550 | member    | 6096268.009417000000 |     0.78913021411542737867
          550 | refund    | 500.0000000000000000 | 0.000064722401713347056331
(3 rows)
```


### Findings

From this data we see that following between Epoch 500 and 501.

- The Reserve dropped 12.0 million ADA.
- The Treasury increased 5.02 million ADA.
- Non-Treasury ADA in circulation increased by 6.99 million ADA.
- SPOs received 1.63 million ADA (21.1%) of the rewards.
- Delegators received 6.10 million ADA (78.9%) of the rewards.


## Averages from Epoch 500 to 550

Other statistics of interest, averaged from Epoch 500 to Epoch 550.

```sql
select
    avg("Transactions") as "Transactions/epoch"
  , sum("Transactions") / count(distinct "Epoch") / 5 / 24 / 60 / 60 as "Transactions/second"
  , avg("Fees [ADA]") as "Fees [ADA/epoch]"
  , sum("Fees [ADA]") / sum("Transactions") as "Fees [ADA/tx]"
  , avg("Block Size [kB]") as "Block Size [kB]"
  , avg("Block Size [kB]") / (select max_block_size / 1000 from epoch_param where epoch_no = 550) as "Block Utilization [%/100]"
  from (
    select
        epoch_no as "Epoch"
      , sum(tx_count) as "Transactions"
      , sum(size) / 1000 / count(*) as "Block Size [kB]"
      from block
      where epoch_no between 500 and 550
      group by epoch_no
  ) txs
  inner join (
    select
        epoch_no as "Epoch"
      , sum(fees) / 1e6 as "Fees [ADA]"
      from ada_pots
      where epoch_no between 500 and 550
      group by epoch_no
  ) fees
    using("Epoch")
;
```

```console
 Transactions/epoch  |  Transactions/second   |  Fees [ADA/epoch]  |     Fees [ADA/tx]      |   Block Size [kB]   | Block Utilization [%/100] 
---------------------+------------------------+--------------------+------------------------+---------------------+---------------------------
 272382.647058823529 | 0.63051538671023965333 | 93157.419716509804 | 0.34200937806581931488 | 17.4117647058823529 |    0.19346405228758169889
(1 row)
```


### Findings

Thus from Epoch 500 to 550 we have the following:

- 272k tx/epoch
- 0.63 tx/second
- Fee of 0.34 ADA/tx
- 19.3% block space utilization

