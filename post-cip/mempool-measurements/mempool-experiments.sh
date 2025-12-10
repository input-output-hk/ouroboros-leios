#!/usr/bin/env bash


export PATH=/extra/iohk/bin:$PATH
export CARDANO_NODE_NETWORK_ID=mainnet
export CARDANO_NODE_SOCKET_PATH=/extra/iohk/networks/mainnet/node.socket


# First experiment

for i in {0..19}
do
  echo -n "$i: "
  head -c 1536 /dev/urandom | basenc --base16 --wrap=128 | sed -e 's/^.*$/{"bytes":"&"}/' -e '2,$s/^/, /' -e '$a]}}' -e '1s/^/  /' -e '1i{"1536":{"list":[' > "tx-$i.metadata"
  cardano-cli conway transaction build \
    --tx-in "fa7c2496cff58610c92ee8fb0a8800d336e144d60e1e13155cc52c120e605bb7#$i" \
    --change-address addr1qy9prvx8ufwutkwxx9cmmuuajaqmjqwujqlp9d8pvg6gupcvluken35ncjnu0puetf5jvttedkze02d5kf890kquh60sut9jg7 \
    --json-metadata-detailed-schema \
    --metadata-json-file "tx-$i.metadata" \
    --out-file "tx-$i.unsigned"
  cardano-cli conway transaction sign \
    --signing-key-file payment.skey \
    --tx-body-file "tx-$i.unsigned" \
    --out-file "tx-$i.signed"
  cardano-cli conway transaction txid \
    --tx-file "tx-$i.signed" \
    > "tx-$i.txid"
done

for i in {0..19}
do
  (
    cardano-cli conway transaction submit --tx-file "tx-$i.signed"
    date -u > "tx-$i.submitted"
  ) &
done
wait

# Wed Nov 26 02:01:16 PM UTC 2025

# 9161c5cd50f2fedc5e2c86ad17720b03f8cc232cee3cf39d073f6695da2697e7
# 59b7d5965f7ccaf31c207999d48478ec112c2a8c1a18d076d56ecae14d6045af
# 62f7aa82f8aa193c6a181ccb0ae050e037fa91e01a82acc09725a7ff2b4b5999
# 5cc3dc20a744338a713709303eeae9fccc4b035e4b9b1aeaf483479125a7a030
# 1f176c316231e138623364a4bed8574ceb070b2562c6867cf012e1c2cded6d7d
# 6d71d94cffbffc9667925db20f13d4f060f67826fb3d541edbe79d86c58ea6d1
# 0ed21a6ff7e05561a73ebe454cbfc7bbea04c443529c23ec6440bb29724bcb4f
# 860cb1697749d2ab49bca6219d50b05b2da2c4183cae32fa4ed3d2be8870fe70
# 8304148164ed0f943aa502173879bd66f0da18d22860c0b754acd9b894aa784d
# 95960b004be8e5b889f1df1ec29356e061ebf9577b83a68a193d3f6aeb11b4ea
# 98f0d4138828af650c871a8f142d46886ddb05231eb2c68876b5e60b735c2b2e
# aff3e9160b309eefdf05ce8755bb075929315b1cdb68e1456fae0c8f5e723636
# fdec199a2d69145fe191498e3225b595e10d459a99a05253cfd6b333f6d27db6
# f30a474797b6f0ed878aca7b06c8895ccd24660b389045f097aeb07afc69fa97
# 9ce69e0b5f63fdc9480f85a06977e86e2e1230b2815d7490de5192672c89e3cf
# a553692d0e5df1a8699f4de3bca2e2aad0dc2d7383c244a887d870c32aab5a1a
# c3db88205930be7012f0b37e64870d6f4817449f4de36c963cb01bd73bc78c5d
# 94124f0a7df8ad4b1cae4d374ba145d547bda5ebee44e6a767e955f649aeb593
# 711d440f3cacafe0db344e7065f60f7482d180326cf0387c6a625f16be0248da
# d2c6825db389345be7be53bc34b6e77e76a46473608092075a7577aead94252b


# Second experiment

for i in {0..19}
do
  echo -n "$i: "
  head -c 8192 /dev/urandom | basenc --base16 --wrap=128 | sed -e 's/^.*$/{"bytes":"&"}/' -e '2,$s/^/, /' -e '$a]}}' -e '1s/^/  /' -e '1i{"1536":{"list":[' > "tx-$i.metadata"
  cardano-cli conway transaction build \
    --tx-in "3a22614b95bea58c73152c28b360ecf42e24c90045fd8bff068de76c932415c1#$i" \
    --change-address addr1qy9prvx8ufwutkwxx9cmmuuajaqmjqwujqlp9d8pvg6gupcvluken35ncjnu0puetf5jvttedkze02d5kf890kquh60sut9jg7 \
    --json-metadata-detailed-schema \
    --metadata-json-file "tx-$i.metadata" \
    --out-file "tx-$i.unsigned"
  cardano-cli conway transaction sign \
    --signing-key-file payment.skey \
    --tx-body-file "tx-$i.unsigned" \
    --out-file "tx-$i.signed"
  cardano-cli conway transaction txid \
    --tx-file "tx-$i.signed" \
    > "tx-$i.txid"
done

for i in {0..19}
do
  (
    cardano-cli conway transaction submit --tx-file "tx-$i.signed"
    date -u > "tx-$i.submitted"
  ) &
  sleep 0.05s
done
wait

# 12be7f48a0bdd33a62df89c44b1ef6810d4d54ea26e7a4bf4c43e1fa3d8aa18f : Wed Nov 26 02:23:16 PM UTC 2025
# 4906885ebf56d0806119f2d57128a9d20aa90867912a67f2faf6705be3febf6f : Wed Nov 26 02:23:16 PM UTC 2025
# d8343e735a6fb5512bdd68fa076525ae7815fb7acd649cd11d927a7186fb6b30 : Wed Nov 26 02:23:16 PM UTC 2025
# 315c821bd42e69fd03425aab4564408bcdf9ce0de6e8f551259011a8aaac650a : Wed Nov 26 02:23:16 PM UTC 2025
# fa2a8d3824f0674f830889f2b1b0c9f998a610a7723c9a73cf7ca6b5b57f7f28 : Wed Nov 26 02:23:16 PM UTC 2025
# 93fb26a1fde07afd41d86f2bb802dc7cd14827de5eac7094ab746dbdb77c2f06 : Wed Nov 26 02:23:16 PM UTC 2025
# 0f55de2cd1cc3354297c855eb4ea62c4d6cf30e26fe9e010b9697bd553336e6c : Wed Nov 26 02:23:16 PM UTC 2025
# 68b2fb3763882dddd54867769ad2b6cd2cdb25bba93d36fef2d8253d5149873d : Wed Nov 26 02:23:17 PM UTC 2025
# d51d5d9ed2663194224596fb0c1a5e125f55647866a44ad9d3fc783a24ac504e : Wed Nov 26 02:23:17 PM UTC 2025
# 80e714ae65fdc9d6725402629624fd7d11b0cafd876de397496304e2423d6ff7 : Wed Nov 26 02:23:17 PM UTC 2025
# 2f93d4bade70efb1459923d14b1d5380565bd0313a9850b69c6b91c58451c205 : Wed Nov 26 02:23:17 PM UTC 2025
# 72723e169663f43ac7d2ff2a0fbe919a24cb68c7508b2ad27f373dabd404ab99 : Wed Nov 26 02:23:17 PM UTC 2025
# e9ffc14e92baccadc6d734630b3675c3d60ffbe2650135684af2fe409e297f40 : Wed Nov 26 02:23:17 PM UTC 2025
# 563fc090ddace40cd0ec03f7812cd78aa4d946958ee5c74f9ad340b6ebb5b9d7 : Wed Nov 26 02:23:17 PM UTC 2025
# 3753370103e9cddccf11de6915922147daf0430422c4708e8f9d8a794ee8ad47 : Wed Nov 26 02:23:17 PM UTC 2025
# d798ed9489cdd977fa2155894edc27d3cb0137fcdb9454133448a242383e1384 : Wed Nov 26 02:23:17 PM UTC 2025
# 6f9c85a92c040bd8a6c15d8242a5aadb25b6314fa3206dd40a380dfbd9671d5e : Wed Nov 26 02:23:17 PM UTC 2025
# 5f63700878516370ecce4582e078865087cc7aa1646fe7fc06906d5f63ca9109 : Wed Nov 26 02:23:17 PM UTC 2025
# 56d345d0c94ed0fce3b0ff6504d5215931133b3f30eb330b21f1855faedc77fa : Wed Nov 26 02:23:17 PM UTC 2025


# Expenses

psql -h thelio mainnet
select distinct
    block.time
  , encode(tx.hash, 'hex') as tx_hash
  , tx.fee
  from tx
  inner join block
    on block.id = tx.block_id
  inner join tx_in
    on tx_in.tx_in_id = tx.id
  inner join tx_out
    on (tx_out.tx_id, tx_out.index) = (tx_in.tx_out_id, tx_out_index)
  where block.time >= '2025-11-26 12:00:00'
    and tx_out.address = 'addr1qy9prvx8ufwutkwxx9cmmuuajaqmjqwujqlp9d8pvg6gupcvluken35ncjnu0puetf5jvttedkze02d5kf890kquh60sut9jg7'
order by 1, 2
;
EOI

#         time         |                             tx_hash                              |  fee
# ---------------------+------------------------------------------------------------------+--------
#  2025-11-26 13:34:05 | fa7c2496cff58610c92ee8fb0a8800d336e144d60e1e13155cc52c120e605bb7 | 251169
#  2025-11-26 14:01:19 | 0ed21a6ff7e05561a73ebe454cbfc7bbea04c443529c23ec6440bb29724bcb4f | 241533
#  2025-11-26 14:01:19 | 1f176c316231e138623364a4bed8574ceb070b2562c6867cf012e1c2cded6d7d | 241533
#  2025-11-26 14:01:19 | 59b7d5965f7ccaf31c207999d48478ec112c2a8c1a18d076d56ecae14d6045af | 241533
#  2025-11-26 14:01:19 | 5cc3dc20a744338a713709303eeae9fccc4b035e4b9b1aeaf483479125a7a030 | 241533
#  2025-11-26 14:01:19 | 62f7aa82f8aa193c6a181ccb0ae050e037fa91e01a82acc09725a7ff2b4b5999 | 241533
#  2025-11-26 14:01:19 | 6d71d94cffbffc9667925db20f13d4f060f67826fb3d541edbe79d86c58ea6d1 | 241533
#  2025-11-26 14:01:19 | 711d440f3cacafe0db344e7065f60f7482d180326cf0387c6a625f16be0248da | 241533
#  2025-11-26 14:01:19 | 8304148164ed0f943aa502173879bd66f0da18d22860c0b754acd9b894aa784d | 241533
#  2025-11-26 14:01:19 | 860cb1697749d2ab49bca6219d50b05b2da2c4183cae32fa4ed3d2be8870fe70 | 241533
#  2025-11-26 14:01:19 | 9161c5cd50f2fedc5e2c86ad17720b03f8cc232cee3cf39d073f6695da2697e7 | 241533
#  2025-11-26 14:01:19 | 94124f0a7df8ad4b1cae4d374ba145d547bda5ebee44e6a767e955f649aeb593 | 241533
#  2025-11-26 14:01:19 | 95960b004be8e5b889f1df1ec29356e061ebf9577b83a68a193d3f6aeb11b4ea | 241533
#  2025-11-26 14:01:19 | 9ce69e0b5f63fdc9480f85a06977e86e2e1230b2815d7490de5192672c89e3cf | 241533
#  2025-11-26 14:01:19 | a553692d0e5df1a8699f4de3bca2e2aad0dc2d7383c244a887d870c32aab5a1a | 241533
#  2025-11-26 14:01:19 | aff3e9160b309eefdf05ce8755bb075929315b1cdb68e1456fae0c8f5e723636 | 241533
#  2025-11-26 14:01:19 | c3db88205930be7012f0b37e64870d6f4817449f4de36c963cb01bd73bc78c5d | 241533
#  2025-11-26 14:01:19 | d2c6825db389345be7be53bc34b6e77e76a46473608092075a7577aead94252b | 241533
#  2025-11-26 14:01:19 | f30a474797b6f0ed878aca7b06c8895ccd24660b389045f097aeb07afc69fa97 | 241533
#  2025-11-26 14:01:19 | fdec199a2d69145fe191498e3225b595e10d459a99a05253cfd6b333f6d27db6 | 241533
#  2025-11-26 14:18:11 | 8ad72acb470abf3153d3c95026f253cd19a3c37531ace0ee55226edae73f841f | 290417
#  2025-11-26 14:21:09 | 3a22614b95bea58c73152c28b360ecf42e24c90045fd8bff068de76c932415c1 | 224197
#  2025-11-26 14:23:46 | 0f55de2cd1cc3354297c855eb4ea62c4d6cf30e26fe9e010b9697bd553336e6c | 543549
#  2025-11-26 14:23:46 | 12be7f48a0bdd33a62df89c44b1ef6810d4d54ea26e7a4bf4c43e1fa3d8aa18f | 543549
#  2025-11-26 14:23:46 | 315c821bd42e69fd03425aab4564408bcdf9ce0de6e8f551259011a8aaac650a | 543549
#  2025-11-26 14:23:46 | 4906885ebf56d0806119f2d57128a9d20aa90867912a67f2faf6705be3febf6f | 543549
#  2025-11-26 14:23:46 | 55b2dc844816545c834a97b4abd484e738dc08a6b1cfffc2e4209e7da1d2cc94 | 543549
#  2025-11-26 14:23:46 | 68b2fb3763882dddd54867769ad2b6cd2cdb25bba93d36fef2d8253d5149873d | 543549
#  2025-11-26 14:23:46 | 93fb26a1fde07afd41d86f2bb802dc7cd14827de5eac7094ab746dbdb77c2f06 | 543549
#  2025-11-26 14:23:46 | d8343e735a6fb5512bdd68fa076525ae7815fb7acd649cd11d927a7186fb6b30 | 543549
#  2025-11-26 14:23:46 | fa2a8d3824f0674f830889f2b1b0c9f998a610a7723c9a73cf7ca6b5b57f7f28 | 543549
#  2025-11-26 14:23:47 | 2f93d4bade70efb1459923d14b1d5380565bd0313a9850b69c6b91c58451c205 | 543549
#  2025-11-26 14:23:47 | 3753370103e9cddccf11de6915922147daf0430422c4708e8f9d8a794ee8ad47 | 543549
#  2025-11-26 14:23:47 | 563fc090ddace40cd0ec03f7812cd78aa4d946958ee5c74f9ad340b6ebb5b9d7 | 543549
#  2025-11-26 14:23:47 | 5f63700878516370ecce4582e078865087cc7aa1646fe7fc06906d5f63ca9109 | 543549
#  2025-11-26 14:23:47 | 6f9c85a92c040bd8a6c15d8242a5aadb25b6314fa3206dd40a380dfbd9671d5e | 543549
#  2025-11-26 14:23:47 | 72723e169663f43ac7d2ff2a0fbe919a24cb68c7508b2ad27f373dabd404ab99 | 543549
#  2025-11-26 14:23:47 | 80e714ae65fdc9d6725402629624fd7d11b0cafd876de397496304e2423d6ff7 | 543549
#  2025-11-26 14:23:47 | d51d5d9ed2663194224596fb0c1a5e125f55647866a44ad9d3fc783a24ac504e | 543549
#  2025-11-26 14:23:47 | d798ed9489cdd977fa2155894edc27d3cb0137fcdb9454133448a242383e1384 | 543549
#  2025-11-26 14:23:47 | e9ffc14e92baccadc6d734630b3675c3d60ffbe2650135684af2fe409e297f40 | 543549
#  2025-11-26 14:24:05 | 56d345d0c94ed0fce3b0ff6504d5215931133b3f30eb330b21f1855faedc77fa | 543549

