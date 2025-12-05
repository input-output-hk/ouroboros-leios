# Run the demo

## Using Nix run (recommended)

You can run the demo directly from the GitHub repository using Nix (requires SSH access):

```shell
nix run github:IntersectMBO/ouroboros-leios#leios-202510-demo
```

Or from a local checkout:

```shell
nix run .#leios-202510-demo
```

The demo uses default values of `REF_SLOT=41` and `SECONDS_UNTIL_REF_SLOT=5`. You can override these:

```shell
SECONDS_UNTIL_REF_SLOT=10 REF_SLOT=200 nix run github:IntersectMBO/ouroboros-leios#leios-202510-demo
```

## Using run-demo.sh directly

Alternatively, you can run the script directly from a dev shell:

```shell
SECONDS_UNTIL_REF_SLOT=5 REF_SLOT=177 DATA="./data" ./run-demo.sh

...
Each row represents a unique block seen by both nodes, joined by hash and slot.
   slot                                               hash     latency_ms
0     2  4e93dab121aaeabf20a6b6112048260fb1b72ed94f10eb...  179118.490342
1    44  bd384ce8792d89da9ab6d11d10fc70a36a2899e6c3b10d...  137309.362409
2    52  23b021f8e2c06e64b10647d9eeb5c9f11e50181f5a5694...  129462.848231
3    53  5ecd12b363657693f31e62421726fcc427788eed6d2fb2...  128463.045544
4    59  0341e8795f13d6bcbd0d1fec0fc03fb75ede8cd6d75999...  122466.373131
5   183  56515bfd5751ca2c1ca0f21050cdb1cd020e396c623a16...     605.664913
6   187  60fd8fc00994ac1d3901f1d7a777edf5b99546a748fc7d...    3269.136876
7   188  48cf5b44cb529d51b5b90c8b7c2572a27a2f22fc8933fe...    6842.006962

Total unique block events matched: 8
```

## Nix build targets

Build an empty Leios DB:

```shell
$ nix build .#leios-empty-db
$ sqlite3 result ".schema"
CREATE TABLE txCache
...
```

Build a busy Leios DB from the manifest:

```shell
$ nix build .#leios-busy-db
$ sqlite3 result ".schema"
CREATE TABLE txCache
...
```

Build a busy Leios schedule from the manifest:

```shell
$ nix build .#leios-busy-db.schedule
$ cat result-schedule
[
  [
    182.9,
    [
      0,
      "adfe0e24083d8dc2fc6192fcd9b01c0a2ad75d7dac5c3745de408ea69eaf62d8",
      28234
...
```
