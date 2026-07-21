# ShelleyBlock byte-preservation acceptance test

Two-node acceptance test for the wire-bytes memo hotfix in
`ouroboros-consensus` (`ShelleyBlock`).

## What it checks

- **NodeA** — relay that syncs the chain from
  `leios-node.play.dev.cardano.org:3001` past the contentious Dijkstra
  block 67555 (header hash
  `70c34f39cf63c8fe9c0f645ef1c6ea3edcf6f72944af43d3eaaf3b40d252761e`).
- **NodeB** — bootstrap set only to `127.0.0.1:3010` (NodeA).

`assert-sync.sh` polls both nodes via `cardano-cli query tip` and passes
once NodeB has selected the same tip as NodeA at a block past 67555.
Without the fix, NodeA re-encodes the body of block 67555 on
disk-write; the re-encoded body no longer matches the `hbBodySize` /
`hbBodyHash` committed to in the header, and NodeB rejects the block
over BlockFetch and cannot advance past 67554.

## Workflow

- **Prerequisite** — extract a `leios3-rel-c-1` snapshot
  (`leios.chain.tar.zst` + `leios.leiosdb.tar.zst`) into
  `$WORKING_DIR/nodeA/` before running the harness. The harness does
  not download; it only prunes.
- **PruneImmutable** — iteratively deletes the highest-numbered
  `.chunk`/`.primary`/`.secondary` trio from `nodeA/db/immutable/` until
  a `grep` for the contentious block header hash
  (`70c34f39…d252761e`, which normally lives in block 67556's `hbPrev`)
  no longer hits any chunk. Also wipes `nodeA/db/volatile/`. Whatever
  we chopped, NodeA re-fetches from IOG.
- **NodeA** — points at `leios-node.play.dev.cardano.org:3001` and
  syncs the trimmed tail plus everything past 67555 to current tip.
- **NodeB / AssertSync** — as above.

## Running

Point `CARDANO_NODE` at the further-fixed build and just launch:

```shell
CARDANO_NODE=/path/to/further-fixed/cardano-node ./run.sh
```

Everything runs automatically. Exit code follows AssertSync: `0` on
pass, non-zero on timeout or tip mismatch.

Tunables (via env):

| Var             | Default             | Meaning                                     |
|-----------------|---------------------|---------------------------------------------|
| `WORKING_DIR`   | `./tmp-acceptance`  | Where each node's `db/`, `node.log` land    |
| `TARGET_BLOCK`  | `67556`             | Min block # NodeB must reach (past 67555)   |
| `TIMEOUT`       | `1800` (s)          | Give up after this long                     |
| `POLL_INTERVAL` | `5` (s)             | Between tip polls                           |
| `NETWORK_MAGIC` | `164`               | Matches `testnet/config` genesis            |
