# UTxO-RPC: implementation tickets

The design is in [README.md, "UTxO-RPC"](README.md#utxo-rpc), and follows [node-to-client](node-to-client.md): when a UTxO-RPC server returns a CertRB, the block's `body.tx` lists the transactions of the EB it certifies. All other blocks are returned as they are on chain. There are no extra rollbacks (`undo`).

The spec is already going this way. [utxorpc/spec#215](https://github.com/utxorpc/spec/pull/215) (open, approved) adds the Leios header and body fields to the unreleased `v1` package, and says: "A block with a Leios certificate has no transactions of its own. Its `body.tx` lists the transactions of the endorser block its certificate certifies, as a Dijkstra node serves the block over local chain sync."

Unlike N2C, the Haskell node's UTxO-RPC server doesn't go through `LocalChainSync`, so the N2C inlining in `chainSyncBlocksServer` doesn't reach its clients. Each server needs its own change.

### What changes for clients

| UTxO-RPC part | With Leios |
|---|---|
| `sync`: `FetchBlock`, `FollowTip`, `DumpHistory` | A CertRB's `body.tx` lists the EB's transactions. `apply`, `undo` and `reset` keep their meaning. |
| `query`: `ReadTx`, `ReadUtxos`, `SearchUtxos` | An EB's transaction, and the outputs it creates, have `block_ref` = the CertRB, where they enter the chain. `ledger_tip` is unchanged: the ledger moves one RB at a time. |
| `submit`: `WaitForTx` | An EB's transaction reaches `STAGE_CONFIRMED` when its CertRB is adopted. |
| `watch`: `WatchTx` | An EB's transaction is `apply`'d with its CertRB, and undone if the CertRB is rolled back. Its `block` is the CertRB. |
| `submit`: `ReadMempool`, `WatchMempool` | Unchanged. |
| Announced (uncertified) EBs | Out of scope for now, as for N2C. |

The EB's hash isn't needed in the CertRB: it's in the previous block's header (`endorser_block_announcement`, added by #215).

---

## 1. Settle the CertRB rules in the spec

**Repository:** `utxorpc/spec`
**Status:** `body.tx` is settled in [#215](https://github.com/utxorpc/spec/pull/215). The rest is not filed.

### Context

#215 says what `body.tx` holds for a CertRB, but not:

- **`native_bytes`.** `AnyChainBlock.native_bytes` could be the block as stored on chain (no transactions) or the N2C form (with the EB's transactions). The draft conformance spec ([#198](https://github.com/utxorpc/spec/issues/198)) says `native_bytes` is the original chain bytes.
- **Where an EB's transactions belong.** `block_ref` in `query`, `block` in `watch`, and when `WaitForTx` reports `STAGE_CONFIRMED`.

### Open question

Which `native_bytes` for a CertRB? We suggest the bytes as stored on chain: they match the header's `block_body_hash`, follow #198, and the parsed `body.tx` already carries the EB's transactions. The catch is that apps decoding `native_bytes` themselves (with Pallas or gouroboros) won't see the EB's transactions there, unlike N2C.

### Acceptance criteria

- [ ] #215 is merged.
- [ ] The spec says what `native_bytes` is for a CertRB.
- [ ] The spec says an EB's transactions belong to the CertRB: it is their `block_ref` in `query` and their `block` in `watch`, and they reach `STAGE_CONFIRMED` with it.
- [ ] #198 has a CertRB test case.

---

## 2. `cardano-rpc`: move to `v1` and fill a CertRB's `body.tx`

**Repository:** `IntersectMBO/cardano-api` (`cardano-rpc`, started in-process by `cardano-node`)
**Depends on:** #1
**Requirements:** **REQ-UtxoRpcInlineCertifiedEbs**, **REQ-UtxoRpcCertifiedOnly**, **UPD-LeiosUtxoRpcServer**
**Tracked in:** [cardano-api#1263](https://github.com/IntersectMBO/cardano-api/issues/1263)

### Context

`cardano-rpc` serves `FetchBlock`, `FollowTip` and `ReadTip` straight from the node's ChainDB, with no N2C round trip ([`Follower.hs`](https://github.com/IntersectMBO/cardano-api/blob/3a950a793ca46ec00a4a79d245cfae7a0ff22893/cardano-rpc/src/Cardano/Rpc/Server/NodeKernelAccess/Internal/Follower.hs#L69-L103)). It builds `body.tx` from the stored block's own transactions ([`Block.hs`](https://github.com/IntersectMBO/cardano-api/blob/3a950a793ca46ec00a4a79d245cfae7a0ff22893/cardano-rpc/src/Cardano/Rpc/Server/Internal/UtxoRpc/Type/Block.hs#L28-L56)). So a CertRB comes out with an empty `body.tx`.

It also compiles against `v1beta`, while #215 adds the Leios fields to `v1` only.

### Task

- Move to `v1` (cardano-api#1263).
- For a CertRB, read the EB's transactions from the LeiosDB and put them in `body.tx`. Do it in two places: the ChainDB follower, which `FollowTip` and `WaitForTx` read from, and the block-by-point read ([`fetchBlock`](https://github.com/IntersectMBO/cardano-api/blob/c2212851b06b9c2acc5bb0bfe1b8a8e8cf2be03a/cardano-rpc/src/Cardano/Rpc/Server/NodeKernelAccess.hs#L255-L270)), which `FetchBlock` and `FollowTip`'s `undo` use. Reuse the consensus code the N2C server uses (`resolveLeiosClosure`), rather than a second copy.
- If the EB's transactions can't be read, fail loudly, as in [node-to-client #1](node-to-client.md#1-never-send-a-certrb-without-its-ebs-transactions).

### Acceptance criteria

- [ ] `FetchBlock` and `FollowTip` return a CertRB with the EB's transactions in `body.tx`.
- [ ] A CertRB in a `FollowTip` `undo` has the same `body.tx` as in its `apply`.
- [ ] `WaitForTx` reports an EB's transaction as confirmed when its CertRB is adopted.
- [ ] A CertRB is never returned without its EB's transactions.
- [ ] The Leios header and body fields from #215 are filled.

---

## 3. Dingo: fill a CertRB's `body.tx` in `sync`

**Repository:** `blinklabs-io/dingo` (and `blinklabs-io/gouroboros`)
**Depends on:** #1
**Requirement:** **REQ-UtxoRpcInlineCertifiedEbs**

### Context

Dingo already stores EBs and indexes their transactions under the CertRB: `ReadTx` returns an EB's transaction with `block_ref` = the CertRB, and `WatchTx` applies and undoes it with the CertRB ([`leios_test.go`](https://github.com/blinklabs-io/dingo/blob/857f7bf0a20b1363ccd6351f57186ca6af38f6cd/api/utxorpc/leios_test.go)).

`sync` doesn't do the same. It maps the stored block with gouroboros ([`sync.go`](https://github.com/blinklabs-io/dingo/blob/857f7bf0a20b1363ccd6351f57186ca6af38f6cd/api/utxorpc/sync.go#L410-L432)), and `DijkstraBlock.Utxorpc()` only maps the block's own transactions ([`dijkstra.go`](https://github.com/blinklabs-io/gouroboros/blob/v0.216.3/ledger/dijkstra/dijkstra.go#L156-L178)). So a CertRB likely comes out with an empty `body.tx`. This is from reading the code, not tested.

### Acceptance criteria

- [ ] `FetchBlock`, `FollowTip` and `DumpHistory` return a CertRB with the EB's transactions in `body.tx`, matching `ReadTx` and `WatchTx`.
- [ ] Served as `v1` once #215 is merged.

---

## 4. Dolos: support Leios blocks

**Repository:** `txpipe/dolos` (and `txpipe/pallas`)
**Depends on:** #1
**Requirements:** **REQ-UtxoRpcInlineCertifiedEbs**, **REQ-UtxoRpcCertifiedOnly**

### Context

Dolos serves UTxO-RPC from blocks it fetches over N2N ([`sync.rs`](https://github.com/txpipe/dolos/blob/34d2b7f619724de0a19da322b04e41deccea7465/src/serve/grpc/v1beta/sync.rs#L23-L40)), so it doesn't get the N2C inlining either. It has no Leios code yet. To return a CertRB with its EB's transactions, it must first fetch and store EBs. Pallas has most of the pieces: [#816](https://github.com/txpipe/pallas/pull/816) (read EBs, merged), [#836](https://github.com/txpipe/pallas/pull/836) (LeiosNotify and LeiosFetch, merged), [#833](https://github.com/txpipe/pallas/pull/833) (map Dijkstra scripts and votes, merged) and [#835](https://github.com/txpipe/pallas/pull/835) (map blocks onto the `v1` schema, built against #215, open).

### Acceptance criteria

- [ ] Dolos fetches and stores the EBs certified on its chain.
- [ ] `sync`, `ReadTx`, `WaitForTx` and `WatchTx` follow the table at the top.

---

## 5. Client SDKs: regenerate against `v1`

**Repositories:** `utxorpc/go-sdk`, `rust-sdk`, `node-sdk`, `python-sdk`, `dotnet-sdk`
**Depends on:** #1

### Context

The SDKs are generated from the spec. They pass `native_bytes` through as bytes and don't decode it, so they need no Leios logic of their own.

### Acceptance criteria

- [ ] Each SDK is regenerated against the `v1` release with #215.
