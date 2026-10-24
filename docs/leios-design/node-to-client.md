# Node-to-client: implementation tickets

The design is in [README.md, "Node-to-client"](README.md#node-to-client): when `LocalChainSync` sends a CertRB, it adds the certified EB's transactions to the CertRB's body. All other blocks are sent as they are on chain. There are no extra rollbacks.

The prototype already does this (`chainSyncBlocksServer` on the `ouroboros-consensus` [`leios-prototype`](https://github.com/IntersectMBO/ouroboros-consensus/blob/840e789b1cd112e161820a20d30d4546f30e6209/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/ChainSync/Server.hs#L109-L175) branch). The tickets below make it ready to leave the prototype.

---

## 1. Never send a CertRB without its EB's transactions

**Repository:** `ouroboros-consensus`
**Requirement:** **REQ-N2CInlineCertifiedEbs**
**Status:** Not started. All three cases below are still on `leios-prototype`.

### Context

The server sends a CertRB without the EB's transactions, and logs nothing, in three cases. The client gets a block that looks complete but is missing transactions. All three are in `resolve` in [`ChainSync/Server.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/840e789b1cd112e161820a20d30d4546f30e6209/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/ChainSync/Server.hs#L154-L175):

- **Decode failure.** The server can't decode the stored block (`Left _ -> pure sblk`, line 167).
- **Missing closure.** `resolveLeiosClosure` can't read the EB's transactions from the LeiosDB (`Left _ -> pure sblk`, line 172).
- **No known announcement.** The header says the block has a certificate, but the server doesn't know which EB the previous block announced (`prevAnnVar` is `Nothing`), so it falls through to `_ -> pure sblk` (line 174).

None of these should happen:

- The node only adopts a CertRB once it has the EB's transactions (**NEW-LeiosCertRbStagingArea**; `cdbAcquiredLeiosEbs` in the prototype), and [`resolveAndApplyLeiosClosure`](https://github.com/IntersectMBO/ouroboros-consensus/blob/840e789b1cd112e161820a20d30d4546f30e6209/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LedgerDB/Forker.hs#L1069-L1074) calls `error` if they are missing. When the CertRB becomes immutable, its EB is promoted to the immutable LeiosDB (`leiosDbPromoteToImmutable`), and garbage collection only removes volatile data. So the read fails only if the LeiosDB itself fails.
- A CertRB always follows the RB that announced its EB. `prevAnnVar` is set by `setPrev` after a rollback or intersection. A code comment there warns that the lookup might miss the block. It won't: `getBlockComponent` checks the VolatileDB first, then the ImmutableDB, in an order chosen to avoid that race ([`getAnyBlockComponent`](https://github.com/IntersectMBO/ouroboros-consensus/blob/840e789b1cd112e161820a20d30d4546f30e6209/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/ChainDB/Impl/Query.hs#L590-L604)).

If one does happen, the server should fail loudly, not hide it.

### Acceptance criteria

- [ ] In all three cases, the server throws instead of sending the block, ending the client's connection.
- [ ] A test checks that a client syncing from genesis, after the LeiosDB has been garbage-collected, gets every CertRB with its EB's transactions.
- [ ] The misleading `setPrev` comment is removed.

---

## 2. Property test for the `LocalChainSync` server

**Repository:** `ouroboros-consensus`
**Depends on:** #1
**Requirements:** **REQ-N2CBackwardCompatible**, **REQ-N2CInlineCertifiedEbs**, **REQ-N2CCertifiedOnly**

### Acceptance criteria

- [ ] For any chain and any sequence of follower updates (rollbacks, chain switches, reconnections), the client ends with the node's chain, with each CertRB carrying its EB's transactions. The server sends no rollbacks of its own.
- [ ] A client that intersects at an RB that announced an EB still gets the next CertRB with the EB's transactions.
- [ ] Every block other than a CertRB is sent byte-for-byte as stored.
- [ ] The server never sends transactions from an EB that isn't certified on the node's selected chain.

---

## 3. Update CIP-164's `ranking_block` CDDL and "Clients" section

**Repository:** `cardano-foundation/CIPs`
**Status:** Not filed

### Context

[CIP-164's "Clients" section](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0164/README.md#clients) already puts the EB's transactions in the CertRB, which matches this design. Three gaps remain:

- Its [`ranking_block`](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0164/README.md#ranking-block-cddl) CDDL predates the Dijkstra block format, changed in [cardano-ledger#5872](https://github.com/IntersectMBO/cardano-ledger/pull/5872). The prototype and client libraries such as gouroboros already follow the ledger.
- It doesn't say that the EB's transactions are applied before the tick to the CertRB's slot.
- It doesn't say that an EB can't be certified across an epoch boundary. The prototype enforces this: ticking into a new epoch clears the announcement ([`PolyPraos.hs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/840e789b1cd112e161820a20d30d4546f30e6209/ouroboros-consensus-protocol/src/ouroboros-consensus-protocol/Ouroboros/Consensus/Protocol/PolyPraos.hs#L568-L587)). So the announcing RB and the CertRB are always in the same epoch, and clients that see the EB's transactions at the CertRB count them in the right epoch.

### Acceptance criteria

- [ ] `ranking_block` matches the Dijkstra ledger CDDL.
- [ ] "Clients" says the EB's transactions are applied to the state after the announcing RB, before the tick.
- [ ] The CIP says an EB can't be certified across an epoch boundary.

---

## 4. Client libraries: read CertRBs with inlined transactions

**Repositories:** `ogmios`, Kupo, Pallas, `db-sync`, `cardano-wallet`

### Context

Clients decode every block as a Dijkstra block, as usual. A CertRB is different in four ways:

- **Large blocks.** A CertRB with its EB's transactions can be much larger than any block today.
- **`block_body_hash`.** The header's hash covers only the on-chain body, so it doesn't match a CertRB.
- **Certificate and transactions together.** On chain a block can't have both ([`blockMatchesHeader`](https://github.com/IntersectMBO/ouroboros-consensus/blob/840e789b1cd112e161820a20d30d4546f30e6209/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Block.hs#L224-L236) in consensus; [cardano-ledger#6202](https://github.com/IntersectMBO/cardano-ledger/pull/6202), still open, in the ledger), but a CertRB sent over N2C does.
- **Order.** Clients that run their own ledger must apply the EB's transactions before ticking to the CertRB's slot. Otherwise a transaction whose validity interval ends between the two slots fails for the client but not for the node.

### Acceptance criteria

For each client:

- [ ] Decodes Dijkstra blocks.
- [ ] Handles maximum-size CertRBs, tested on a devnet.
- [ ] Doesn't check `block_body_hash` or reject cert-plus-transactions for CertRBs.
- [ ] If it runs a ledger, applies the EB's transactions before the tick.
