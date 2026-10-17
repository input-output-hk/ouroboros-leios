# Node-to-client: implementation tickets


## 1. Append, don't replace, in `inlineLeiosClosure`

**Repository:** `ouroboros-consensus`
**Requirement:** **REQ-N2CInlineCertifiedEbs**

### Context

RB⁺ is RB with the EB's transactions added after RB's own, in the body's transaction list ([`block_body`](https://github.com/IntersectMBO/cardano-ledger/blob/d93c654699c8f10c883a625168f65dd387abc695/eras/dijkstra/impl/cddl/data/dijkstra.cddl#L109-L113) in the Dijkstra ledger CDDL: `[transactions, leios_certificate / nil, peras_certificate / nil]`). `inlineLeiosClosure` (Shelley instance in `Shelley/Ledger/Leios.hs`) currently replaces the list. That works for the prototype's CertRBs, whose list is empty, but would drop RB's own transactions.

### Task

- Change `inlineLeiosClosure` to append the EB's transactions to the existing list.
- Check its other callers still get what they expect: `resolveLeiosBlock` in `Storage/LedgerDB/Forker.hs`, and `db-analyser` (`Cardano/Tools/DBAnalyser/Leios.hs`).

### Acceptance criteria

- [ ] For a block with transactions, the result has the block's transactions followed by the EB's, in order.
- [ ] For a block with an empty list, the result is the same as before.
- [ ] Other callers are checked and, if needed, updated.

---

## 2. Send RB⁺ in place of the announcing RB (rules 1 and 2)

**Repository:** `ouroboros-consensus`
**Depends on:** #1
**Requirements:** **REQ-N2CInlineCertifiedEbs**, **REQ-N2CCertifiedOnly**

### Context

The prototype (`chainSyncBlocksServer`, [`cbd1003`](https://github.com/IntersectMBO/ouroboros-consensus/commit/cbd100331abaf65d20e9362c75039db0ff50c080), release `prototype-2026w40a`; [#898](https://github.com/input-output-hk/ouroboros-leios/issues/898)) inlines the EB's transactions in the CertRB. The ledger applies them at RB, so clients get a different history from the node:

- **Validity intervals.** A transaction whose `invalid_hereafter` falls between the two blocks' slots was valid when the ledger applied it, but the client sees it in a block after it expired.
- **Epoch boundaries.** If the two blocks are in different epochs, the client counts the transactions in the wrong epoch: the wrong stake snapshot for delegations and withdrawals, the wrong protocol parameters for fees, and governance actions in the wrong epoch.
- **Timestamps.** Every transaction appears at least the certificate inclusion delay ($3 \times L_\text{hdr} + L_\text{vote} + L_\text{diff}$) later than it was applied.

### Task

All changes are in the follower wrapper of `chainSyncBlocksServer` (`wrapFollower`). `chainSyncServerForFollower` and the `ChainDB` follower don't change.

- **Build RB⁺ from RB's own announcement** (`headerLeiosAnnouncement`). Remove `prevAnnVar` and `setPrev`, which tracked the previous block's announcement.
- **Add wrapper state:**
  - a queue of pending `ChainUpdate`s, drained by `followerInstruction` and `followerInstructionBlocking` before asking the inner follower. One update from the inner follower can become up to three for the client.
  - the client's tip: its point, its parent's point, and, if it is an RB that announced an EB, whether the client got RB or RB⁺.
- **Rule 1: lookahead.** Before sending an RB that announced an EB, ask the inner follower for the next instruction without blocking (`followerInstruction`):

  | Next instruction | Send | Then |
  |---|---|---|
  | `AddBlock` of a block with `headerContainsLeiosCert` | RB⁺ | Queue the CertRB |
  | Any other `AddBlock`, or a `RollBack` | RB | Queue the instruction |
  | `Nothing` (RB is at the tip) | RB | — |

  A queued CertRB goes through the same step when it's sent, because it can announce an EB of its own.
- **Rule 2: certificate arrives later.** If the inner follower yields a CertRB while the client has plain RB, send `RollBack` to RB's parent, then RB⁺, then the CertRB. Record RB's parent when sending RB, so no lookup is needed. The inner follower doesn't move.

### Acceptance criteria

- [ ] A client catching up from behind the tip gets RB⁺ directly, with no extra rollback.
- [ ] A client at the tip gets RB, then a one-block rollback, RB⁺ and the CertRB when the CertRB arrives.
- [ ] RB is sent plain when its EB isn't certified.
- [ ] CertRBs are sent unchanged.
- [ ] `prevAnnVar` and `setPrev` are removed, along with the misleading `setPrev` comment about a possible race.

---

## 3. Roll back one block deeper on chain switch or reconnection (rule 3)

**Repository:** `ouroboros-consensus`
**Depends on:** #2

### Context

Two cases leave the server unsure whether the client has RB or RB⁺:

- the node switches to a chain that keeps RB but changes whether its EB is certified.
- a client reconnects at an RB that announced an EB.

After `FindIntersect`, the inner follower's first instruction is a `RollBack` to the intersection, so both cases arrive as a `RollBack`.

### Task

- When a `RollBack` lands on an RB that announced an EB, roll back to RB's parent instead. Read RB from the `ChainDB` (`getBlockComponent`) and send it again through rule 1.
- Look up RB's parent point. RB's header gives only the parent's hash.

One block deeper is always enough, because the parent's contents don't depend on what comes after RB.

### Open question

How to look up the parent's point. The current chain fragment (`getCurrentChain`) covers the last k blocks and its anchor. A rollback of k + 1 blocks reaches below the anchor, into the ImmutableDB.

### Acceptance criteria

- [ ] A chain switch that keeps RB but changes whether its EB is certified leaves the client with the right version of RB.
- [ ] A client that reconnects at an RB that announced an EB ends with the right version of RB.
- [ ] Rollbacks of k + 1 blocks work.
- [ ] A failed parent lookup fails loudly, rather than sending a wrong block.

---

## 4. Property test for the `LocalChainSync` server

**Repository:** `ouroboros-consensus`
**Depends on:** #2, #3
**Requirements:** **REQ-N2CInlineCertifiedEbs**, **REQ-N2CCertifiedOnly**

### Task

Add a property test for the wrapper in `chainSyncBlocksServer`.

### Acceptance criteria

- [ ] For any chain and any sequence of follower updates (rollbacks, chain switches, reconnections), the client ends with the node's chain, with each RB whose EB is certified replaced by its RB⁺.
- [ ] A client catching up from behind the tip sees no extra rollback.
- [ ] The server never inlines an EB that isn't certified on the node's selected chain.

---

## 5. Fail loudly when an EB closure is missing

**Repository:** `ouroboros-consensus`
**Status:** In progress on branch `leios-1106-n2c-fail-missing-closure`, which throws `CertRbClosureUnavailable`; not yet released.

### Context

If `resolveLeiosClosure` can't read the EB's transactions from the LeiosDB, the released prototype sends the block without them and logs nothing. The client gets a block that looks valid, matches its header hash, and is missing transactions. Chain selection should make this impossible, because the node never adopts a CertRB without its closure (**NEW-LeiosCertRbStagingArea**), but nothing tests it.

### Acceptance criteria

- [ ] The server throws instead of sending the block, ending the client's connection.
- [ ] A test checks that chain selection never adopts a CertRB whose closure is missing.

---

## 6. Fail loudly when a block can't be decoded

**Repository:** `ouroboros-consensus`

### Context

When the server can't decode a stored block, it sends it unchanged (`Left _ -> pure sblk` in `serveBlockWithLeiosClosure`). As in #5, the client gets a block that looks valid and is missing the EB's transactions.

### Acceptance criteria

- [ ] A decode failure throws instead of sending the block.

---

## 7. Build each RB⁺ once and share it across clients

**Repository:** `ouroboros-consensus`
**Depends on:** #2

### Context

With several clients (indexers), the node decodes each block, adds the EB's transactions and re-encodes it once per client.

### Acceptance criteria

- [ ] Each RB⁺ is built once and served to every client from the cache.
- [ ] The cache is bounded.

---

## 8. Bump the `ouroboros-consensus` pin

**Repository:** `cardano-node`
**Depends on:** #2–#7

### Context

`cardano-node` has no N2C protocol logic of its own; it only wires the LeiosDB configuration through. The current pin is `83c0b07` (`prototype-2026w40a`).

### Acceptance criteria

- [ ] `cabal.project` points at an `ouroboros-consensus` commit with #2–#7.

---

## 9. Update CIP-164's "Clients" section and `ranking_block` CDDL

**Repository:** `cardano-foundation/CIPs`
**Status:** Not filed

### Context

[CIP-164's "Clients" section](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0164/README.md#clients) puts the EB's transactions in the CertRB. Its [`ranking_block`](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0164/README.md#ranking-block-cddl) CDDL predates the Dijkstra ledger's block format, changed in [cardano-ledger#5872](https://github.com/IntersectMBO/cardano-ledger/pull/5872). The prototype and client libraries such as gouroboros already follow the ledger.

### Acceptance criteria

- [ ] "Clients" says EB transactions go in RB⁺, delivered with `RollBackward` / `RollForward`.
- [ ] `ranking_block` matches the Dijkstra ledger CDDL.

---

## 10. Client libraries: read RB⁺ and handle the rollbacks

**Repositories:** `ogmios`, Kupo, Pallas, `db-sync`, `cardano-wallet`

### Context

Clients receive normal Dijkstra blocks, but three things are new:

- **Large blocks.** RB⁺ can be much larger than any block today.
- **Rollbacks at the tip.** One one-block rollback for each CertRB, [about half of all blocks under load](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0164/README.md#feasible-protocol-parameters). The block sent after the rollback has the same header hash as the block removed, so clients can recognise these and skip costly undo work.
- **`block_body_hash`.** The header's `block_body_hash` covers only the on-chain body, so it doesn't match RB⁺. Clients mustn't check it against RB⁺.

On the Musashi testnet (`prototype-2026w35` image, `cardano-node` `6a540bd`), `cardano-cli` from the same release can query the tip and UTxO, build transactions and submit them. Ogmios, Kupo and Blockfrost can't read its blocks yet, and none is hosted for the testnet. On a local proto-devnet with `prototype-2026w35` and `prototype-2026w39`, a Pallas client received CertRBs of up to 6,603 transactions (1.8 MB).

### Status (October 2026)

| Client | Dijkstra decoding | Large blocks (source read, September 2026) |
|---|---|---|
| Pallas | On the unreleased `dijkstra` branch ([pallas#800](https://github.com/txpipe/pallas/pull/800); EBs in [#816](https://github.com/txpipe/pallas/pull/816)) | No size limit or timeout found |
| `cardano-wallet` | In progress ([#5209](https://github.com/cardano-foundation/cardano-wallet/issues/5209)) | No size limit or timeout found |
| `db-sync` | `leios-prototype` branches | No size limit or timeout found |
| `ogmios` | Not started | No size limit or timeout found |
| Kupo | Not started | Not checked |

### Acceptance criteria

For each client:

- [ ] Decodes Dijkstra blocks.
- [ ] Handles maximum-size RB⁺ blocks, tested on a devnet.
- [ ] Handles a one-block rollback for each CertRB at the tip.
- [ ] Doesn't check `block_body_hash` against RB⁺.
