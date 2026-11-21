# Forge interface for endorser blocks: three designs

This document compares three states of the forge code:

- **main**: [`128c75a53`](https://github.com/IntersectMBO/ouroboros-consensus/commit/128c75a531a940742eeb8dd490016f44548edc83) (2026-10-06).
- **snapshot**: PR [#2397](https://github.com/IntersectMBO/ouroboros-consensus/pull/2397), branch `dnadales/eb-forge-snapshot`, on top of PR [#2354](https://github.com/IntersectMBO/ouroboros-consensus/pull/2354). `forgeBlock` gets the whole mempool snapshot.
- **interface**: PR [#2377](https://github.com/IntersectMBO/ouroboros-consensus/pull/2377), branch `dnadales/eb-forge-interface`. The forge loop passes the endorser-block (EB) part as a second list.

## 1. The forge loop on main

### Who calls it

[`blockForgingController`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel.hs#L410-L421) and [`forkBlockForging`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel.hs#L531-L554):

```haskell
-- blockForgingController: one thread for each set of forging credentials
blockForging <- atomically getBlockForging         -- [MkBlockForging m blk]
traverse_ cancelThread forgingThreads
blockForging' <- traverse (forkBlockForging st) blockForging

-- forkBlockForging: the thread calls forge at each new slot
forkLinkedWatcherAllocate registry label blockForgingMLabel finalize
  ( \bf -> knownSlotWatcher btime $ \currentSlot ->
      withEarlyExit_ $
        forge (forgeTracer tracers) (forgeStateInfoTracer tracers)
              cfg chainDB mempool bf currentSlot
  )
```

### `forge`

[`forge`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L61-L71):

```haskell
-- Ouroboros.Consensus.NodeKernel.Forge (ouroboros-consensus-diffusion)
forge ::
  forall m blk.
  (IOLike m, RunNode blk) =>                         -- generic: no era code
  Tracer m (TraceLabelCreds (TraceForgeEvent blk)) ->
  Tracer m (TraceLabelCreds (ForgeStateInfo blk)) ->
  TopLevelConfig blk ->
  ChainDB m blk ->
  Mempool m blk ->
  BlockForging m blk ->                              -- era code: forgeBlock
  SlotNo ->
  WithEarlyExit m ()
```

For Cardano, `blk` is `HardForkBlock (CardanoEras c)`.

[`forge`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L61-L147), with only the lines that the designs change.
The `...` lines are the same in all three designs: block context, leader check, ticking and tracing.

```haskell
(fbArgs, txssz, snapSize, forgingOnTopOf) <-
  ChainDB.withReadOnlyForkerAtPoint chainDB (SpecificPoint bcPrevPoint) $ \case
    ...
    Right forker -> do
      ...
      (txs, txssz, snapSize) <-                      -- the loop selects the txs
        getTransactionsToForge cfg mempool currentSlot tickedLedgerState forker
      let fbArgs = Block.ForgeBlockArgs { ..., Block.fbTxs = txs, ... }
      pure (fbArgs, txssz, snapSize, ...)

newBlock <- lift $ Block.forgeBlock blockForging fbArgs        -- returns blk only

trace $ TraceForgedBlock currentSlot forgingOnTopOf newBlock snapSize txssz

addBlockToChainDB trace chainDB mempool currentSlot (fbTxs fbArgs) newBlock
```

### How it selects the transactions

[`getTransactionsToForge`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L460-L493) calls [`snapshotPartition`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/API.hs#L440) on a mempool snapshot for the ticked ledger state:

```haskell
let (txs, txssz, ebTxs, _) =
      snapshotPartition
        mempoolSnapshot
        (blockCapacityTxMeasure (configLedger cfg) tickedLedgerState)  -- capacity of the extended state
        Data.Measure.zero                                              -- EB capacity
unless (null ebTxs) $ throwIO $ userError "... non-empty endorser-block part ..."
```

`txs` is the ranking-block (RB) part: the longest prefix of the mempool that fits the block capacity.
The EB part is always empty.

### What the loop does with the transactions after the forge

[`addBlockToChainDB`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L263-L321):

```haskell
-- In forge: the loop passes the list that it selected.
addBlockToChainDB trace chainDB mempool currentSlot (fbTxs fbArgs) newBlock

addBlockToChainDB trace chainDB mempool currentSlot txs newBlock = do
  ...
  result <- lift $ ChainDB.addBlockAsync chainDB noPunish newBlock
  ...
  when (mbCurTip /= SuccesfullyAddedBlock (blockPoint newBlock)) $ do
    ...
      Just reason -> do                              -- the block is invalid
        whenJust (NE.nonEmpty (map (txId . txForgetValidated) txs))
                 (lift . removeTxsEvenIfValid mempool)
    exitEarly

  trace $ TraceAdoptedBlock currentSlot newBlock txs -- the block is adopted
```

The loop cannot read the transactions out of the block.
[`HasTxs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Ledger/SupportsMempool.hs#L308) is not a constraint of [`RunNode`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Node/Run.hs#L97-L135), and [`DualBlock`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Ledger/Dual.hs#L126) has no instance.

### The facts that the next sections compare

- The loop selects the transactions. The era gets them in [`fbTxs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Block/Forging.hs#L249).
- [`forgeBlock`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Block/Forging.hs#L125) has the type `ForgeBlockArgs blk -> m blk`.
- The loop keeps its list and uses it after the forge.
- The EB capacity is zero, so no EB is possible.

## 2. The forge loop in the snapshot design (#2397)

Links point to [`4146b4938`](https://github.com/IntersectMBO/ouroboros-consensus/commit/4146b4938d18598d1fbef72cc014dd533e81024b).
The type of `forge` does not change.

### `forge`

[`forge`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L59-L149), the same lines as in section 1:

```haskell
(fbArgs, forgingOnTopOf) <-
  ChainDB.withReadOnlyForkerAtPoint chainDB (SpecificPoint bcPrevPoint) $ \case
    ...
    Right forker -> do
      ...
      mempoolSnapshot <-                             -- no selection here
        getMempoolSnapshotToForge mempool currentSlot tickedLedgerState forker
      let fbArgs = Block.ForgeBlockArgs { ..., Block.fbMempoolSnapshot = mempoolSnapshot, ... }
      pure (fbArgs, ...)

Block.ForgedBlock                                    -- the era returns its selection
  { Block.forgedBlock = newBlock, Block.forgedTxs, Block.forgedTxsMeasure }
  <- lift $ Block.forgeBlock blockForging fbArgs

trace $ TraceForgedBlock currentSlot forgingOnTopOf newBlock
          (snapshotMempoolSize (Block.fbMempoolSnapshot fbArgs)) forgedTxsMeasure

addBlockToChainDB trace chainDB mempool currentSlot forgedTxs newBlock
```

### How it selects the transactions

The loop does not select.
[`getMempoolSnapshotToForge`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L458-L479) only takes the snapshot:

```haskell
mempoolSnapshot <- getSnapshotFor mempool currentSlot tickedLedgerState (roforkerReadTables forker)
_ <- evaluate (snapshotMempoolSize mempoolSnapshot)  -- revalidate here, not inside HotKey.sign
pure mempoolSnapshot
```

The era's `forgeBlock` selects.
Two steps pick that `forgeBlock`.

**1. Each era has its own `BlockForging` record.**
For Cardano, [`blockForgingShelleyBased`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus-cardano/src/ouroboros-consensus-cardano/Ouroboros/Consensus/Cardano/Node.hs#L934-L990) builds one record for each Shelley-based era:

```haskell
OptSkip $                                            -- Byron: its record comes separately
  OptNP.fromNonEmptyNP $
    tpraos :* tpraos :* tpraos :* tpraos             -- Shelley to Alonzo
      :* praos :* praos                              -- Babbage, Conway
      :* leios                                       -- Dijkstra
      :* Nil
```

[`hardForkBlockForging`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Forging.hs#L86-L102) combines them into one record with `forgeBlock = hardForkForgeBlock blockForgings`.

**2. The HFC calls the record of the tip era.**
[`hardForkForgeBlock`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Forging.hs#L314-L405):

```haskell
hardForkForgeBlock blockForging ForgeBlockArgs{..} =
  hcollapse
    $ hcizipWith3 proxySingle forgeBlockOne cfgs (OptNP.toNP blockForging)
    $ Match.mustMatchNS "IsLeader" (getOneEraIsLeader fbIsLeader)
    $ State.tip ledgerState                          -- an NS: one value, at the tip era
 where
  TickedHardForkLedgerState transition ledgerState = fbCurrentTickedLedgerState

  forgeBlockOne index cfg' (Comp mBlockForging') (Pair (WrapIsLeader isLeader') (FlipTickedLedgerState ledgerState')) =
    K $ injectForgedBlock index
      <$> forgeBlock (fromMaybe (error ...) mBlockForging')   -- the tip era's record
            ForgeBlockArgs { ..., fbMempoolSnapshot = projectMempoolSnapshot index fbMempoolSnapshot, ... }
```

`hcizipWith3` runs `forgeBlockOne` only at the position of the `NS`.
The dispatch is the same on main.
The snapshot branch changes only what `forgeBlockOne` passes in and gets back.

**The two kinds of era `forgeBlock`.**
The Praos and TPraos eras use `forgeShelleyBlock` ([`praosSharedBlockForging`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Node/Praos.hs#L66-L93), [`forgeShelleyBlock`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Forge.hs#L48-L56)), which calls [`selectBlockTxs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Block/Forging.hs#L317-L328):

```haskell
forgeBlock = forgeShelleyBlock hotKey canBeLeader    -- in praosSharedBlockForging

forgeShelleyBlock hotKey cbl args =
  forgeShelleyBlockWithTxs hotKey cbl args (selectBlockTxs args)

selectBlockTxs ForgeBlockArgs{..} = (txs, txsMeasure)
 where
  (txs, txsMeasure, _, _) =                          -- same call as on main, no throw
    snapshotPartition
      fbMempoolSnapshot
      (blockCapacityTxMeasure (configLedger fbConfig) fbCurrentTickedLedgerState)
      Data.Measure.zero
```

Dijkstra uses [`forgeLeiosBlock`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Node/Leios.hs#L129-L151) ([`leiosSharedBlockForging`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Node/Leios.hs#L96-L125)):

```haskell
forgeBlock = forgeLeiosBlock                         -- in leiosSharedBlockForging

forgeLeiosBlock args@ForgeBlockArgs{..} = do
  forged <- forgeShelleyBlockWithTxs hotKey canBeLeader args (rbTxs, rbTxsMeasure)
  for_ (mkLeiosEb ebTxs) $ \eb ->                    -- Nothing for an empty EB part
    traceWith tracer $ TraceForgedLeiosEb fbCurrentSlotNo eb ebTxsMeasure
  pure forged                                        -- the EB leaves only in the trace
 where
  (rbTxs, rbTxsMeasure, ebTxs, ebTxsMeasure) =       -- one call gives both parts
    snapshotPartition
      fbMempoolSnapshot
      (blockCapacityTxMeasure ledgerConfig fbCurrentTickedLedgerState)
      (ebCapacityTxMeasure ledgerConfig fbCurrentTickedLedgerState)
```

### The interface

[`forgeBlock`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Block/Forging.hs#L133), [`ForgeBlockArgs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Block/Forging.hs#L251-L272) and [`ForgedBlock`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Block/Forging.hs#L279-L302):

```haskell
forgeBlock :: ForgeBlockArgs blk -> m (ForgedBlock blk)

data ForgeBlockArgs blk = ForgeBlockArgs
  { ..., fbMempoolSnapshot :: !(MempoolSnapshot blk), ... }   -- replaces fbTxs

data ForgedBlock blk = ForgedBlock
  { forgedBlock      :: !blk
  , forgedTxs        :: ![Validated (GenTx blk)]              -- for addBlockToChainDB
  , forgedTxsMeasure :: !(MempoolMeasure blk)                 -- for TraceForgedBlock
  }
```

[`addBlockToChainDB`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L265-L318) does not change.
It gets `forgedTxs` in place of `fbTxs fbArgs`.

### Compared with main

|                               | main                                      | snapshot                                    |
|-------------------------------|-------------------------------------------|---------------------------------------------|
| Who selects                   | the loop (`getTransactionsToForge`)       | the era's `forgeBlock` (`selectBlockTxs`, or `forgeLeiosBlock` in Dijkstra) |
| `forgeBlock` gets             | `fbTxs`                                   | `fbMempoolSnapshot`                         |
| `forgeBlock` returns          | `blk`                                     | `ForgedBlock blk`                           |
| List for `addBlockToChainDB`  | `fbTxs fbArgs`                            | `forgedTxs`                                 |
| EB part                       | empty, the loop throws if not             | Dijkstra builds an EB and traces it. Other eras drop it. |

## 3. The forge loop in the interface design (#2377)

Links point to [`d4da9acab`](https://github.com/IntersectMBO/ouroboros-consensus/commit/d4da9acab15ceec59a06e216627e1808b452b393), the head of #2377.
#2377 is on main, not on #2354.
So it has no Dijkstra forge on Leios.
Blocks marked **sketch** are not in #2377.
They show the code that gives the same behaviour as the snapshot branch, on top of #2354.

### `forge`

[`forge`](https://github.com/IntersectMBO/ouroboros-consensus/blob/d4da9acab15ceec59a06e216627e1808b452b393/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L62-L157), the same lines as in section 1:

```haskell
forge ... blockForging onForgedLeiosEb currentSlot = do   -- new argument
  ...
  (fbArgs, txssz, snapSize, forgingOnTopOf) <-
    ChainDB.withReadOnlyForkerAtPoint chainDB (SpecificPoint bcPrevPoint) $ \case
      ...
      Right forker -> do
        ...
        (txs, txssz, ebTxs, snapSize) <-                 -- the loop selects both parts
          getTransactionsToForge cfg mempool currentSlot tickedLedgerState forker
        let fbArgs = Block.ForgeBlockArgs { ..., Block.fbTxs = txs, Block.fbEbTxs = ebTxs, ... }
        pure (fbArgs, txssz, snapSize, ...)

  (newBlock, mForgedEb) <- lift $ Block.forgeBlock blockForging fbArgs

  trace $ TraceForgedBlock currentSlot forgingOnTopOf newBlock snapSize txssz

  addBlockToChainDB trace chainDB mempool currentSlot (fbTxs fbArgs) newBlock  -- exits if not adopted

  lift $ whenJust mForgedEb (onForgedLeiosEb (getHeader newBlock))
```

[`forkBlockForging`](https://github.com/IntersectMBO/ouroboros-consensus/blob/d4da9acab15ceec59a06e216627e1808b452b393/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel.hs#L531-L555) passes `(\_ _ -> pure ())` as `onForgedLeiosEb`.

### How it selects the transactions

[`getTransactionsToForge`](https://github.com/IntersectMBO/ouroboros-consensus/blob/d4da9acab15ceec59a06e216627e1808b452b393/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L471-L510) returns the EB part too.
In #2377, the EB capacity is still zero, so `ebTxs` is always empty.

**Sketch:** pass the EB capacity and drop the throw.

```haskell
let (txs, txssz, ebTxs, _) =
      snapshotPartition
        mempoolSnapshot
        (blockCapacityTxMeasure (configLedger cfg) tickedLedgerState)
        (ebCapacityTxMeasure (configLedger cfg) tickedLedgerState)  -- was Data.Measure.zero
```

The HFC instance of [`ebCapacityTxMeasure`](https://github.com/IntersectMBO/ouroboros-consensus/blob/128c75a531a940742eeb8dd490016f44548edc83/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Mempool.hs#L437-L461) is on main already.
It takes the tip era's capacity and injects it.
Before Dijkstra, that capacity is zero, so `ebTxs` stays empty.

The snapshot branch partitions in the same way: combined measures and an injected capacity (`projectMempoolSnapshot`).
So both designs select the same two parts.

### How the HFC passes the parts to the era

[`hardForkForgeBlock`](https://github.com/IntersectMBO/ouroboros-consensus/blob/d4da9acab15ceec59a06e216627e1808b452b393/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Forging.hs#L309-L445):

```haskell
hardForkForgeBlock blockForging ForgeBlockArgs{..} =
  fmap hcollapse
    $ hsequence'
    $ hizipWith3 forgeBlockOne cfgs (OptNP.toNP blockForging)
    $ Match.mustMatchNS "IsLeader" (getOneEraIsLeader fbIsLeader)
    $ State.tip
    $ injectValidatedTxs fbEbTxs                     -- main's rematchValidatedTxs,
    $ injectValidatedTxs fbTxs ledgerState           -- called once for each list
 where
  forgeBlockOne index cfg' (Comp mBlockForging') (Pair (WrapIsLeader isLeader') (Pair (Pair (FlipTickedLedgerState ledgerState') (Comp txs')) (Comp ebTxs'))) =
    Comp $ K . first (HardForkBlock . OneEraBlock . injectNS index . I)
      <$> forgeBlock (fromMaybe (error ...) mBlockForging')
            ForgeBlockArgs { ..., fbTxs = map unwrapValidatedGenTx txs', fbEbTxs = map unwrapValidatedGenTx ebTxs', ... }
```

The dispatch is the same as on main and on the snapshot branch: the era of `State.tip`.
The HFC converts two lists of transactions and no measures.
So `CanHardFork` needs no new methods.

### The two kinds of era `forgeBlock`

Every era except Dijkstra ignores `fbEbTxs` and returns `Nothing` ([`praosSharedBlockForging`](https://github.com/IntersectMBO/ouroboros-consensus/blob/d4da9acab15ceec59a06e216627e1808b452b393/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Node/Praos.hs#L64-L90)):

```haskell
forgeBlock = fmap (\blk -> (blk, Nothing)) . forgeShelleyBlock hotKey canBeLeader
```

`forgeShelleyBlock` keeps its type and uses `fbTxs`, as on main.

**Sketch:** Dijkstra, in #2354's `leiosSharedBlockForging`.
`mkLeiosEb` is the function that the snapshot branch adds.

```haskell
forgeBlock = \args@ForgeBlockArgs{fbEbTxs} -> do
  blk <- forgeShelleyBlock hotKey canBeLeader args   -- uses fbTxs
  pure (blk, ForgedLeiosEb <$> mkLeiosEb fbEbTxs)    -- Nothing for an empty EB part
```

### The interface

[`forgeBlock`](https://github.com/IntersectMBO/ouroboros-consensus/blob/d4da9acab15ceec59a06e216627e1808b452b393/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Block/Forging.hs#L126), [`ForgeBlockArgs`](https://github.com/IntersectMBO/ouroboros-consensus/blob/d4da9acab15ceec59a06e216627e1808b452b393/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Block/Forging.hs#L240-L279) and [`ForgedLeiosEb`](https://github.com/IntersectMBO/ouroboros-consensus/blob/d4da9acab15ceec59a06e216627e1808b452b393/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Leios/Types.hs#L223-L226):

```haskell
forgeBlock :: ForgeBlockArgs blk -> m (blk, Maybe ForgedLeiosEb)

data ForgeBlockArgs blk = ForgeBlockArgs
  { ..., fbTxs :: ![Validated (GenTx blk)]             -- the RB part, as on main
  , fbEbTxs :: ![Validated (GenTx blk)], ... }         -- the EB part

data ForgedLeiosEb = ForgedLeiosEb { forgedLeiosEbBody :: !LeiosEb }
```

`ForgedLeiosEb` has no `blk` parameter, so it is one type for every block type.

### After the forge

[`addBlockToChainDB`](https://github.com/IntersectMBO/ouroboros-consensus/blob/d4da9acab15ceec59a06e216627e1808b452b393/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L273-L331) does not change. It gets `fbTxs fbArgs`, as on main.
If the ChainDB adopts the block, `forge` calls `onForgedLeiosEb` with the forged EB.

**Sketch:** trace the EB in the node kernel's callback, in place of `(\_ _ -> pure ())`.

```haskell
(\hdr eb -> traceWith leiosForgeTracer (TraceForgedLeiosEb (blockSlot hdr) eb))
```

This trace comes after adoption.
On the snapshot branch, `forgeLeiosBlock` traces before `addBlockToChainDB`.

### Compared with main and the snapshot branch

|                               | main                                | snapshot                                                   | interface (#2377 + sketches)                    |
|-------------------------------|-------------------------------------|------------------------------------------------------------|-------------------------------------------------|
| Who selects                   | the loop (`getTransactionsToForge`) | the era's `forgeBlock` (`selectBlockTxs`, `forgeLeiosBlock`) | the loop (`getTransactionsToForge`)             |
| `forgeBlock` gets             | `fbTxs`                             | `fbMempoolSnapshot`                                        | `fbTxs` and `fbEbTxs`                           |
| `forgeBlock` returns          | `blk`                               | `ForgedBlock blk`                                          | `(blk, Maybe ForgedLeiosEb)`                    |
| List for `addBlockToChainDB`  | `fbTxs fbArgs`                      | `forgedTxs`                                                | `fbTxs fbArgs`                                  |
| HFC converts                  | one list                            | the snapshot, with measures (`projectMempoolSnapshot`)     | two lists                                       |
| New `CanHardFork` methods     | none                                | `hardForkProj*` (three)                                    | none                                            |
| `forgeShelleyBlock` type      | unchanged                           | returns `ForgedBlock`                                      | unchanged                                       |
| EB leaves the era through     | no EB                               | a tracer argument of `leiosSharedBlockForging`             | the result of `forgeBlock`                      |
| EB trace                      | none                                | before `addBlockToChainDB`                                 | after adoption, in `onForgedLeiosEb`            |

## 4. Pros and cons

The interface design fits better, mainly because of the certify step.

### Snapshot

Pros:

- The era owns the RB/EB split. The loop knows nothing about EBs.
- It follows the "How" section of [#1107](https://github.com/input-output-hk/ouroboros-leios/issues/1107): "`forgeBlock` gets the whole `MempoolSnapshot`".
- `forgedTxs` is what the era selected, so `addBlockToChainDB` traces and removes the era's own list.

Cons:

- The API breaks more: every era's `forgeBlock`, plus `forgeShelleyBlock`, `forgeByronBlock`, `forgeSimple` and the db-synthesizer.
- The HFC needs `projectMempoolSnapshot` and three [`CanHardFork`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Abstract/CanHardFork.hs#L135-L151) methods. They have no default. A missing instance gives a `-Wmissing-methods` warning and fails at run time.
- Measures go through a projection and back through an injection. Before Dijkstra, [`hardForkProjTxEbMeasure`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus-cardano/src/ouroboros-consensus-cardano/Ouroboros/Consensus/Cardano/CanHardFork.hs#L308-L325) drops `txReferencesSize`, so `TraceForgedBlock` shows zero for it.
- It fits the certify step badly. A certifying RB carries no transactions ([CIP-0164 Step 5](https://github.com/cardano-foundation/CIPs/blob/a2cac18039d7bab6c0dc1a806ad8a96b8b0546fc/CIP-0164/README.md?plain=1#L398-L430)). Its EB part needs a second snapshot, against the ledger state after the certified EB. One `fbMempoolSnapshot` cannot give that.
- The EB leaves the era only through a tracer argument of [`leiosSharedBlockForging`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4146b4938d18598d1fbef72cc014dd533e81024b/ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Node/Leios.hs#L96-L125). The trace comes before adoption.

### Interface

Pros:

- The diff is smaller. `forgeShelleyBlock` and `addBlockToChainDB` keep their types.
- The HFC converts two lists and no measures. `CanHardFork` needs no new methods.
- It fits the certify step. The prototype's [`forge`](https://github.com/IntersectMBO/ouroboros-consensus/blob/4181c130e350d19cfdf4d3d7f0422750a8455f27/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel/Forge.hs#L729-L798) decides to certify, takes a second snapshot, and passes an empty RB part and the new EB part.
- The EB is a return value. The callback after adoption is where storing the EB can start.

Cons:

- The loop must get the EB capacity, through `ebCapacityTxMeasure`.
- `Block.Forging` depends on a Leios type, `ForgedLeiosEb`, for every block type.
- `forge` gets a callback parameter.
- It differs from the text of #1107. The [question](https://github.com/input-output-hk/ouroboros-leios/issues/1107#issuecomment-6043579926) to nfrisby and ch1bo has no answer yet.
