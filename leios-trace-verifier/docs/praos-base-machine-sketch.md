# The Praos node as the trace verifier's `BaseMachine`

Design notes for `src/Leios/Base/Praos*`, the wrapper that turns the honest
node of `ouroboros-praos-formal-spec` (pinned at `847697e` via the root
flake's `praos-spec-src` input; library built by `nix/agda.nix`'s `praosSpec`
derivation) into the `BaseMachine` that `Defaults.agda` installs in the
verifier's `SpecStructure`.  This began as a sketch inside the
`ouroboros-leios-formal-spec` checkout and was moved here (2026-08-13)
because it is a pure *consumer* of `leios-spec`'s `Leios.Base.BaseMachine`
interface, like the verifier itself.  The sketch's code blocks have since
become the real modules and are not duplicated here.

## Module map

- `Praos.agda` (`--safe`): the machine.  It holds a `PraosAbstract`
  interface record (block-tree state plus delivery, minting and read
  functions), the step relation, the `IsConstrained`/`IsPure` proofs and the
  `BaseMachine` assembly (`Node.Assemble`).  The step-index proofs need
  `opaque unfolding _⊗₀_`, as in `Leios.Linear.Trace.Verifier`.
- `Instance.agda`: `PraosAbstract` instantiated with the actual Praos spec,
  i.e. `Params` with `Txs := RankingBlock` and the honest-node functions
  from `Protocol.Semantics`.  Not `--safe`, since Praos's `chainFromBlock`
  is `TERMINATING`.
- `BlockTree.agda`: the block tree, with incremental chain selection for
  chains of node-log size, and proofs of the five `Protocol.Tree` laws
  (`instantiated`/`extendable`/`valid`/`optimal`/`selfContained`).  The
  design is as follows:
    * genesis is part of every tree's pool, so a valid best chain always
      exists inside it;
    * every block of the pool has an entry holding the longest valid chain
      of the pool that ends in it, if there is one;
    * a block whose slot is no lower than that of any earlier block (`top`)
      extends the longest chain of a parent, and no earlier entry changes,
      since the slots of a valid chain fall strictly towards genesis;
    * the tree also keeps the longest chain of all, which answers every
      query at or past `top` at once;
    * a block arriving out of order makes the tree rebuild its entries from
      the pool in slot order (rare, since the converters deliver blocks in
      order);
    * the entries' chains share their tails, so an entry costs one cell.

  The invariant `Inv` travels with the tree, and the laws follow from it.
- `ListLemmas.agda` (`--safe`): the generic list machinery behind
  `BlockTree`, measure-generic.  `MaxBy` is the fold picking the longest
  candidate (it returns the base or a member, and no member is longer);
  `SortDesc` is the descending sort by slot (it keeps exactly the pool's
  members and returns them sorted, the order in which the tree rebuilds).
- `Assumptions.agda`: a concrete `Assumptions` instance, with the tree of
  `BlockTree.agda` as `TreeImpl`, all parties honest, and `party₀` (index
  0) as genesis producer and sole member of `parties₀`.  It contains no
  postulates.  Its module parameters are the following:
    * `winner₀ : ∀ p → winner p 0`, which discharges `genesisWinner`; only
      the caller, who supplies `winner`, can witness it;
    * `blockHash`, the block hash used for prev-linkage (no law depends on
      it);
    * `self`, the party the node mints as.

  It also exports the verifier-facing helpers `mkPraosBlock`,
  `praosBlockHash`, `genesisHash` and `praosHeader` (a block's parent and
  slot, which is what a log records of a block the node mints).
- `Machine.agda`: assembles `praosNode` into `Assembled.praosBase :
  BaseMachine`; exports `B'` for the `SpecStructure`, and `node⁻` (the node
  without its empty adversary port), `NodeState`, `initNodeState` and the
  trace checker `Check` for stacking Leios on it.
- `Defaults.agda` (outside the `Praos` directory) wires it up:
    * `d-Base = PB.B'` and `d-BaseFunctionality = PB.praosBase`, with the
      stub's trivial `Cert`/`VTy`/`initSlot`/`V-chkCerts` kept, so the
      verifier-facing `BaseIOF` interface is unchanged;
    * `d-winner _ 0 = ⊤` and `d-winner p (suc sl) = p ≡ sutId → suc sl ∈
      rb-slots`: slot 0 is a universal winner, which discharges `winner₀`
      (only genesis sits at slot 0, and the machine never mints there,
      since `Deliver` mints at `suc clock`); in later slots the SUT wins
      exactly its leadership-schedule slots, and every other party wins
      every slot, so delivered blocks of other parties are never rejected
      for leadership;
    * `self = sutId`;
    * `d-blockHash sl pid _ = [ sl , toℕ pid ]`: slot and producer, which
      identify honest blocks.  The payload is left out on purpose: the node
      mints the SUT's blocks with the payload Leios submitted, which the log
      does not record, while other parties' blocks name them as parents by
      their log id.  Two blocks of one producer in one slot (equivocation)
      are not told apart;
    * `tipHash`, the hash of a selected chain's tip, for logs that name it.

  This cost `Defaults.agda` its `--safe` flag (Praos's `TERMINATING
  chainFromBlock`; no postulates are involved).

`src/trace-parser.agda` reaches all of these through the verifiers and
`Defaults.agda`.  The Makefile's `praos-base` / `praos-instance` /
`praos-assumptions` / `praos-machine` targets still check them one at a
time.

## The verifiers stack Leios on the node

Both verifiers run `LinearLeiosStack`, Linear Leios composed with `node⁻`
along `BaseIO`, with a checker composed from the Leios checker, the node's
`Check` and `idᶜ` for the wires.  The node, not the trace, answers Leios's
ledger requests and takes the blocks Leios submits; the trace only feeds the
node the blocks the SUT receives, and the trace's record of the blocks the
SUT mints is checked against what the node mints.  The node's clock trails
the Leios slot by one, so there is no round for slot 0.

- `LinearLeiosVerifier` (conformance traces): `RBGenerated` records per-RB
  header data in `RB-meta` (prev-hash from the event's `parent` ref, the
  genesis hash when null; slot; producer).  Blocks are built on demand
  (`buildBlk`), because the RB payload in `RB-refs` may still be corrected
  by a later `EBGenerated`.  Received blocks collect in `inbox` until the
  slot's `deliver` step.  The checker observes minted blocks through
  `praosHeader`; the trace records no selected chain, so that is not
  checked.
- `LinearLeiosVerifierChain` (node.log): blocks the node adopted before the
  SUT forged in a slot go into that slot's round (`inbox`), later ones wait
  for the next (`late`).  The log names no producers, so the other blocks of
  a slot are numbered, skipping the SUT, which keeps them apart in the
  tree.  Each round must mint the block the SUT forged, on the tip the SUT
  had then, and select the chain the SUT selected, observed through
  `praosHeader` and `tipHash`.

## The shape of the wrapper

The honest Praos node, extracted from the global small-step semantics, does
exactly three things per round: absorb delivered blocks (`processMsgsʰ`),
mint if it won the slot (`makeBlockʰ`), and observe the clock tick.  The
wrapper re-packages those, all *local* and pure functions of `LocalState`,
as a `Machine BaseNetwork (BaseIO ⊗₀ BaseAdv)` answering Leios's
`INIT/SUBMIT/FTCH-LDG/FTCH-SLOT` protocol.  The global-state machinery
(`execOrder`, `Progress`, `permuteParties`) stays outside; it belongs to the
deployment/simulation proof, not the node.

One timing fact from `NetTranslate` (`Network/Leios.agda`) pins down the
driving protocol: each DD round, the base machine first receives the round's
delivery batch and must *synchronously* answer with the messages it wants
diffused (`SendB` waits for base output before activating Leios).  So
delivery, minting and the clock tick collapse into **one machine step**
(`Deliver`), and a `SUBMIT` from Leios in round *t* can only be minted from
round *t+1* on, a semantic wrinkle to remember in the simulation proof.

`IsConstrained`/`IsPure` hold *by construction*: the wrapper is a fresh
inductive relation, and only `FtchLdg`/`FtchSlot` answer the queries, both
leaving the state unchanged.  Praos's `Computational` proofs become relevant
only for the future simulation lemma relating `Deliver` steps to the honest
constructors `honestParty↓`/`honestParty↑`; that is where the real proof
budget lies, not in the machine.

## `producer`/`slotOf`

`IsBlockchain` demands `producer : RankingBlock → Participant` and `slotOf :
RankingBlock → ℕ`, but `BASE-LDG` returns bare payloads, and the pinned
`leios-spec`'s `RankingBlock` (`announcedEB`, `txsOrEbCert`) carries neither
a producer nor a slot.  The Praos block around it has both, but the payload
projection loses them.  Both therefore stay parameters of
`Machine.Assembled`, and `Defaults.agda` fills them with placeholders
(`λ _ → sutId`, `λ _ → 0`).

That is sound for the verifier: `producer`/`slotOf` (and `BM`/`BaseNetwork`,
hence `BaseMsg`) are consumed only by `Network.Leios` and
`Blockchain.Liveness.Transfer`, deployment-level theorem transport outside
`src/trace-parser.agda`'s import graph, so nothing exercises them at
runtime.  The proper fix, should the deployment-level work need it, is to
enrich `RankingBlock` with the Praos envelope fields and enforce coherence
in the wrapper's `Deliver`/mint step, since an RB *is* a Praos block.

## What stays outside the wrapper (deliberately)

- **Stake**: `stake₀` is a parameter, which the node returns on Leios's
  `INIT`.  It is Praos's stake distribution, which is used for RB and EB
  selection.
- **Cert checking**: `checkCert` is stored but unused, since Praos's `_✓`
  ignores payloads.  Enforcing it at minting is easy in the wrapper; making
  *chain validity* respect it is an upstream `_✓`-hook change.
- **`txSelection` reconciliation**: the wrapper mints from `pending`, which
  is precisely the state-dependent `txSelection` the upstream Praos repo
  does not have (`Assumptions.agda` sets `txSelection` to a constant).  The
  simulation proof will need Praos's `txSelection : Slot → Party → Txs`
  generalized to consume the submit buffer, the one upstream PR the wrapper
  cannot avoid.
- **Adversary and scheduling**: `ForgingFree`/`CollisionFree`,
  `permuteParties` and corrupt parties are all deployment-level.  They
  reappear only in the theorem transport discharging
  `Deployment.safety`/`hcg`/`∃cq` from Praos's CP/CG/CQ.  For that work,
  re-include the `Properties` modules the `praosSpec` nix derivation
  currently prunes, alongside `Everything` (name clash with iog-prelude),
  `Examples` (holes) and `Protocol.TraceVerifier` (needs agda-irrelevance).
