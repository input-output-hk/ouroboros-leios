# The Praos node as the trace verifier's `BaseMachine`

Design notes for `src/Leios/Base/Praos*` — the wrapper that turns the honest
node of `ouroboros-praos-formal-spec` (pinned at `847697e` via the root
flake's `praos-spec-src` input; library built by `nix/agda.nix`'s `praosSpec`
derivation) into the `BaseMachine` that `Defaults.agda` installs in the
verifier's `SpecStructure`. This began as a sketch inside the
`ouroboros-leios-formal-spec` checkout and was moved here (2026-08-13)
because it's a pure *consumer* of `leios-spec`'s `Leios.Base.BaseMachine`
interface, like the verifier itself; the sketch's code blocks have since
become the real modules and are not duplicated here.

## Module map

- `Praos.agda` (`--safe`) — the machine: a `PraosAbstract` interface record
  (block-tree state + delivery/minting/read functions) and the step relation,
  `IsConstrained`/`IsPure` proofs, and `BaseMachine` assembly. The step-index
  proofs need `opaque unfolding _⊗₀_`, as in `Leios.Linear.Trace.Verifier`.
- `Instance.agda` — `PraosAbstract` instantiated with the actual Praos spec:
  `Params` with `Txs := RankingBlock`, honest-node functions from
  `Protocol.Semantics`. Not `--safe` (Praos's `chainFromBlock` is
  `TERMINATING`).
- `Assumptions.agda` — a concrete `Assumptions` instance: `TreeImpl := List
  Block`, `bestChain` = the longest chain `chainFromBlock` reconstructs from
  the slot-bounded pool, all parties honest. The five `Protocol.Tree` laws
  (`instantiated`/`extendable`/`valid`/`optimal`/`selfContained`) and
  `genesisWinner` are **postulated** — open problems even upstream:
  `ouroboros-praos-formal-spec`'s own `Examples.Praos` leaves the same five
  as `{!!}` holes under `--allow-unsolved-metas`, and its `extendTree` there
  looks like it actually *violates* `extendable` for blocks that fork below
  the current chain tips. Same honesty tradeoff as the verifier's
  `leadershipSchedule` postulate. Node identity is fixed at `party₀`
  (index 0), made harmless by the `winner` choice below.
- `Machine.agda` — assembles `praosNode` to `Assembled.praosBase :
  BaseMachine`; exports `B'` for the `SpecStructure`.
- `Defaults.agda` — `d-Base = PB.B'`, `d-BaseFunctionality = PB.praosBase`,
  with the stub's trivial `Cert`/`VTy`/`initSlot`/`V-chkCerts` kept (so the
  verifier-facing `BaseIOF` interface is unchanged) and `winner := λ _ sl →
  (EB , sl) ∈ winning-slots`, the same leadership-schedule oracle `sortition`
  consults. The party argument is ignored: the schedule is the SUT's own and
  `makeBlockʰ` only evaluates `winner` at the machine's own identity — which
  also neutralizes the `party₀`-vs-`sutId` mismatch. This cost `Defaults.agda`
  its `--safe` flag.

The modules aren't reachable from `src/trace-parser.agda`'s `--safe`-only
prefix on their own; the Makefile's `praos-base` / `praos-instance` /
`praos-assumptions` / `praos-machine` targets check them individually.

## The shape of the wrapper

The honest Praos node, extracted from the global small-step semantics, does
exactly three things per round: absorb delivered blocks (`processMsgsʰ`),
mint if it won the slot (`makeBlockʰ`), observe the clock tick. The wrapper
re-packages those — all *local*, pure functions of `LocalState` — as a
`Machine BaseNetwork (BaseIO ⊗₀ BaseAdv)` answering Leios's
`INIT/SUBMIT/FTCH-LDG/FTCH-SLOT` protocol. The global-state machinery
(`execOrder`, `Progress`, `permuteParties`) stays outside; it belongs to the
deployment/simulation proof, not the node.

One timing fact from `NetTranslate` (`Network/Leios.agda`) pins down the
driving protocol: each DD round, the base machine first receives the round's
delivery batch and must *synchronously* answer with the messages it wants
diffused (`SendB` waits for base output before activating Leios). So
delivery + minting + clock tick collapse into **one machine step**
(`Deliver`), and a `SUBMIT` from Leios in round *t* can only be minted from
round *t+1* on — a semantic wrinkle to remember in the simulation proof.

`IsConstrained`/`IsPure` hold *by construction* (the wrapper is a fresh
inductive relation; only `FtchLdg`/`FtchSlot` answer the queries, both
leaving state unchanged). Praos's `Computational` proofs become relevant only
for the future simulation lemma relating `Deliver` steps to the honest
constructors `honestParty↓`/`honestParty↑` — that's where the real proof
budget lies, not in the machine.

## `producer`/`slotOf`

`IsBlockchain` demands `producer : RankingBlock → Participant` and `slotOf :
RankingBlock → ℕ`, but `BASE-LDG` returns bare payloads. Resolution as wired:

- `slotOf := RankingBlock.slot` — the pinned `leios-spec` still has the
  pre-CIP-33 `RankingBlock` shape with a `slot` field. (The spec's `main`
  branch dropped it; if the pin ever moves, the original fix applies: enrich
  `RankingBlock` with the Praos envelope fields, coherence enforced in the
  wrapper's `Deliver`/mint step — an RB *is* a Praos block.)
- `producer` genuinely can't be recovered from a bare payload (two payloads
  by different producers are equal as `RankingBlock`s), so it stays a
  parameter, filled with a placeholder. That's sound for the verifier:
  `producer`/`slotOf` (and `BM`/`BaseNetwork`, hence `BaseMsg`) are consumed
  only by `Network.Leios` and `Blockchain.Liveness.Transfer` —
  deployment-level theorem transport outside `src/trace-parser.agda`'s import
  graph — so they are exercised by nothing at runtime. For the same reason
  the postulates in `Assumptions.agda` are never forced.

## What stays outside the wrapper (deliberately)

- **Stake**: `stake₀` is a parameter — Praos has no stake distribution, and
  nothing in CP/CG/CQ constrains it. It only feeds Leios's voting committee.
- **Cert checking**: `checkCert` is stored but unused — Praos's `_✓` ignores
  payloads. Enforcing it at minting is easy in the wrapper; making *chain
  validity* respect it is an upstream `_✓`-hook change.
- **`txSelection` reconciliation**: the wrapper mints from `pending`, which
  is precisely the state-dependent `txSelection` the upstream Praos repo
  doesn't have. The simulation proof will need Praos's `txSelection : Slot →
  Party → Txs` generalized to consume the submit buffer — the one upstream PR
  the wrapper can't avoid.
- **Adversary & scheduling**: `ForgingFree`/`CollisionFree`,
  `permuteParties`, corrupt parties — all deployment-level; they reappear
  only in the theorem transport discharging `Deployment.safety`/`hcg`/`∃cq`
  from Praos's CP/CG/CQ. (For that work, re-include the `Properties` modules
  the `praosSpec` nix derivation currently prunes, alongside `Everything`
  (name clash with iog-prelude), `Examples` (holes) and
  `Protocol.TraceVerifier` (needs agda-irrelevance).)
