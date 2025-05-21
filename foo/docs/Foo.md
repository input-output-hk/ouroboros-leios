Nicolas Frisby <nick.frisby@iohk.io> <nicolas.frisby@moduscreate.com>

## Introduction

The executable sketch in the accompanying `Foo.hs` file proposes rules for the following.

- How input blocks (IBs) should be generated from submitted transactions (txs).
- How IBs should be interpreted by the ledger when referenced by ranking blocks (RBs).

This proposal does not involve labeled UTxO (eg sharding).
It instead explores accepting that concurrent IBs may involve duplicate and/or conflicting txs, especially if the adversary is desires.

In terms of the current draft of <https://docs.google.com/document/d/1Qau3KPBuTJMDK8Il1mk_CCJAKY8q6wO9-H9aMuyn4xs/edit?tab=t.0#heading=h.tico77dbdt7s>, this proposal embraces the _speculative ledger state_ in order to remain similar to the existing Praos node, which seems promising for an non-disruptive initial Leios implementation even if it's not optimal.

Compared to the Praos node, this proposal leverages Leios's IBs to smooth the utilization of bandwidth between RBs, but it does not itself also smooth the utilization of CPU between RBs.
For example, RBs will effectively become very big Praos blocks, and so some nodes may simply be proportionally slower to select them.
Today's Praos block capacity is primarily bound by bandwidth concerns, so smoothing bandwidth utilization without smoothing CPU utilization might suffice to meaningfully increase throughput capacity.

## Derivation

This propsal began by supposing the Leios TxMempool behaves as similarly as possible to the Mempool in today's Praos node, and then patching incompatibilitiese as they became apparent.

- Just like the Praos Mempool, the Leios TxMempool simply contains all received txs in their arrival order that have always been cumuatlively fully valid starting from the currently selected RB.
  In particular, txs are only evicted when they're no longer valid in that way.
  The key difference between the Praos Mempool and the Leios TxMempool is that the TxMempool will push its txs into new IBs in contrast to the Praos Mempool pushing its txs into new RBs.

- If new IBs were to simply take the oldest prefix of the TxMempool that fits, then every IB created between two RBs would contain the oldest txs.
  That is a prohibitive degree of duplication.
  Therefore, the logic for filling a new IB will depend on received IBs that might still influence the next RB.
  This motivates a new component, called the IbMempool.

- The IbMempool contains IBs that have not yet expired (with respect to the currently selected RB) and so might occur in an extension of the currently selected RB (whether the node mints that next RB or receives it).
  Expired IBs might still be necessary---eg if the node were to switch chains---but they can never be included by an extension of the currently selected RB.

- A new IB contains the biggest-possible prefix of the subsequence of the TxMempool that would remain valid if the next RB contained every IB in the IbMempool.
  The IbMempool must be ordered for it to determine a ledger state that can be used to identify that subsequence of the TxMempool.
  That ledger state can then be constructed in the exact same way that a ledger state is constructed from the IB sequenced determined by a new RB (rules which will be detailed below).

    - Given how the IbMempool excludes txs from new IBs, it should be in ascending order of slot.

    - Given how the IbMempool is an optimistic approximation of future RBs, tiebreakers for IBs with equal slots would ideally be objective and equivalent in the IbMempool and in RBs (eg similar to today's Praos block tiebreaker).
  
- Concurrent IBs (ie a pair of IBs that were both minted by a node before receiving the other IB) will still contain duplicates of some txs.
  This shortcoming of parallel IB generation cannot be eliminated but can be mitigated, by trading some latency.
  For that purpose, every tx will be assigned a lane ("tx lane" is just a different name for the "tx color" proposed in <https://iohk.io/en/research/library/papers/ouroboros-leios-design-goals-and-concepts/>).
  It must be possible to explicitly assign a lane, so that dependent txs can be assigned the same lane.
  Even txs without an explicit lane will have an implicit lane (eg derived from their `TxId`).
  A new IB will be restricted to those txs in the TxMempool in a set of lanes.
  That set of lanes is extended one random sample at a time until either the IB is full or contains the entire TxMempool.

    - A tx's lane (eg `Maybe Word8`) should be a signed field of the tx and so influence its `TxId`.

    - The number of lanes will need to be tuned in balance with the prevalence of concurrent IBs: higher IB rates means more lanes.

    - If one tx depends on another, they should be in the same lane.
      This increases the chance that the second tx can be included ASAP once the first tx is included (perhaps even in the same IB).

    - Even if each user only ever assigned one random lane to all their txs, their cumulative traffic would be balanced among all the lanes.
      This means wallets could assign the asme lane to all submitted txs and randomly change that lane if the user hasn't submitted a tx in a while.
      Thus most users don't need to be aware of lanes.

    - A user restricting themselves to a single lane will not necessarily see improved latency for their txs.
      But they would see improved throughput, since most IBs between RBs will not be concurrent.

    - A throughput-hungry user like dApp, on the other hand, would want to distribute a large burst of work across as many lanes as possible in order leverage Leios's parallelism.

    - The new IB logic adapts: if traffic is low and/or confined to a few lanes, a new IB will only consider lanes that have txs in them.
      This means that lanes only mitigate duplication if the TxMempools have more txs than one IB and those txs are in different lanes.
      Low tx traffic and/or traffic confined to a single lane will increase duplication.

    - If duplication is still too high--eg due to low and/or few-laned traffic---then perhaps the new IB logic could bound how many lanes it samples, ie accept that idle lanes waste throughput.

- The use of lanes to reduce duplication does not prevent an attacker from submitting conflicting txs.
  Suppose the attacker submits several txs that all spend the exact same UTxO.
  If some of those txs end up in concurrent IBs, then only one of them could possibly be valid.
  Thus the attacker has consumed more IB capacity (ie throughput capacity) than they've paid for.

    - This attack is overt.

    - Note that a single TxMempool would never contain any conflicting txs, so this attack would require the adversary to submit different txs to different SPOs.

    - If the adversary can somehow reliably predict which of its txs will be the valid one in the eventual RB, then they can make the attack much worse.
      They'd submit additional large txs that depend on one of the txs that will end up in an concurrent IB but be phase-1 invalid.
      Thus some of those large txs would also occupy IB capacity without being paid for, since they're phase-1 invalid.
      This exacerbation can be prevented by adding ledger rules that confiscate (eg as "bonus" fees) all inputs of txs that depend on txs that conflicted with other txs.
      Honest users do not risk confiscation unless they sign txs that consume UTxO that might occur in conflicting txs---be careful who you do business with.

    - That confiscation logic can be slightly embellished to also reap all otherwise-unconsumed inputs if the latter conflicting txs spend additional inputs.

    - The ledger rules must not confiscate inputs that the conflicting tx wasn't authorized to spend.
      In particular, scripts would have to be evaluated.
      (This risk arises only because adversarial IBs might contain txs that were never phase-2 valid.)

    - Confiscation prevent the exacerbated attack but not the base attack.
      Note that the expected efficiency of the base attack is proportional to the expected number of concurrent IBs.
      An attacker efficiently wasting IB capacity in this way would either need to be accepted as an unmitigated vector or else mitigated in some other way (eg inflating fees, tuning concurrency down).
