
import Leioscrypto.BLS
import Leioscrypto.Contexts
import Leioscrypto.Registration
import Leioscrypto.Types


namespace Leioscrypto



inductive Vote where
| PersistentVote : ElectionId → BlockHash → PoolIndex → BLS.Signature → Vote
| NonpersistentVote : ElectionId → BlockHash → PoolIndex → BLS.Signature → BLS.Signature → Vote
deriving Repr

namespace Vote

  def electionId : Vote → ElectionId
  | PersistentVote eid _ _ _ => eid
  | NonpersistentVote eid _ _ _ _ => eid

  def ebHash : Vote → BlockHash
  | PersistentVote _ bh _ _ => bh
  | NonpersistentVote _ bh _ _ _ => bh

  def poolIndex : Vote → PoolIndex
  | PersistentVote _ _ pi _ => pi
  | NonpersistentVote _ _ pi _ _ => pi

  def sigma_m : Vote → BLS.Signature
  | PersistentVote _ _ _ sm => sm
  | NonpersistentVote _ _ _ sm _ => sm

  def sigma_eid : Vote → Option BLS.Signature
  | PersistentVote _ _ _ _ => none
  | NonpersistentVote _ _ _ _ se => some se

  def ValidSignatures (regs : Registry) (ctx : EpochContext) (vote : Vote) : Prop :=
    let poolIndex : Nat := vote.poolIndex
    let poolCount : Nat := ctx.pools.length
    let validIndex :  poolIndex < poolCount := sorry
    let poolId : PoolKeyHash := ctx.lookupPoolId poolIndex validIndex
    sorry

end Vote


end Leioscrypto
