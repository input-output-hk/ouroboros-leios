
import Leioscrypto.BLS
import Leioscrypto.Contexts
import Leioscrypto.Registration
import Leioscrypto.Types


namespace Leioscrypto


inductive Vote where
| PersistentVote : ElectionId → PoolIndex → BlockHash → BLS.Signature → Vote
| NonpersistentVote : ElectionId → PoolKeyHash → BLS.Signature → BlockHash → BLS.Signature → Vote

namespace Vote

  def electionId : Vote → ElectionId
  | PersistentVote eid _ _ _ => eid
  | NonpersistentVote eid _ _ _ _ => eid

  def ebHash : Vote → BlockHash
  | PersistentVote _ _ bh _ => bh
  | NonpersistentVote _ _ _ bh _ => bh

  def σ_eid : Vote → Option BLS.Signature
  | PersistentVote _ _ _ _ => none
  | NonpersistentVote _ _ sig _ _ => some sig

  def σ_m : Vote → BLS.Signature
  | PersistentVote _ _ _ sig => sig
  | NonpersistentVote _ _ _ _ sig => sig

  structure WellFormed (vote : Vote) : Prop where
    wf_σ_eid : vote.σ_eid.elim True BLS.Signature.WellFormed
    wf_σ_m : vote.σ_m.WellFormed

  structure Valid (election : Election) (vote : Vote) : Prop where
    correct_election : vote.electionId = election.electionId
    correct_block : vote.ebHash = election.ebHash
    valid_pool :
      match vote with
      | PersistentVote _ poolIndex _ _ => election.epoch.valid_index poolIndex
      | NonpersistentVote _ poolId _ _ _ => election.epoch.valid_poolid poolId

  def lookupPool (election : Election) (vote : Vote) (valid : vote.Valid election) : PoolKeyHash :=
    match vote with
    | PersistentVote _ poolIndex _ _ => election.epoch.stakes.lookupPoolId poolIndex valid.valid_pool
    | NonpersistentVote _ poolId _ _ _ => poolId

  def Authentic (election : Election) (vote : Vote) (valid : vote.Valid election) : Prop :=
    let epoch := election.epoch
    let registry := epoch.registry
    let poolId := vote.lookupPool election valid
    let validId : poolId ∈ registry.map Registration.poolId :=
     by
      cases vote
      case PersistentVote _ poolIndex _ _ =>
        apply epoch.pools_valid_ids
        let h₁ := valid.valid_pool
        simp [*] at h₁
        apply epoch.stakes.poolId_in_pools poolIndex h₁
      case NonpersistentVote _ _ _ _ _ =>
        apply epoch.pools_valid_ids
        apply valid.valid_pool
    let registration : Registration := registry.lookupRegistration poolId validId
    let mvk := registration.pool.mvk
    let eid := election.electionId.toByteArray
    let msg_eid := eid ++ election.epoch.nonce.toByteArray
    let ver_eid := vote.σ_eid.elim True $ BLS.Ver mvk msg_eid
    let msg_m := eid ++ election.ebHash.toByteArray
    let ver_m := BLS.Ver mvk msg_m vote.σ_m
    let has_seats := epoch.fa.voteWeight poolId vote.σ_eid ≠ none
    ver_eid ∧ ver_m ∧ has_seats

    def Checked (election : Election) (vote : Vote) (valid : vote.Valid election) : Prop :=
      vote.WellFormed ∧ vote.Authentic election valid

end Vote


end Leioscrypto
