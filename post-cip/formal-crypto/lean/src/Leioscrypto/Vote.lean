
import Leioscrypto.BLS
import Leioscrypto.Contexts
import Leioscrypto.Registration
import Leioscrypto.Types


namespace Leioscrypto


inductive Vote where
| PersistentVote : ElectionId → PoolIndex → BlockHash → BLS.Signature → Vote
| NonpersistentVote : ElectionId → PoolKeyHash → BLS.Signature → BlockHash → BLS.Signature → Vote

-- TODO: Create a valid vote.

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
      | PersistentVote _ poolIndex _ _ => election.epoch.fa.valid_persistent_poolindex poolIndex
      | NonpersistentVote _ poolId _ _ _ => election.epoch.fa.valid_nonpersistent_poolid poolId

  private def AuthenticPersistent (election : Election) (poolIndex : PoolIndex) (σ_m : BLS.Signature) (h: election.epoch.fa.valid_persistent_poolindex poolIndex) : Prop :=
    let epoch := election.epoch
    let fa := epoch.fa
    let stakes := fa.stakes
    let registry := epoch.registry
    let validIndex : stakes.valid_poolindex poolIndex :=
      by
        apply fa.persistent_index_is_valid_index
        apply h
    let poolId : PoolKeyHash := stakes.lookupPoolId poolIndex validIndex
    let validId : registry.valid_poolid poolId := epoch.valid_persistent_index_in_registry poolIndex validIndex
    let registration : Registration := registry.lookupRegistration poolId validId
    let eid := election.electionId.toByteArray
    let mvk := registration.pool.mvk
    let msg_m := eid ++ election.ebHash.toByteArray
    let ver_m := BLS.Ver mvk msg_m σ_m
    let weight : Rat := fa.persistentWeight poolIndex h
    let hasSeats := weight > 0
    ver_m ∧ hasSeats

  private def AuthenticNonpersistent (election : Election) (poolId : PoolKeyHash) (σ_eid : BLS.Signature) (σ_m : BLS.Signature) (h: election.epoch.fa.valid_nonpersistent_poolid poolId) : Prop :=
    let epoch := election.epoch
    let fa := epoch.fa
    let stakes := fa.stakes
    let registry := epoch.registry
    let validId : registry.valid_poolid poolId :=
      by
        apply epoch.valid_nonpersistent_id_in_registry
        apply h
    let registration : Registration := registry.lookupRegistration poolId validId
    let mvk := registration.pool.mvk
    let eid := election.electionId.toByteArray
    let msg_eid := eid ++ election.epoch.nonce.toByteArray
    let ver_eid := BLS.Ver mvk msg_eid σ_eid
    let msg_m := eid ++ election.ebHash.toByteArray
    let ver_m := BLS.Ver mvk msg_m σ_m
    let weight : Rat := fa.nonpersistentWeight poolId h.valid₁ σ_eid
    let hasSeats := weight > 0
    ver_eid ∧ ver_m ∧ hasSeats

  def Authentic (election : Election) (vote : Vote) (valid : vote.Valid election) : Prop :=
    match vote with
    | PersistentVote _ poolIndex _ σ_m => AuthenticPersistent election poolIndex σ_m $ by apply valid.valid_pool
    | NonpersistentVote _ poolId σ_eid _ σ_m => AuthenticNonpersistent election poolId σ_eid σ_m $ by apply valid.valid_pool
    /-
    let epoch := election.epoch
    let fa := epoch.fa
    let stakes := fa.stakes
    let registry := epoch.registry
    let h₁ : ∃ poolId : PoolKeyHash, registry.valid_poolid poolId :=
     sorry
    let poolId := vote.lookupPool election valid
    let validId : registry.valid_poolid poolId :=
     by
      cases vote
      case PersistentVote _ poolIndex _ _ =>
        have h₁ : fa.valid_persistent_poolindex poolIndex :=
          by
            apply valid.valid_pool
        obtain ⟨ _ , h₂ ⟩ := epoch.valid_persistent_index_in_registry poolIndex h₁

        --apply vote.lookupPool at poolId
        sorry
      case NonpersistentVote _ _ _ _ _ =>
        have h₁ : fa.valid_nonpersistent_poolid poolId :=
          by
            sorry
        let x := epoch.valid_nonpersistent_id_in_registry h₁
        exact x
        sorry
    let registration : Registration := registry.lookupRegistration poolId validId
    let mvk := registration.pool.mvk
    let eid := election.electionId.toByteArray
    let msg_eid := eid ++ election.epoch.nonce.toByteArray
    let ver_eid := vote.σ_eid.elim True $ BLS.Ver mvk msg_eid
    let msg_m := eid ++ election.ebHash.toByteArray
    let ver_m := BLS.Ver mvk msg_m vote.σ_m
    let has_seats := epoch.fa.voteWeight poolId vote.σ_eid ≠ none
    ver_eid ∧ ver_m ∧ has_seats
    -/

    def Checked (election : Election) (vote : Vote) (valid : vote.Valid election) : Prop :=
      vote.WellFormed ∧ vote.Authentic election valid

    structure Checked' (election : Election) (vote : Vote) : Prop where
      wf : vote.WellFormed
      valid : vote.Valid election
      authentic: vote.Authentic election valid

end Vote


end Leioscrypto
