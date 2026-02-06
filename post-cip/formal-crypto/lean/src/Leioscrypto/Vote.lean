
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
    let mvk := registration.pool.mvk
    let ver_m := BLS.Ver mvk election.blockMessage σ_m
    let weight : Rat := fa.persistentWeight poolIndex h
    let has_seats := weight > 0
    ver_m ∧ has_seats

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
    let ver_eid := BLS.Ver mvk election.eligibilityMessage σ_eid
    let ver_m := BLS.Ver mvk election.blockMessage σ_m
    let weight : Rat := fa.nonpersistentWeight poolId h.valid₁ σ_eid
    let has_seats := weight > 0
    ver_eid ∧ ver_m ∧ has_seats

  def Authentic (election : Election) (vote : Vote) (valid : vote.Valid election) : Prop :=
    match vote with
    | PersistentVote _ poolIndex _ σ_m => AuthenticPersistent election poolIndex σ_m $ by apply valid.valid_pool
    | NonpersistentVote _ poolId σ_eid _ σ_m => AuthenticNonpersistent election poolId σ_eid σ_m $ by apply valid.valid_pool

  structure Checked (election : Election) (vote : Vote) : Prop where
    wf : vote.WellFormed
    valid : vote.Valid election
    authentic: vote.Authentic election valid

  def makePersistentVote (election : Election) (poolIndex : PoolIndex) (secret : BLS.SecretKey) (_ : election.epoch.fa.valid_persistent_poolindex poolIndex) : Vote :=
    PersistentVote
      election.electionId
      poolIndex
      election.ebHash
      (BLS.Sign secret election.blockMessage)

  theorem wf_make_persistent_vote
      (election : Election)
      (poolIndex : PoolIndex)
      (secret : BLS.SecretKey)
      (h : election.epoch.fa.valid_persistent_poolindex poolIndex)
    : (makePersistentVote election poolIndex secret h).WellFormed :=
    by
      constructor
      · simp only [Option.elim]
        constructor
      · apply BLS.wf_sign

  theorem valid_make_persistent_vote
      (election : Election)
      (poolIndex : PoolIndex)
      (secret : BLS.SecretKey)
      (h : election.epoch.fa.valid_persistent_poolindex poolIndex)
    : (makePersistentVote election poolIndex secret h).Valid election :=
    by
      constructor
      · dsimp [makePersistentVote]
        simp_all
      · rfl
      · constructor

  theorem authentic_make_persistent_vote
      (election : Election)
      (poolIndex : PoolIndex)
      (secret : BLS.SecretKey)
      (h_idx : election.epoch.fa.valid_persistent_poolindex poolIndex)
      (h_val : (makePersistentVote election poolIndex secret h_idx).Valid election)
      (h_seats : election.epoch.fa.persistentWeight poolIndex h_idx > 0)
      (h_key : ∀ (h_s : election.epoch.fa.stakes.valid_poolindex poolIndex)
                 (h_r : election.epoch.registry.valid_poolid (election.epoch.fa.stakes.lookupPoolId poolIndex h_s)),
                 (election.epoch.registry.lookupRegistration _ h_r).pool.mvk = BLS.Spec.SkToPk secret)
    : (makePersistentVote election poolIndex secret h_idx).Authentic election h_val :=
    by
      unfold Authentic
      unfold AuthenticPersistent
      constructor
      · rw [h_key]
        apply BLS.verify_sign
      · exact h_seats

  theorem check_make_persistent_vote
      (election : Election)
      (poolIndex : PoolIndex)
      (secret : BLS.SecretKey)
      (h_idx : election.epoch.fa.valid_persistent_poolindex poolIndex)
      (h_seats : election.epoch.fa.persistentWeight poolIndex h_idx > 0)
      (h_key : ∀ (h_s : election.epoch.fa.stakes.valid_poolindex poolIndex)
                 (h_r : election.epoch.registry.valid_poolid (election.epoch.fa.stakes.lookupPoolId poolIndex h_s)),
                 (election.epoch.registry.lookupRegistration _ h_r).pool.mvk = BLS.Spec.SkToPk secret)
    : (makePersistentVote election poolIndex secret h_idx).Checked election :=
    by
      have h_val := valid_make_persistent_vote election poolIndex secret h_idx
      exact ⟨
        wf_make_persistent_vote election poolIndex secret h_idx,
        h_val,
        authentic_make_persistent_vote election poolIndex secret h_idx h_val h_seats h_key
      ⟩

  def makeNonpersistentVote (election : Election) (poolId : PoolKeyHash) (secret : BLS.SecretKey) (_ : election.epoch.fa.valid_nonpersistent_poolid poolId) : Vote :=
    NonpersistentVote
      election.electionId
      poolId
      (BLS.Sign secret election.eligibilityMessage)
      election.ebHash
      (BLS.Sign secret election.blockMessage)

  theorem wf_make_nonpersistent_vote
      (election : Election)
      (poolId : PoolKeyHash)
      (secret : BLS.SecretKey)
      (h : election.epoch.fa.valid_nonpersistent_poolid poolId)
    : (makeNonpersistentVote election poolId secret h).WellFormed :=
    by
      constructor
      · apply BLS.wf_sign
      · apply BLS.wf_sign

  theorem valid_make_nonpersistent_vote
      (election : Election)
      (poolId : PoolKeyHash)
      (secret : BLS.SecretKey)
      (h : election.epoch.fa.valid_nonpersistent_poolid poolId)
    : (makeNonpersistentVote election poolId secret h).Valid election :=
    by
      constructor
      · dsimp [makeNonpersistentVote]
        simp_all
      · rfl
      · constructor

  theorem authentic_make_nonpersistent_vote
      (election : Election)
      (poolId : PoolKeyHash)
      (secret : BLS.SecretKey)
      (h_id : election.epoch.fa.valid_nonpersistent_poolid poolId)
      (h_val : (makeNonpersistentVote election poolId secret h_id).Valid election)
      (h_seats : election.epoch.fa.nonpersistentWeight poolId h_id.valid₁ (BLS.Sign secret election.eligibilityMessage) > 0)
      (h_key : ∀ (h_r : election.epoch.registry.valid_poolid poolId), (election.epoch.registry.lookupRegistration poolId h_r).pool.mvk = BLS.Spec.SkToPk secret)
    : (makeNonpersistentVote election poolId secret h_id).Authentic election h_val :=
    by
      unfold Authentic
      simp only [makeNonpersistentVote]
      unfold AuthenticNonpersistent
      dsimp
      simp only [h_key]
      refine ⟨?_, ?_, ?_⟩
      · apply BLS.verify_sign
      · apply BLS.verify_sign
      · exact h_seats

  theorem check_make_nonpersistent_vote
      (election : Election)
      (poolId : PoolKeyHash)
      (secret : BLS.SecretKey)
      (h_id : election.epoch.fa.valid_nonpersistent_poolid poolId)
      (h_seats : election.epoch.fa.nonpersistentWeight poolId h_id.valid₁ (BLS.Sign secret election.eligibilityMessage) > 0)
      (h_key : ∀ (h_r : election.epoch.registry.valid_poolid poolId),
                 (election.epoch.registry.lookupRegistration poolId h_r).pool.mvk = BLS.Spec.SkToPk secret)
    : (makeNonpersistentVote election poolId secret h_id).Checked election :=
    by
      have h_val := valid_make_nonpersistent_vote election poolId secret h_id
      exact ⟨
        wf_make_nonpersistent_vote election poolId secret h_id,
        h_val,
        authentic_make_nonpersistent_vote election poolId secret h_id h_val h_seats h_key
      ⟩

end Vote


end Leioscrypto
