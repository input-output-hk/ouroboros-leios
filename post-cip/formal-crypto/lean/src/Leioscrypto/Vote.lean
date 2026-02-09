
import Leioscrypto.BLS
import Leioscrypto.Contexts
import Leioscrypto.Registration
import Leioscrypto.Types


/-!
Leios votes.
-/


namespace Leioscrypto


/-- A vote. -/
inductive Vote where
/-- A vote by a persistent voter. -/
| PersistentVote : ElectionId → PoolIndex → BlockHash → BLS.Signature → Vote
/-- A vote by a non-persistent voter. -/
| NonpersistentVote : ElectionId → PoolKeyHash → BLS.Signature → BlockHash → BLS.Signature → Vote

namespace Vote

  /---The voter. -/
  def voter : Vote → PoolIndex ⊕ PoolKeyHash
  | PersistentVote _ poolIndex _ _ => Sum.inl poolIndex
  | NonpersistentVote _ poolId _ _ _ => Sum.inr poolId

  /-- The election identifier. -/
  def electionId : Vote → ElectionId
  | PersistentVote eid _ _ _ => eid
  | NonpersistentVote eid _ _ _ _ => eid

  /-- The hash of the EB. -/
  def ebHash : Vote → BlockHash
  | PersistentVote _ _ bh _ => bh
  | NonpersistentVote _ _ _ bh _ => bh

  /-- The proof of eligibility, just for a non-persistent voter. -/
  def σ_eid : Vote → Option BLS.Signature
  | PersistentVote _ _ _ _ => none
  | NonpersistentVote _ _ sig _ _ => some sig

  /-- The signature. -/
  def σ_m : Vote → BLS.Signature
  | PersistentVote _ _ _ sig => sig
  | NonpersistentVote _ _ _ _ sig => sig

  /-- A vote has valid BLS points.-/
  structure WellFormed (vote : Vote) : Prop where
    wf_σ_eid : vote.σ_eid.elim True BLS.Signature.WellFormed
    wf_σ_m : vote.σ_m.WellFormed

  /-- A vote is valid for a particular election. -/
  structure Valid (election : Election) (vote : Vote) : Prop where
    /-- The election identifier matches. -/
    correct_election : vote.electionId = election.electionId
    /-- The block matches. -/
    correct_block : vote.ebHash = election.ebHash
    /-- The pool is present in the sortition. -/
    valid_pool :
      match vote with
      | PersistentVote _ poolIndex _ _ => election.epoch.fa.valid_persistent_poolindex poolIndex
      | NonpersistentVote _ poolId _ _ _ => election.epoch.fa.valid_nonpersistent_poolid poolId

  /-- A persistent vote is authentic if the signature is authentic and the voter has stake. -/
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

  /-- A non-persistent vote is authentic if the signature is valid, the voter has seats, and they are eligible. -/
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

  /-- An authentic vote. -/
  def Authentic (election : Election) (vote : Vote) (valid : vote.Valid election) : Prop :=
    match vote with
    | PersistentVote _ poolIndex _ σ_m => AuthenticPersistent election poolIndex σ_m $ by apply valid.valid_pool
    | NonpersistentVote _ poolId σ_eid _ σ_m => AuthenticNonpersistent election poolId σ_eid σ_m $ by apply valid.valid_pool

  structure Checked (election : Election) (vote : Vote) : Prop where
    wf : vote.WellFormed
    valid : vote.Valid election
    authentic: vote.Authentic election valid

  /-- Create a persistent vote. -/
  def makePersistentVote (election : Election) (poolIndex : PoolIndex) (secret : BLS.SecretKey) (_ : election.epoch.fa.valid_persistent_poolindex poolIndex) : Vote :=
    PersistentVote
      election.electionId
      poolIndex
      election.ebHash
      (BLS.Sign secret election.blockMessage)

  /-- A created persistent vote is well-formed. -/
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

  /-- A created persistent vote is valid. -/
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

  /-- A created persistent vote is authentic. -/
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

  /-- A created persistetn vote is checked. -/
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

  /-- Create a non-persistent vote. -/
  def makeNonpersistentVote (election : Election) (poolId : PoolKeyHash) (secret : BLS.SecretKey) (_ : election.epoch.fa.valid_nonpersistent_poolid poolId) : Vote :=
    NonpersistentVote
      election.electionId
      poolId
      (BLS.Sign secret election.eligibilityMessage)
      election.ebHash
      (BLS.Sign secret election.blockMessage)

  /-- A created non-persistetn vote is well-formed. -/
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

  /-- A created non-persistent vote is valid. -/
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

  /-- A crated non-persistent vote is authentic. -/
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

  /-- A crated non-persistent vote is checked. -/
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

  /-- Create a vote, if possible. -/
  def makeVote (election : Election) (poolId : PoolKeyHash) (sk : BLS.SecretKey) : Option Vote :=
    match election.isEligible poolId with
    | Eligible.IsPersistent h =>
        let fa := election.epoch.fa
        let poolIndex : PoolIndex := fa.stakes.lookupPoolIndex poolId h.valid₁
        some $ makePersistentVote election poolIndex sk h.valid₂
    | Eligible.IsNonpersistent h =>
        some $ makeNonpersistentVote election poolId sk h
    | Eligible.NotElibible =>
        none

  /-- A created vote is checked. -/
  theorem check_make_vote
      (election : Election)
      (poolId : PoolKeyHash)
      (sk : BLS.SecretKey)
      (vote : Vote)
      (h_some : makeVote election poolId sk = some vote)
      -- FIXME: It may be possible to eliminate the need for `h_seats_p`.
      (h_seats_p : ∀ i h, election.epoch.fa.persistentWeight i h > 0)
      -- FIXME: It may be possible to eliminate the need for `h_seats_n`.
      (h_seats_n : ∀ id h sig, election.epoch.fa.nonpersistentWeight id h sig > 0)
      (h_key : ∀ (h_r : election.epoch.registry.valid_poolid poolId), (election.epoch.registry.lookupRegistration poolId h_r).pool.mvk = BLS.Spec.SkToPk sk)
    : vote.Checked election :=
    by
      unfold makeVote at h_some
      match h_elig : election.isEligible poolId with
      | Eligible.IsPersistent h_pers =>
        simp only [h_elig] at h_some
        simp only [Option.some.injEq] at h_some
        rw [← h_some]
        let fa := election.epoch.fa
        let stakes := fa.stakes
        let poolIndex := stakes.lookupPoolIndex poolId h_pers.valid₁
        refine check_make_persistent_vote election poolIndex sk h_pers.valid₂ (h_seats_p poolIndex h_pers.valid₂) ?_
        intro h_s h_r
        have h_roundtrip : stakes.lookupPoolId poolIndex h_s = poolId := by
          -- FIXME: Needs proof.
          sorry
        rw [h_roundtrip] at h_r
        aesop
      | Eligible.IsNonpersistent h_non =>
        simp only [h_elig] at h_some
        simp only [Option.some.injEq] at h_some
        rw [← h_some]
        refine check_make_nonpersistent_vote election poolId sk h_non ?_ ?_
        · apply h_seats_n
        · apply h_key
      | Eligible.NotElibible =>
        simp only [h_elig] at h_some
        contradiction

end Vote


end Leioscrypto
