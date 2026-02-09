
import Leioscrypto.BLS
import Leioscrypto.Contexts
import Leioscrypto.Types
import Leioscrypto.Vote


/-!
Leios certificates.
-/


namespace Leioscrypto


/-- Leios certificate. -/
structure Certificate where
  /-- The election identifier. -/
  electionId : ElectionId
  /-- The hash of the EB being certified. -/
  ebHash : BlockHash
  /-- List of persistent voters. -/
  persistentVotes : List PoolIndex
  /-- List of non-persistent voters and their eligibility proof. -/
  nonpersistentVotes : List (PoolKeyHash × BLS.Signature)
  /-- Aggregate signature on the votes. -/
  σ_tilde_eid : Option BLS.Signature
  /-- Aggregate signature on the eligibility. -/
  σ_tilde_m : BLS.Signature

namespace Certificate

  /-- A well-formed certificate contains valid BLS points. -/
  structure WellFormed (cert : Certificate) : Prop where
    wf_σ_tilde_eid : cert.σ_tilde_eid.elim True BLS.Signature.WellFormed
    wf_σ_tilde_m : cert.σ_tilde_m.WellFormed

  /-- A valid certificate is constistent with its corresponding election. -/
  structure Valid (cert : Certificate) (election : Election) : Prop where
    /-- The certificate is for the correct election. -/
    correct_election : cert.electionId = election.electionId
    /-- The certificate is for the correct EB hash. -/
    correct_ebhash : cert.ebHash = election.ebHash
    /-- Persistent voters vote no more than once. -/
    unique_persistent_voters : cert.persistentVotes.Nodup
    /-- Non-persistent voters vote no more than once. -/
    unique_nonpersistent_voters : (cert.nonpersistentVotes.map Prod.fst).Nodup
    /-- Persistent voters have valid indices into the epoch stake distribution. -/
    valid_persistent_ids : ∀ poolIndex ∈ cert.persistentVotes, election.epoch.valid_index poolIndex
    /-- Persistent voters are indeed persistent in the epoch. -/
    valid_persistent_voters : ∀ poolIndex ∈ cert.persistentVotes, election.epoch.fa.valid_persistent_poolindex poolIndex
    /-- Non-persistent voters are indeed non-persistent in the epoch. -/
    valid_nonpersistent_candidates : ∀ poolId ∈ cert.nonpersistentVotes.map Prod.fst, election.epoch.fa.valid_nonpersistent_poolid poolId

  /-- An authentic certificate passes cryptographic verification. -/
  def Authentic (cert : Certificate) (election : Election) (valid : cert.Valid election) : Prop :=
    let epoch := election.epoch
    let registry := epoch.registry
    let fa := epoch.fa
    let stakes := fa.stakes
    -- Public keys.
    let persistentKeys : List BLS.PublicKey :=
      cert.persistentVotes.attach.map
        fun ⟨ poolIndex , h₁ ⟩ ↦
          let validIndex : stakes.valid_poolindex poolIndex :=
            by
              apply fa.persistent_index_is_valid_index
              apply valid.valid_persistent_voters
              exact h₁
          let poolId : PoolKeyHash := stakes.lookupPoolId poolIndex validIndex
          let validId : registry.valid_poolid poolId := epoch.valid_persistent_index_in_registry poolIndex validIndex
          let registration : Registration := registry.lookupRegistration poolId validId
          registration.pool.mvk
    let nonpersistentKeys : List BLS.PublicKey :=
      cert.nonpersistentVotes.attach.map
        fun ⟨ ⟨ poolId , _ ⟩ , h₁ ⟩ ↦
          let validId : registry.valid_poolid poolId :=
            by
              apply epoch.valid_nonpersistent_id_in_registry
              apply valid.valid_nonpersistent_candidates
              apply List.mem_map_of_mem h₁
          let reg := registry.lookupRegistration poolId validId
          reg.pool.mvk
    let keys : List BLS.PublicKey := persistentKeys ++ nonpersistentKeys
    -- Verify signature on eligibility.
    let σ_eid : List BLS.Signature := cert.nonpersistentVotes.map Prod.snd
    let bkey : BLS.PublicKey := BLS.BKey nonpersistentKeys σ_eid
    let bsig : BLS.Signature := BLS.BSig σ_eid
    let ver_σ_tilde_eid : Prop := BLS.Ver bkey election.eligibilityMessage bsig
    -- Verify signature on block.
    let akey : BLS.PublicKey := BLS.AKey keys
    let ver_σ_tilde_m : Prop := BLS.Ver akey election.blockMessage cert.σ_tilde_m
    -- Quorum computation.
    let persistentWeight : Rat :=
      List.sum
        $ cert.persistentVotes.attach.map
          fun ⟨ poolIndex , h₁ ⟩ ↦
            let h₂ := valid.valid_persistent_voters poolIndex h₁
            fa.persistentWeight poolIndex h₂
    let nonpersistentWeight : Rat :=
      List.sum
        $ cert.nonpersistentVotes.attach.map
          fun ⟨ ⟨ poolId , σ_eid ⟩ , h₁ ⟩ ↦
            let h₂ := valid.valid_nonpersistent_candidates poolId (List.mem_map_of_mem h₁)
            fa.nonpersistentWeight poolId h₂.valid₁ σ_eid
    let has_quorum : Prop := (persistentWeight + nonpersistentWeight) ≥ stakes.total.cast * epoch.protocol.τ
    -- Final constraints.
    ver_σ_tilde_eid ∧ ver_σ_tilde_m ∧ has_quorum

  /-- A checked certificate is well-formed, valid, and authentic. -/
  structure Checked (cert : Certificate) (election : Election) where
    wf : cert.WellFormed
    valid : cert.Valid election
    authentic : cert.Authentic election valid

  /-- Create a certificate. -/
  def makeCertificate
      (election : Election)
      (votes : List Vote)
    : Option Certificate :=
    -- FIXME: Needs implementation.
    sorry

  /-- Created certificates are also well-formed, valid, and authentic. -/
  theorem check_make_certificate
      (election : Election)
      (votes : List Vote)
      (checked_votes : ∀vote ∈ votes, vote.Checked election)
      (unique_voters : (votes.map Vote.voter).Nodup)
      (cert : Certificate)
      (h_some : makeCertificate election votes = some cert)
      (h_checked : ∀ vote ∈ votes, vote.Checked election)
    : cert.Checked election :=
    -- FIXME: Needs proof.
    sorry

end Certificate


end Leioscrypto
