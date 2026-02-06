
import Leioscrypto.BLS
import Leioscrypto.Contexts
import Leioscrypto.Types


namespace Leioscrypto


structure Certificate where
  electionId : ElectionId
  ebHash : BlockHash
  persistentVotes : List PoolIndex
  nonpersistentVotes : List (PoolKeyHash × BLS.Signature)
  σ_tilde_eid : Option BLS.Signature
  σ_tilde_m : BLS.Signature

-- TODO: Create a valid certificate.

namespace Certificate

  structure WellFormed (cert : Certificate) : Prop where
    wf_σ_tilde_eid : cert.σ_tilde_eid.elim True BLS.Signature.WellFormed
    wf_σ_tilde_m : cert.σ_tilde_m.WellFormed

  structure Valid (cert : Certificate) (election : Election) : Prop where
    correct_election : cert.electionId = election.electionId
    correct_ebhash : cert.ebHash = election.ebHash
    unique_persistent_voters : cert.persistentVotes.Nodup
    unique_nonpersistent_voters : (cert.nonpersistentVotes.map Prod.fst).Nodup
    valid_persistent_ids : ∀ poolIndex ∈ cert.persistentVotes, election.epoch.valid_index poolIndex
    valid_persistent_voters : ∀ poolIndex ∈ cert.persistentVotes, election.epoch.fa.valid_persistent_poolindex poolIndex
    valid_nonpersistent_candidates : ∀ poolId ∈ cert.nonpersistentVotes.map Prod.fst, election.epoch.fa.valid_nonpersistent_poolid poolId

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
        $ cert.persistentVotes.map
          fun poolIndex ↦
            let h : fa.valid_persistent_poolindex poolIndex :=
              sorry
            fa.persistentWeight poolIndex h
    let nonpersistentWeight : Rat :=
      List.sum
        $ cert.nonpersistentVotes.attach.map
          fun ⟨ ⟨ poolId , σ_eid ⟩ , h₁ ⟩ ↦
            let h₂ : fa.stakes.valid_poolid poolId :=
              by
                have h₃ : election.epoch.fa.valid_nonpersistent_poolid poolId :=
                  by
                    apply valid.valid_nonpersistent_candidates
                    apply List.mem_map_of_mem h₁
                apply h₃.valid₁
            fa.nonpersistentWeight poolId h₂ σ_eid
    let has_quorum : Prop := (persistentWeight + nonpersistentWeight) ≥ stakes.total.cast * epoch.protocol.τ
    -- Final constraints.
    ver_σ_tilde_eid ∧ ver_σ_tilde_m ∧ has_quorum

  structure Checked (cert : Certificate) (election : Election) where
    wf : cert.WellFormed
    valid : cert.Valid election
    authentic : cert.Authentic election valid

end Certificate


end Leioscrypto
