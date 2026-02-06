
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

  structure WellFormed (c : Certificate) : Prop where
    wf_σ_tilde_eid : c.σ_tilde_eid.elim True BLS.Signature.WellFormed
    wf_σ_tilde_m : c.σ_tilde_m.WellFormed

  structure Valid (c : Certificate) (election : Election) : Prop where
    correct_election : c.electionId = election.electionId
    correct_ebhash : c.ebHash = election.ebHash
    unique_persistent_voters : c.persistentVotes.Nodup
    unique_nonpersistent_voters : (c.nonpersistentVotes.map Prod.fst).Nodup
    valid_persistent_ids : ∀ poolIndex ∈ c.persistentVotes, election.epoch.valid_index poolIndex
    valid_persistent_voters : ∀ poolIndex ∈ c.persistentVotes, election.epoch.fa.valid_persistent_poolindex poolIndex
    valid_nonpersistent_candidates : ∀ poolId ∈ c.nonpersistentVotes.map Prod.fst, election.epoch.fa.valid_nonpersistent_poolid poolId

  def Authentic (cert : Certificate) (election : Election) (valid : cert.Valid election) : Prop :=
    let epoch := election.epoch
    -- Public keys.
    let persistentKeys : List BLS.PublicKey :=
      sorry
    let nonpersistentKeys : List BLS.PublicKey :=
      sorry
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
    let fa := epoch.fa
    let stakes := fa.stakes
    let persistentWeight : Rat :=
      List.sum
        $ cert.persistentVotes.map
          fun poolIndex ↦
            let h : fa.valid_persistent_poolindex poolIndex := sorry
            fa.persistentWeight poolIndex h
    let nonpersistentWeight : Rat :=
      List.sum
        $ cert.nonpersistentVotes.map
          fun ⟨ poolId , σ_eid ⟩ ↦
            let h : fa.stakes.valid_poolid poolId := sorry
            fa.nonpersistentWeight poolId h σ_eid
    let has_quorum : Prop := (persistentWeight + nonpersistentWeight) ≥ stakes.total.cast * epoch.protocol.τ
    -- Final constraints.
    ver_σ_tilde_eid ∧ ver_σ_tilde_m ∧ has_quorum

end Certificate


end Leioscrypto
