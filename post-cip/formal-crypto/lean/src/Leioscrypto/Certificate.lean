
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
    valid_persistent_voters : ∀ poolIndex ∈ c.persistentVotes, election.epoch.fa.valid_persistent_id poolIndex
    valid_nonpersistent_candidates : ∀ poolId ∈ c.nonpersistentVotes.map Prod.fst, election.epoch.fa.valid_nonpersistent_pool poolId

  def Authentic (c : Certificate) (election : Election) : Prop :=
    let epoch := election.epoch
    let fa := epoch.fa

/-
    let σ_m : BLS.Signature := BLS.AKey c.persistentVotes
    let weighPersistent (poolIndex : PoolIndex) : Option Rat :=
      do
        sorry
    let persistentWeight : Option Rat :=
      List.sum <$> c.persistentVotes.mapM weighPersistent
    let weighNonpersistent : PoolKeyHash × BLS.Signature → Option Rat
    | ⟨ poolId , σ_eid ⟩ => fa.voteWeight poolId (some σ_eid)
    let nonpersistentWeight : Option Rat :=
      List.sum <$> c.nonpersistentVotes.mapM weighNonpersistent
-/
    let has_quorum := sorry
    has_quorum

end Certificate


end Leioscrypto
