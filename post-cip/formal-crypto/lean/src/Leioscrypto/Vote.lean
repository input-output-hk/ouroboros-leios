
import Leioscrypto.BLS
import Leioscrypto.Contexts
import Leioscrypto.Registration
import Leioscrypto.Types


namespace Leioscrypto


structure Vote where
  electionId : ElectionId
  ebHash : BlockHash
  poolIndex : PoolIndex
  σ_eid : Option BLS.Signature
  σ_m : BLS.Signature

namespace Vote

  structure WellFormed (v : Vote) : Prop where
    wf_σ_eid : v.σ_eid.elim True BLS.Signature.WellFormed
    wf_σ_m : v.σ_m.WellFormed

  def Valid (election : Election) (vote : Vote) : Prop :=
    let correctElection := vote.electionId = election.electionId
    let correctBlock := vote.ebHash = election.ebHash
    let validIndex := vote.poolIndex < election.epoch.pools.length
    correctElection ∧ correctBlock ∧ validIndex

  def Authentic (election : Election) (vote : Vote) (wf : vote.WellFormed) (valid : vote.Valid election) : Prop :=
    let epoch := election.epoch
    let registry := epoch.registry
    let wf_registry := epoch.wf_registry
    let poolExists := valid.right.right
    let poolId := epoch.lookupPoolId vote.poolIndex poolExists
    let poolInEpoch : poolId ∈ epoch.pools.map Prod.fst := epoch.poolId_in_pools vote.poolIndex poolExists
    let validId := epoch.pools_valid_ids poolId poolInEpoch
    let registration : Registration := registry.lookupRegistration poolId validId
    let wf_pool := wf_registry.wf_registrations registration
    let mvk := registration.pool.mvk
    let eid := election.electionId.toByteArray
    let msg_eid := eid ++ election.epoch.nonce.toByteArray
    let ver_eid := vote.σ_eid.elim True $ BLS.Ver mvk msg_eid
    let msg_m := eid ++ election.ebHash.toByteArray
    let ver_m := BLS.Ver mvk msg_m vote.σ_m
    ver_eid ∧ ver_m

end Vote


end Leioscrypto
