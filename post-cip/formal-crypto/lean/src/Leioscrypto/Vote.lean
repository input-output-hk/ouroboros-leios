
import Leioscrypto.BLS
import Leioscrypto.Contexts
import Leioscrypto.Registration
import Leioscrypto.Types


namespace Leioscrypto


structure Vote where
  electionId : ElectionId
  ebHash : BlockHash
  poolIndex : PoolIndex
  sigma_eid : Option BLS.Signature
  sigma_m : BLS.Signature

namespace Vote

  structure WellFormed (v : Vote) : Prop where
    wf_sigma_eid : v.sigma_eid.elim True BLS.Signature.WellFormed
    wf_sigma_m : v.sigma_m.WellFormed

  def ValidSignatures (regs : Registry) (ctx : EpochContext) (vote : Vote) : Prop :=
    let poolIndex : Nat := vote.poolIndex
    let poolCount : Nat := ctx.pools.length
    let validIndex :  poolIndex < poolCount := sorry
    let poolId : PoolKeyHash := ctx.lookupPoolId poolIndex validIndex
    sorry

end Vote


end Leioscrypto
