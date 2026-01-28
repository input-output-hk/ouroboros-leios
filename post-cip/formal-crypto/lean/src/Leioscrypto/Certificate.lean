
import Leioscrypto.BLS
import Leioscrypto.Contexts
import Leioscrypto.Types


namespace Leioscrypto


structure Certificate where
  electionId : ElectionId
  ebHash : BlockHash
  persistentVotes : List PoolIndex
  nonpersistentVotes : List (PoolIndex × BLS.Signature)
  sigma_tilde_eid : Option BLS.Signature
  sigma_tilde_m : BLS.Signature

namespace Certificate

  structure WellFormed (c : Certificate) : Prop where
    wf_sigma_tilde_eid : c.sigma_tilde_eid.elim True BLS.Signature.WellFormed
    wf_sigma_tilde_m : c.sigma_tilde_m.WellFormed

end Certificate


end Leioscrypto
