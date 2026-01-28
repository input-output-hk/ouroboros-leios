
import Leioscrypto.BLS
import Leioscrypto.Contexts
import Leioscrypto.Types


namespace Leioscrypto


structure Certificate (e : ElectionContext) where
  electionId : ElectionId
  ebHash : BlockHash
  persistentVotes : List PoolIndex
  nonpersistentVotes : List (PoolIndex × BLS.Signature)
  sigma_tilde_eid : Option BLS.Signature
  sigma_tilde_m : BLS.Signature
deriving Repr


end Leioscrypto
