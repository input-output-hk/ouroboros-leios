
import Aesop
import Leioscrypto.FaitAccompli
import Leioscrypto.Registration
import Leioscrypto.Types
import Mathlib.Data.List.Defs


namespace Leioscrypto


-- Note that these contextual types are correct by construction because they are not deserialized from data provided by potentially corrupt parties.


structure LeiosParameters where
  τ : Rat
  τ_bounded : (1 : Rat) / 2 < τ ∧ τ ≤ 1
  n : Nat
  n_positive : 0 < n


structure Epoch where
  registry : Registry
  valid_registry : registry.IsValidRegistry
  number : Nat
  stakes : StakeDistribution
  pools_valid_ids : ∀ p ∈ stakes.pools.map Prod.fst, p ∈ registry.map Registration.poolId
  slot_range : Slot × Slot
  slot_range_ordered : slot_range.fst ≤ slot_range.snd
  nonce : PraosNonce


structure Election where
  epoch : Epoch
  slot : Slot
  slot_in_epoch : epoch.slot_range.fst ≤ slot ∧ slot ≤ epoch.slot_range.snd
  electionId : ElectionId
  electionId_eq_slot : electionId = slot
  ebHash : BlockHash


end Leioscrypto
