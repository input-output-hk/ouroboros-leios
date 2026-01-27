
import Leioscrypto.Registration
import Leioscrypto.Types
import Leioscrypto.Util


namespace Leioscrypto


structure LeiosParameters where
  τ : Rat
  τ_bounded : (1 : Rat) / 2 < τ ∧ τ ≤ 1
  n : Nat
  n_positive : 0 < n
deriving Repr


structure EpochContext where
  pools : List (Pool × Coin)
  pools_not_duplicated : (pools.map Prod.fst).Nodup
  pools_have_stake : pools.Forall (fun a ↦ a.snd > 0)
  pools_sorted_nonincreasing : pools.Pairwise (fun x y ↦ x.snd ≥ y.snd)
  slot_range : Slot × Slot
  slot_range_ordered : slot_range.fst ≤ slot_range.snd
  nonce : PraosNonce
deriving Repr


structure ElectionContext where
  epochContext : EpochContext
  slot : Slot
  slot_in_epoch : epochContext.slot_range.fst ≤ slot ∧ slot ≤ epochContext.slot_range.snd
  ebHash : BlockHash
deriving Repr


end Leioscrypto
