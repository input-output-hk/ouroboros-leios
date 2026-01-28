
import Leioscrypto.Registration
import Leioscrypto.Types
import Leioscrypto.Util
import Mathlib.Data.List.Defs


namespace Leioscrypto


structure LeiosParameters where
  τ : Rat
  τ_bounded : (1 : Rat) / 2 < τ ∧ τ ≤ 1
  n : Nat
  n_positive : 0 < n
deriving Repr


structure EpochContext where
  epoch : Nat
  pools : List (PoolKeyHash × Coin)
  pools_not_duplicated : (pools.map Prod.fst).Nodup
  pools_have_stake : pools.Forall (fun a ↦ a.snd > 0)
  pools_sorted_nonincreasing : pools.Pairwise (fun x y ↦ x.snd ≥ y.snd)
  slot_range : Slot × Slot
  slot_range_ordered : slot_range.fst ≤ slot_range.snd
  nonce : PraosNonce

namespace EpochContext

  def Valid (reg: Registry) (ctx : EpochContext) : Prop :=
    ∀ p ∈ ctx.pools.map Prod.fst, p ∈ reg.registrations.map (Pool.poolKeyHash ∘ Registration.pool)

  def lookup (ctx : EpochContext) (i : Nat) (h : i < ctx.pools.length) : PoolKeyHash × Coin :=
    ctx.pools.get ⟨ i, h ⟩

  def lookupPoolId (ctx : EpochContext) (i : Nat) (h : i < ctx.pools.length) : PoolKeyHash :=
    Prod.fst $ ctx.pools.get ⟨ i, h ⟩

end EpochContext


structure ElectionContext where
  epochContext : EpochContext
  slot : Slot
  slot_in_epoch : epochContext.slot_range.fst ≤ slot ∧ slot ≤ epochContext.slot_range.snd
  electionId : ElectionId
  electionId_eq_slot : electionId = slot
  ebHash : BlockHash


end Leioscrypto
