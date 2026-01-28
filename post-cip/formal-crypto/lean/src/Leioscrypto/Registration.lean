
import Aesop
import Leioscrypto.BLS
import Leioscrypto.Types
import Leioscrypto.Util
import Mathlib.Data.List.Nodup


namespace Leioscrypto


opaque validColdSignature (α : Type) (x : α) : PoolKeyHash → ColdKeySignature → Prop


structure Pool where
  poolKeyHash : PoolKeyHash
  mvk : BLS.PubKey
  mvk_valid : mvk.valid
  mu : BLS.PoP
  mu_valid : mu.valid
deriving Repr, BEq


structure Registration where
  pool : Pool
  issueCounter : Nat
  signature : ColdKeySignature
deriving Repr, BEq


structure Registry where
  registrations : List Registration
  pools_unique_keyhash : (registrations.map $ Pool.poolKeyHash ∘ Registration.pool).Nodup
--pools_unique_blskeys : (registrations.map $ Pool.mvk ∘ Registration.pool).Nodup
deriving Repr

instance : Inhabited Registry where
  default :=
    ⟨
      default
    , List.nodup_nil
--  , List.nodup_nil
    ⟩


namespace Registry

  def deregister (poolId : PoolKeyHash) (regs : Registry) : Registry :=
    let registrations := regs.registrations
    match registrations.find? $ fun reg' ↦ reg'.pool.poolKeyHash == poolId with
    | none => regs
    | some reg =>
        let registrations' := registrations.erase reg
        let sublist_map_nodup {a : Type} (f : Pool → a) (h₀ : (registrations.map $ f ∘ Registration.pool).Nodup) : (registrations'.map $ f ∘ Registration.pool).Nodup :=
          by
            let xs := registrations.map $ f ∘ Registration.pool
            let xs' := registrations'.map $ f ∘ Registration.pool
            have h₁ : registrations'.Sublist registrations := List.erase_sublist
            have h₂ : xs'.Sublist xs :=
              by
                rw [List.sublist_map_iff]
                exists registrations'
            apply List.Nodup.sublist h₂ h₀
        ⟨
          registrations'
        , sublist_map_nodup Pool.poolKeyHash regs.pools_unique_keyhash
--      , sublist_map_nodup Pool.mvk regs.pools_unique_blskeys
        ⟩


  def register (regs : Registry) (reg : Registration) : Registry :=
    let poolId : PoolKeyHash := reg.pool.poolKeyHash
    let registrations := regs.registrations
    let test (reg' : Registration) : Bool := reg'.pool.poolKeyHash != poolId
    let registrations' := registrations.filter test
    let registrations'' := reg :: registrations'
    ⟨
      registrations''
    , -- FIXME: Refactor for succinctness and explicitness.
      by
        let keyhashes := registrations.map $ Pool.poolKeyHash ∘ Registration.pool
        let keyhashes' := registrations'.map $ Pool.poolKeyHash ∘ Registration.pool
        have h₁ : keyhashes'.Sublist keyhashes :=
          by
            rw [List.sublist_map_iff]
            exists registrations'
            simp_all only [List.filter_sublist, and_self, registrations', test, poolId, registrations, keyhashes']
        have h₂ : keyhashes'.Nodup := List.Sublist.nodup h₁ regs.pools_unique_keyhash
        have h₃ : ¬ poolId ∈ keyhashes' ∧ keyhashes'.Nodup :=
          by
            simp_all [keyhashes', registrations', test, poolId, registrations]
        simp_all only [Function.comp_apply, not_false_eq_true, List.map_cons, List.nodup_cons, and_self, keyhashes', registrations', test, poolId, registrations, registrations'']
    ⟩

  def ValidRegistration (reg : Registration) (regs : Registry) : Prop :=
    let test (reg' : Registration) : Bool := reg'.pool.poolKeyHash == reg.pool.poolKeyHash
    match regs.registrations.find? test with
    | none => True
    | some reg' => reg'.issueCounter > reg.issueCounter

end Registry


inductive IsValidRegistry : Registry → Prop
| empty : IsValidRegistry default
| deregister (regs : Registry) (poolId : PoolKeyHash) : IsValidRegistry regs → IsValidRegistry (regs.deregister poolId)
| register (regs : Registry) (reg : Registration) : IsValidRegistry regs → regs.ValidRegistration reg → IsValidRegistry (regs.register reg)


end Leioscrypto
