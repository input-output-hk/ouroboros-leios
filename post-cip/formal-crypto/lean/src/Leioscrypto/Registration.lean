
import Aesop
import Leioscrypto.BLS
import Leioscrypto.Types
import Leioscrypto.Util
import Mathlib.Data.List.Nodup


namespace Leioscrypto


opaque validColdSignature (α : Type) (x : α) : PoolKeyHash → ColdKeySignature → Prop


structure Pool where
  poolKeyHash : PoolKeyHash
  mvk : BLS.PublicKey
  mu : BLS.PoP
deriving BEq

namespace Pool

  structure WellFormed (p : Pool) : Prop where
    wf_mvk : p.mvk.WellFormed
    wf_mu : p.mu.WellFormed

end Pool


structure Registration where
  pool : Pool
  issueCounter : Nat
  signature : ColdKeySignature
deriving BEq

namespace Registration

  structure WellFormed (r : Registration) : Prop where
    wf_pool : r.pool.WellFormed

end Registration


structure Registry where
  registrations : List Registration
deriving Inhabited

namespace Registry

  structure WellFormed (r : Registry) : Prop where
    wf_registrations : ∀ p ∈ r.registrations, p.WellFormed
    unique_hashes : (r.registrations.map $ Pool.poolKeyHash ∘ Registration.pool).Nodup

  def lookup (poolId : PoolKeyHash) (regs : Registry) (h : poolId ∈ regs.registrations.map (Pool.poolKeyHash ∘ Registration.pool)) : Pool :=
    let test (reg : Registration) : Bool := reg.pool.poolKeyHash == poolId
    match h_find : regs.registrations.find? test with
    | some reg => reg.pool
    | none =>
        have impossible : False :=
          by
            simp only [List.mem_map, Function.comp_apply] at h
            obtain ⟨r, r_in_list, r_has_id⟩ := h
            rw [List.find?_eq_none] at h_find
            specialize h_find r r_in_list
            rw [beq_iff_eq] at h_find
            rw [r_has_id] at h_find
            simp at h_find
        impossible.elim

  def deregister (poolId : PoolKeyHash) (regs : Registry) : Registry :=
    let registrations := regs.registrations
    match registrations.find? $ fun reg' ↦ reg'.pool.poolKeyHash == poolId with
    | none => regs
    | some reg => ⟨ registrations.erase reg ⟩

  theorem deregister_wf (poolId : PoolKeyHash) (regs :Registry) (h : regs.WellFormed) : (deregister poolId regs).WellFormed :=
    sorry
/-
  def deregister' (poolId : PoolKeyHash) (regs : Registry) : Registry :=
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
        ⟩
-/

  def register (reg : Registration) (regs : Registry) : Registry :=
    let poolId : PoolKeyHash := reg.pool.poolKeyHash
    let registrations := regs.registrations
    let test (reg' : Registration) : Bool := reg'.pool.poolKeyHash != poolId
    ⟨ registrations.filter test ⟩

  theorem register_wf (reg : Registration) (regs : Registry) (h : regs.WellFormed) : (register reg regs).WellFormed :=
    sorry
  /-
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

  -/

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
