
import Aesop
import Leioscrypto.BLS
import Leioscrypto.Types
import Leioscrypto.Util
import Mathlib.Data.List.Nodup


namespace Leioscrypto


opaque validColdSignature (α : Type) (x : α) : PoolKeyHash → ColdKeySignature → Prop


structure Pool where
  poolId : PoolKeyHash
  mvk : BLS.PublicKey
  μ : BLS.ProofOfPossession
deriving BEq

namespace Pool

  structure WellFormed (p : Pool) : Prop where
    wf_mvk : p.mvk.WellFormed
    wf_μ : p.μ.WellFormed

end Pool


structure Registration where
  pool : Pool
  issueCounter : Nat
  signature : ColdKeySignature
deriving BEq

namespace Registration

  structure WellFormed (reg : Registration) : Prop where
    wf_pool : reg.pool.WellFormed

end Registration


def Registry := List Registration
deriving Inhabited, Membership

namespace Registry

  structure WellFormed (rgy : Registry) : Prop where
    wf_registrations : ∀ p ∈ rgy, p.WellFormed
    unique_hashes : (rgy.map $ Pool.poolId ∘ Registration.pool).Nodup

  theorem wf_empty : (default : Registry).WellFormed :=
    ⟨
      by
        intro p h
        contradiction
    , List.nodup_nil
    ⟩

  def deregister (poolId : PoolKeyHash) (rgy : Registry) : Registry :=
    let present (reg : Registration) : Bool := reg.pool.poolId == poolId
    match rgy.find? present with
    | none => rgy
    | some reg => rgy.erase reg

  theorem wf_deregister (poolId : PoolKeyHash) (rgy :Registry) (h : rgy.WellFormed) : (deregister poolId rgy).WellFormed :=
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

  def register (reg : Registration) (rgy : Registry) : Registry :=
    let poolId : PoolKeyHash := reg.pool.poolId
    let absent (reg' : Registration) : Bool := reg'.pool.poolId != poolId
    rgy.filter absent

  theorem wf_register (reg : Registration) (rgy : Registry) (h : rgy.WellFormed) : (register reg rgy).WellFormed :=
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

  def lookup (poolId : PoolKeyHash) (rgy : Registry) (h : poolId ∈ rgy.map (Pool.poolId ∘ Registration.pool)) : Pool :=
    let present (reg : Registration) : Bool := reg.pool.poolId == poolId
    match h_find : rgy.find? present with
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

end Registry


namespace Registration

  def Valid (reg : Registration) (rgy : Registry) : Prop :=
    let present (reg' : Registration) : Bool := reg'.pool.poolId == reg.pool.poolId
    match rgy.find? present with
    | none => reg.WellFormed
    | some reg' => reg.WellFormed ∧ reg'.issueCounter > reg.issueCounter

end Registration


inductive IsValidRegistry : Registry → Prop
| empty : IsValidRegistry default
| deregister (rgy : Registry) (poolId : PoolKeyHash) : IsValidRegistry rgy → IsValidRegistry (rgy.deregister poolId)
| register (rgy : Registry) (reg : Registration) : IsValidRegistry rgy → reg.Valid rgy → IsValidRegistry (rgy.register reg)


end Leioscrypto
