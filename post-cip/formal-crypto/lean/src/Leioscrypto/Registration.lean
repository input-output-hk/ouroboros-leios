
import Leioscrypto.BLS
import Leioscrypto.Types
import Leioscrypto.Util
import Mathlib.Data.List.Nodup


namespace Leioscrypto


opaque verifyColdSignature : PoolKeyHash → ColdKeySignature → Prop


structure Pool where
  poolId : PoolKeyHash
  mvk : BLS.PublicKey
  μ : BLS.ProofOfPossession
deriving BEq

namespace Pool

  structure WellFormed (p : Pool) : Prop where
    wf_mvk : p.mvk.WellFormed
    wf_μ : p.μ.WellFormed

  -- TODO: Create a valid pool.

end Pool


structure Registration where
  pool : Pool
  issueCounter : Nat
  signature : ColdKeySignature
deriving BEq

namespace Registration

  structure WellFormed (reg : Registration) : Prop where
    wf_pool : reg.pool.WellFormed

  def poolId : Registration → PoolKeyHash :=
    Pool.poolId ∘ Registration.pool

  structure Authentic (reg : Registration) : Prop where
    signed_by_cold_key : verifyColdSignature reg.poolId reg.signature
    proven_possession : BLS.Check reg.pool.mvk reg.pool.μ

  def Checked (reg : Registration) : Prop :=
    reg.WellFormed ∧ reg.Authentic

  -- TODO: Create a valid registration.

end Registration


def Registry := List Registration
deriving Inhabited, Membership


namespace Registry

  structure Checked (rgy : Registry) : Prop where
    checked_registrations : ∀ reg ∈ rgy, reg.Checked
    unique_hashes : (rgy.map Registration.poolId).Nodup

  def valid_poolid (rgy : Registry) (poolId : PoolKeyHash) : Prop :=
    poolId ∈ rgy.map Registration.poolId

  theorem wf_empty : (default : Registry).Checked :=
    ⟨
      by
        intro p h
        contradiction
    , List.nodup_nil
    ⟩

  def deregister (poolId : PoolKeyHash) (rgy : Registry) : Registry :=
    let present (reg : Registration) : Bool := reg.poolId == poolId
    match rgy.find? present with
    | none => rgy
    | some reg => rgy.erase reg

  theorem checked_deregister (poolId : PoolKeyHash) (rgy :Registry) (h : rgy.Checked) : (deregister poolId rgy).Checked :=
    by
      dsimp [deregister]
      split
      · exact h
      · next reg _ =>
          let rgy' := rgy.erase reg
          have rgy_sublist_rgy' : rgy'.Sublist rgy := List.erase_sublist
          exact ⟨
            by
              intro reg' h₂
              have reg'_mem_rgy : reg' ∈ rgy := List.Sublist.mem h₂ rgy_sublist_rgy'
              have _ : reg'.Checked := h.checked_registrations reg' reg'_mem_rgy
              simp_all
          , by
              let pools := rgy.map Registration.poolId
              let pools' := rgy'.map Registration.poolId
              have pools'_sublist_pools : pools'.Sublist pools :=
                by
                  rw [List.sublist_map_iff]
                  exists rgy'
              apply List.Nodup.sublist pools'_sublist_pools h.unique_hashes
          ⟩

  def later_registration (rgy : Registry) (reg : Registration) : Prop :=
    let poolId : PoolKeyHash := reg.poolId
    let present (reg' : Registration) : Bool := reg'.poolId != poolId
    match rgy.find? present with
    | none => True
    | some reg' => reg'.issueCounter < reg.issueCounter

  def register (reg : Registration) (rgy : Registry) (_ : rgy.later_registration reg) : Registry :=
    let poolId : PoolKeyHash := reg.poolId
    let absent (reg' : Registration) : Bool := reg'.poolId != poolId
    reg :: rgy.filter absent

theorem checked_register (reg : Registration) (h₁ : reg.Checked) (rgy : Registry) (h₂ : rgy.Checked) (h₃ : rgy.later_registration reg) : (register reg rgy h₃).Checked :=
    by
      let poolId : PoolKeyHash := reg.poolId
      let absent (reg' : Registration) : Bool := reg'.poolId != poolId
      let rgy' := rgy.filter absent
      let rgy'' := reg :: rgy'
      have rgy'_sublist_rgy : rgy'.Sublist rgy :=
        by
          simp [rgy', List.filter_sublist]
      exact ⟨
        by
          intros reg' h₆
          cases h₆ with
          | head =>
            exact h₁
          | tail _ h_mem =>
            apply h₂.checked_registrations
            exact List.Sublist.mem h_mem rgy'_sublist_rgy
      , by
          let pools := rgy.map Registration.poolId
          let pools' := rgy'.map Registration.poolId
          have pools'_sublist_pools : pools'.Sublist pools :=
            by
              rw [List.sublist_map_iff]
              exists rgy'
          have pools'_nodup : pools'.Nodup :=
            List.Sublist.nodup pools'_sublist_pools h₂.unique_hashes
          have poolid_notin_pools' : ¬ poolId ∈ pools' :=
            by
              dsimp [pools', rgy', absent]
              rw [List.mem_map]
              intro h_contra
              obtain ⟨x, h_in_filter, h_id_eq⟩ := h_contra
              rw [List.mem_filter] at h_in_filter
              have h_ne := h_in_filter.2
              rw [h_id_eq] at h_ne
              simp at h_ne
          dsimp [register]
          simp [List.nodup_cons]
          apply pools'_nodup
      ⟩

  def lookupRegistration (poolId : PoolKeyHash) (rgy : Registry) (h : rgy.valid_poolid poolId) : Registration :=
    lookup₀ Registration.poolId rgy poolId h

  inductive IsValidRegistry : Registry → Prop
  | empty : IsValidRegistry default
  | deregister (rgy : Registry) (poolId : PoolKeyHash) : IsValidRegistry rgy → IsValidRegistry (rgy.deregister poolId)
  | register (rgy : Registry) (reg : Registration) (_ : reg.Checked) (h : rgy.later_registration reg): IsValidRegistry rgy → IsValidRegistry (rgy.register reg h)

end Registry


end Leioscrypto
