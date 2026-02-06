
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

-- TODO: Create a valid pool.

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

-- TODO: Create a valid registration.

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

  --FIXME: Include constraint on issue counter.
  def register (reg : Registration) (rgy : Registry) : Registry :=
    let poolId : PoolKeyHash := reg.poolId
    let absent (reg' : Registration) : Bool := reg'.poolId != poolId
    reg :: rgy.filter absent

  theorem checked_register (reg : Registration) (h₁ : reg.Checked) (rgy : Registry) (h₂ : rgy.Checked) : (register reg rgy).Checked :=
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
          let pools := rgy.map Registration.poolId
          let pools' := rgy'.map Registration.poolId
          let pools'' := rgy'.map Registration.poolId
          have pools'_sublist_pools : pools'.Sublist pools :=
          by
            rw [List.sublist_map_iff]
            exists rgy'
          have pools'_nodup : pools'.Nodup := List.Sublist.nodup pools'_sublist_pools h₂.unique_hashes
          intros reg' h₆
          have reg'_mem_rgy'' : reg' ∈ rgy'' := h₆
          sorry
      , by
          let pools := rgy.map Registration.poolId
          let pools' := rgy'.map Registration.poolId
          let pools'' := rgy'.map Registration.poolId
          have pools'_sublist_pools : pools'.Sublist pools :=
          by
            rw [List.sublist_map_iff]
            exists rgy'
          have pools'_nodup : pools'.Nodup := List.Sublist.nodup pools'_sublist_pools h₂.unique_hashes
          have poolid_notin_pools' : ¬ poolId ∈ pools' :=
            by
              simp_all [pools', rgy', absent, poolId]
--        simp_all only [Function.comp_apply, not_false_eq_true, List.map_cons, List.nodup_cons, and_self, keyhashes', registrations', test, poolId, registrations, registrations'']
          sorry
      ⟩

  def lookupRegistration (poolId : PoolKeyHash) (rgy : Registry) (h : rgy.valid_poolid poolId) : Registration :=
    lookup₀ Registration.poolId rgy poolId h

  inductive IsValidRegistry : Registry → Prop
  | empty : IsValidRegistry default
  | deregister (rgy : Registry) (poolId : PoolKeyHash) : IsValidRegistry rgy → IsValidRegistry (rgy.deregister poolId)
  | register (rgy : Registry) (reg : Registration) : IsValidRegistry rgy → reg.Checked → IsValidRegistry (rgy.register reg)

end Registry


end Leioscrypto
