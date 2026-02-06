
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
          have h₁ : rgy'.Sublist rgy := List.erase_sublist
          exact ⟨
            by
              intro r hr
              have h_mem_orig : r ∈ rgy := List.Sublist.mem hr h₁
              have x : r.Checked := h.checked_registrations r h_mem_orig
              simp_all
          , by
              let xs := rgy.map Registration.poolId
              let xs' := rgy'.map Registration.poolId
              have h₂ : xs'.Sublist xs :=
                by
                  rw [List.sublist_map_iff]
                  exists rgy'
              apply List.Nodup.sublist h₂ h.unique_hashes
          ⟩

  --FIXME: Include constraint on issue counter.
  def register (reg : Registration) (rgy : Registry) : Registry :=
    let poolId : PoolKeyHash := reg.poolId
    let absent (reg' : Registration) : Bool := reg'.poolId != poolId
    reg :: rgy.filter absent

  theorem checked_register (reg : Registration) (rgy : Registry) (h : rgy.Checked) : (register reg rgy).Checked :=
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

  def lookupRegistration (poolId : PoolKeyHash) (rgy : Registry) (h : rgy.valid_poolid poolId) : Registration :=
    lookup₀ Registration.poolId rgy poolId h

  inductive IsValidRegistry : Registry → Prop
  | empty : IsValidRegistry default
  | deregister (rgy : Registry) (poolId : PoolKeyHash) : IsValidRegistry rgy → IsValidRegistry (rgy.deregister poolId)
  | register (rgy : Registry) (reg : Registration) : IsValidRegistry rgy → reg.Checked → IsValidRegistry (rgy.register reg)

end Registry


end Leioscrypto
