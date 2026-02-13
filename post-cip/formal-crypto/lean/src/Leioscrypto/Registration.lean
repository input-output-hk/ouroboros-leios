
import Leioscrypto.BLS
import Leioscrypto.Types
import Leioscrypto.Util
import Mathlib.Data.List.Nodup


/-!
Pool registration in Leios.
-/


namespace Leioscrypto


/-- Verify the signature by a pool's cold key. -/
opaque verifyColdSignature : PoolKeyHash → ColdKeySignature → Prop


/-- A stakke pool.-/
structure Pool where
  /-- The pool identifier. -/
  poolId : PoolKeyHash
  /-- The public key. -/
  mvk : BLS.PublicKey
  /-- The proof of possession. -/
  μ : BLS.ProofOfPossession
deriving BEq

namespace Pool

  /-- A pool has valid BLS points. -/
  structure WellFormed (p : Pool) : Prop where
    wf_mvk : p.mvk.WellFormed
    wf_μ : p.μ.WellFormed

  /-- Create a pool. -/
  def makePool (poolId : PoolKeyHash) (secret : BLS.SecretKey) : Pool :=
    let ⟨ mvk , μ ⟩ := BLS.KeyGen secret
    ⟨ poolId , mvk , μ ⟩

  /-- Creating a pool yields a well-formed pool. -/
  theorem wf_make_pool (poolId : PoolKeyHash) (secret : BLS.SecretKey) : (makePool poolId secret).WellFormed :=
    by
      dsimp [makePool]
      obtain ⟨h_mvk, h_μ⟩ := BLS.wf_keygen secret
      constructor
      · exact h_mvk
      · exact h_μ

end Pool


/-- A registration for a pool. -/
structure Registration where
  /-- The pool data. -/
  pool : Pool
  /-- The registration issuance counter for the pool. -/
  issueCounter : Nat
  /-- The signature on the registration. -/
  signature : ColdKeySignature
deriving BEq

namespace Registration

  /-- A registration is well-formed if the pool data also is. -/
  structure WellFormed (reg : Registration) : Prop where
    wf_pool : reg.pool.WellFormed

  /-- The pool identifier. -/
  def poolId : Registration → PoolKeyHash :=
    Pool.poolId ∘ Registration.pool

  /-- A registration is cryptographically valid if signed by the cold key and having a cryptographically valid proof of key possession. -/
  structure Authentic (reg : Registration) : Prop where
    signed_by_cold_key : verifyColdSignature reg.poolId reg.signature
    proven_possession : BLS.Check reg.pool.mvk reg.pool.μ

  /-- A checked registration is well-formed and authentic. -/
  def Checked (reg : Registration) : Prop :=
    reg.WellFormed ∧ reg.Authentic

end Registration


/-- The registration is simply a list of registrations. -/
def Registry := List Registration
deriving Inhabited, Membership


namespace Registry

  /-- A registry is checked if all of its registrations are and they have unique pool identifiers. -/
  structure Checked (rgy : Registry) : Prop where
    checked_registrations : ∀ reg ∈ rgy, reg.Checked
    unique_hashes : (rgy.map Registration.poolId).Nodup

  /-- A pool identifier is in the registry. -/
  def valid_poolid (rgy : Registry) (poolId : PoolKeyHash) : Prop :=
    poolId ∈ rgy.map Registration.poolId

  /-- An empty registry is well-formed. -/
  theorem wf_empty : (default : Registry).Checked :=
    ⟨
      by
        intro p h
        contradiction
    , List.nodup_nil
    ⟩

  /-- De-registeer a pool. -/
  def deregister (poolId : PoolKeyHash) (rgy : Registry) : Registry :=
    let present (reg : Registration) : Bool := reg.poolId == poolId
    match rgy.find? present with
    | none => rgy
    | some reg => rgy.erase reg

  /-- De-registering a pool maintains well-formedness. -/
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

  /-- A registration is subsequent to a previous registration. -/
  def later_registration (rgy : Registry) (reg : Registration) : Prop :=
    let poolId : PoolKeyHash := reg.poolId
    let present (reg' : Registration) : Bool := reg'.poolId != poolId
    match rgy.find? present with
    | none => True
    | some reg' => reg'.issueCounter < reg.issueCounter

  /-- Register or re-register a pool. -/
  def register (reg : Registration) (rgy : Registry) (_ : rgy.later_registration reg) : Registry :=
    let poolId : PoolKeyHash := reg.poolId
    let absent (reg' : Registration) : Bool := reg'.poolId != poolId
    reg :: rgy.filter absent

  /-- Registration preserves well-formedness. -/
  theorem checked_register (reg : Registration) (h₁ : reg.Checked) (rgy : Registry) (h₂ : rgy.Checked) (h₃ : rgy.later_registration reg) : (register reg rgy h₃).Checked :=
    by
      dsimp [register]
      constructor
      · intros reg' reg'_in_rgy''
        cases reg'_in_rgy'' with
        | head =>
            exact h₁
        | tail _ reg'_mem =>
            let rgy' := rgy.filter fun reg' ↦ reg'.poolId != reg.poolId
            have rgy'_sublist_rgy : rgy'.Sublist rgy :=
              by
                simp [rgy', List.filter_sublist]
            apply h₂.checked_registrations
            exact List.Sublist.mem reg'_mem rgy'_sublist_rgy
      · rw [List.map_cons, List.nodup_cons]
        constructor
        · intro h_contra
          simp only [List.mem_map, List.mem_filter] at h_contra
          obtain ⟨_, ⟨_, h_ne⟩, h_eq⟩ := h_contra
          simp [h_eq] at h_ne
        · apply List.Sublist.nodup _ h₂.unique_hashes
          apply List.Sublist.map
          apply List.filter_sublist

  /-- Look up a registration for a pool identifier. -/
  def lookupRegistration (poolId : PoolKeyHash) (rgy : Registry) (h : rgy.valid_poolid poolId) : Registration :=
    lookup₀ Registration.poolId rgy poolId h

  /-- A Valid registry. -/
  inductive IsValidRegistry : Registry → Prop
  /-- Empty registry. -/
  | empty : IsValidRegistry default
  /-- De-registration. -/
  | deregister (rgy : Registry) (poolId : PoolKeyHash) : IsValidRegistry rgy → IsValidRegistry (rgy.deregister poolId)
  /-- Registration. -/
  | register (rgy : Registry) (reg : Registration) (_ : reg.Checked) (h : rgy.later_registration reg): IsValidRegistry rgy → IsValidRegistry (rgy.register reg h)

  /-- A valid registry is also a checked registry. -/
  theorem is_valid_implies_checked (rgy : Registry) (h : IsValidRegistry rgy) : rgy.Checked :=
    by
      induction h with
      | empty =>
          exact wf_empty
      | deregister rgy' poolId _ ih =>
          apply checked_deregister poolId rgy' ih
      | register rgy' reg reg_checked later _ ih =>
          apply checked_register reg reg_checked rgy' ih later

end Registry


end Leioscrypto
