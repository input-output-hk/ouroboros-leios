{-# OPTIONS --safe #-}

{- Module: Leios.Ledger.Validation

   The validation functionality for endorser blocks, as a machine in the
   style of 'CategoricalCrypto.Machine'.  It replaces the static validity
   oracle 'isValidityChecked' of the spec's 'SpecStructure': validation
   (scripts, signatures, the ledger rules) takes time that depends on the
   node and its environment, not on the EB alone, so it is a stateful
   functionality the protocol talks to.

        protocol (Leios)
              ↕  ValIO:  SUBMIT eb, QUERY h  /  RESULT h r
      ┌───────┴────────┐
      │   validation   │   state: the clock and the EBs submitted
      └───────↕────────┘
              ValObs:  TICK, DONE h   (from the environment below)

   The protocol submits an EB, which the functionality remembers, and
   queries it by reference, getting 'Valid', 'Invalid', 'InProgress' or
   'Unknown' (never submitted); a submission answers as a query does.  Time
   is the environment's: it advances the clock once per slot.  Validation
   of a submitted EB completes when the environment reports it ('DONE'),
   and at the latest 'Δ' slots after submission: 'InProgress' cannot
   outlast the bound ('bounded-InProgress').  The channel 'ValIO' is the one
   the spec change of 'LinearLeiosStack' gives Linear Leios.  What a completed validation answers is
   the backend's 'verdict', so the machine is parametric over the ledger
   that validates: 'Leios.Ledger.Validation.STS' gives the backend of a
   decidable ledger transition system, and 'Leios.Ledger.Validation.Dijkstra'
   instantiates it with the Dijkstra era's 'EB' rule.  The trace verifier
   runs it with the backend a trace can support (see 'LinearLeiosStack').
-}

open import Leios.Prelude hiding (_⊗_; _∨_)
open import Data.Bool using (_∨_; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Maybe.Properties using (just-injective)

open import CategoricalCrypto hiding (id; _∘_)
open import CategoricalCrypto.Machine.Trace using (Checker; Checkable; Step; step)
import CategoricalCrypto.Machine.Trace as MT

open import Tactic.Defaults
open import Tactic.Derive.DecEq

module Leios.Ledger.Validation where

------------------------------------------------------------------------------
-- Answers and verdicts

-- The status of an EB, as a query reports it.
data ValidationResult : Type where
  Valid Invalid InProgress Unknown : ValidationResult

unquoteDecl DecEq-ValidationResult =
  derive-DecEq ((quote ValidationResult , DecEq-ValidationResult) ∷ [])

-- What a completed validation decides.
data Verdict : Type where
  accept reject : Verdict

-- A ledger that validates EBs: the verdict of validating a submission.
record Backend (EB : Type) : Type where
  field verdict : EB → Verdict

-- The backend of a log that records no transaction bodies: what the node
-- acquired, it validates successfully.  A log shows when validation
-- completes, not what it decides.
acceptAll : ∀ {EB} → Backend EB
acceptAll = record { verdict = λ _ → accept }

toResult : Verdict → ValidationResult
toResult accept = Valid
toResult reject = Invalid

toResult≢InProgress : ∀ v → toResult v ≢ InProgress
toResult≢InProgress accept ()
toResult≢InProgress reject ()

T⇒≡ : ∀ {b} → T b → b ≡ true
T⇒≡ {true} _ = refl

------------------------------------------------------------------------------
-- The interface

module Interface (EB Ref : Type) where

  -- 'Out' from the protocol to the functionality, 'In' the reverse.
  data ValIOF : Mode → Type where
    SUBMIT : EB → ValIOF Out
    QUERY  : Ref → ValIOF Out
    RESULT : Ref → ValidationResult → ValIOF In

  ValIO : Channel
  ValIO = simpleChannel ValIOF

  -- What the environment reports: a new slot, and the validation of an EB
  -- completed.
  data ValObsF : Mode → Type where
    TICK : ValObsF In
    DONE : Ref → ValObsF In

  ValObs : Channel
  ValObs = simpleChannel ValObsF

------------------------------------------------------------------------------
-- The machine

module Functionality
  (EB Ref : Type) ⦃ _ : DecEq Ref ⦄
  (ref     : EB → Ref)
  (backend : Backend EB) (open Backend backend)
  -- How long validation may stay in progress after submission.
  (Δ : ℕ)
  where

  open Interface EB Ref public

  record Submitted : Type where
    constructor ⟨_,_,_⟩
    field eb    : EB
          since : ℕ     -- the slot it was submitted in
          done  : Bool  -- whether the environment reported completion

  open Submitted

  record ValState : Type where
    field clock : ℕ
          subs  : List (Ref × Submitted)

  open ValState

  initValState : ℕ → ValState
  initValState n = record { clock = n ; subs = [] }

  -- The first submission under a reference.
  lookupᵛ : Ref → List (Ref × Submitted) → Maybe Submitted
  lookupᵛ h [] = nothing
  lookupᵛ h ((h′ , e) ∷ xs) with h ≟ h′
  ... | yes _ = just e
  ... | no  _ = lookupᵛ h xs

  -- Validation has completed by slot 'c': it was reported, or the bound
  -- has passed.
  completed : ℕ → Submitted → Bool
  completed c e = done e ∨ (since e + Δ N.≤ᵇ c)

  statusAt : ℕ → Maybe Submitted → ValidationResult
  statusAt c nothing  = Unknown
  statusAt c (just e) = if completed c e then toResult (verdict (eb e)) else InProgress

  status : ValState → Ref → ValidationResult
  status s h = statusAt (clock s) (lookupᵛ h (subs s))

  submittedAt : ValState → Ref → Maybe ℕ
  submittedAt s h = since <$> lookupᵛ h (subs s)

  -- Submitting an EB a second time changes nothing: the functionality
  -- remembers the first submission.
  submit′ : Maybe Submitted → ValState → EB → ValState
  submit′ (just _) s _  = s
  submit′ nothing  s eb = record s { subs = (ref eb , ⟨ eb , clock s , false ⟩) ∷ subs s }

  submit : ValState → EB → ValState
  submit s eb = submit′ (lookupᵛ (ref eb) (subs s)) s eb

  -- A report of completion for an EB never submitted is ignored.
  finish′ : Maybe Submitted → ValState → Ref → ValState
  finish′ nothing  s _ = s
  finish′ (just e) s h = record s { subs = (h , record e { done = true }) ∷ subs s }

  finish : ValState → Ref → ValState
  finish s h = finish′ (lookupᵛ h (subs s)) s h

  tick : ValState → ValState
  tick s = record s { clock = suc (clock s) }

  private variable
    s : ValState
    x : EB
    h : Ref

  data _-⟦_/_⟧ᵛ⇀_ : MachineType ValObs ValIO ValState where

    Submit : let s′ = submit s x in
      s -⟦ L⊗ (ϵ ᵗ¹) ↑ₒ SUBMIT x / just (L⊗ (ϵ ᵗ¹) ↑ᵢ RESULT (ref x) (status s′ (ref x))) ⟧ᵛ⇀ s′

    Query :
      s -⟦ L⊗ (ϵ ᵗ¹) ↑ₒ QUERY h / just (L⊗ (ϵ ᵗ¹) ↑ᵢ RESULT h (status s h)) ⟧ᵛ⇀ s

    Tick :
      s -⟦ ϵ ⊗R ↑ᵢ TICK / nothing ⟧ᵛ⇀ tick s

    Done :
      s -⟦ ϵ ⊗R ↑ᵢ DONE h / nothing ⟧ᵛ⇀ finish s h

  ValM : Machine ValObs ValIO
  ValM .Machine.State   = ValState
  ValM .Machine.stepRel = _-⟦_/_⟧ᵛ⇀_

  ----------------------------------------------------------------------------
  -- Bounded InProgress

  -- A query at least 'Δ' slots after submission does not answer
  -- 'InProgress'.
  bounded-InProgress : ∀ s h {m} → submittedAt s h ≡ just m → m + Δ N.≤ clock s
                     → status s h ≢ InProgress
  bounded-InProgress s h eq m+Δ≤c with lookupᵛ h (subs s)
  ... | just e with refl ← just-injective eq
    rewrite T⇒≡ (N.≤⇒≤ᵇ m+Δ≤c) | ∨-zeroʳ (done e) = toResult≢InProgress (verdict (eb e))

  -- What the step of a query answers.
  opaque
    unfolding _⊗₀_

    answerOf : Maybe (MT.Output ValM) → Maybe ValidationResult
    answerOf (just (inj₂ (RESULT _ r))) = just r
    answerOf _                          = nothing

    query-answer : ∀ {s s′ o} → s -⟦ L⊗ (ϵ ᵗ¹) ↑ₒ QUERY h / o ⟧ᵛ⇀ s′
                 → answerOf o ≡ just (status s h)
    query-answer Query = refl

  -- The same, of the machine's steps: past the bound, no query step answers
  -- 'InProgress'.
  bounded-InProgress-step : ∀ {s s′ o m} → submittedAt s h ≡ just m → m + Δ N.≤ clock s
                          → s -⟦ L⊗ (ϵ ᵗ¹) ↑ₒ QUERY h / o ⟧ᵛ⇀ s′
                          → answerOf o ≢ just InProgress
  bounded-InProgress-step {h} {s} eq le d ans =
    bounded-InProgress s h eq le (just-injective (trans (sym (query-answer d)) ans))

  ----------------------------------------------------------------------------
  -- Valid answers are stable

  private
    statusAt-tick : ∀ c me → statusAt c me ≡ Valid → statusAt (suc c) me ≡ Valid
    statusAt-tick c (just e) eq with done e | since e + Δ N.≤ᵇ c in le
    ... | true  | _     = eq
    ... | false | true  rewrite T⇒≡ (N.≤⇒≤ᵇ (N.m≤n⇒m≤1+n (N.≤ᵇ⇒≤ (since e + Δ) c (subst T (sym le) tt)))) = eq
    ... | false | false = case eq of λ ()

    -- A completed validation stays completed when reported.
    statusAt-done : ∀ c e → statusAt c (just e) ≡ Valid
                  → statusAt c (just (record e { done = true })) ≡ Valid
    statusAt-done c e eq with completed c e
    ... | true  = eq
    ... | false = case eq of λ ()

    Valid⇒known : ∀ c me → statusAt c me ≡ Valid → me ≢ nothing
    Valid⇒known c nothing  ()
    Valid⇒known c (just _) _ ()

    status-submit : ∀ s eb → lookupᵛ h (subs s) ≢ nothing
                  → status (submit s eb) h ≡ status s h
    status-submit {h} s eb ne with lookupᵛ (ref eb) (subs s) in eq
    ... | just _  = refl
    ... | nothing with h ≟ ref eb
    ...   | yes refl = ⊥-elim (ne eq)
    ...   | no  _    = refl

    status-finish : ∀ s h′ → status s h ≡ Valid → status (finish s h′) h ≡ Valid
    status-finish {h} s h′ eq with lookupᵛ h′ (subs s) in eq′
    ... | nothing = eq
    ... | just e with h ≟ h′
    ...   | no  _    = eq
    ...   | yes refl rewrite eq′ = statusAt-done (clock s) e eq

  -- Once a query answers 'Valid', every later query does: recording the
  -- answer, as a protocol does that keeps the validated EBs, is sound.
  Valid-stable : ∀ {s i o s′} → status s h ≡ Valid → s -⟦ i / o ⟧ᵛ⇀ s′ → status s′ h ≡ Valid
  Valid-stable {h} {s} eq (Submit {x = eb}) =
    trans (status-submit s eb (Valid⇒known (clock s) (lookupᵛ h (subs s)) eq)) eq
  Valid-stable eq Query = eq
  Valid-stable {h} {s} eq Tick = statusAt-tick (clock s) (lookupᵛ h (subs s)) eq
  Valid-stable {h} {s} eq (Done {h = h′}) = status-finish s h′ eq

  ----------------------------------------------------------------------------
  -- The trace checker

  -- The machine is deterministic, so a hint picks no step: it is what the
  -- log implies of the step.  A query is checked against the answer the log
  -- implies, e.g. 'Valid' for an EB the node voted on; the other steps,
  -- submissions included, are 'nothing'.
  ValHint : Type
  ValHint = Maybe ValidationResult

  opaque
    unfolding _⊗₀_

    hintAt : ValState → MT.Input ValM → ValHint
    hintAt s (inj₁ TICK)       = nothing
    hintAt s (inj₁ (DONE _))   = nothing
    hintAt s (inj₂ (SUBMIT _)) = nothing
    hintAt s (inj₂ (QUERY h))  = just (status s h)

    -- Every input steps, in one way only.
    val-step : ∀ s i → Step ValM s i
    val-step s (inj₁ TICK)       = step nothing _ Tick
    val-step s (inj₁ (DONE _))   = step nothing _ Done
    val-step s (inj₂ (SUBMIT _)) = step (just (inj₂ _)) _ Submit
    val-step s (inj₂ (QUERY _))  = step (just (inj₂ _)) _ Query

    -- The reference a query asks about.
    queried : MT.Input ValM → Maybe Ref
    queried (inj₂ (QUERY h)) = just h
    queried _                = nothing

    -- The inputs, from the environment and from the protocol.
    obsInput : ValObsF In → MT.Input ValM
    obsInput = inj₁

    reqInput : ValIOF Out → MT.Input ValM
    reqInput = inj₂

  valᶜ : Checker ValM
  valᶜ = record
    { Hint      = ValHint
    ; hintOf    = λ {s} {i} _ → hintAt s i
    ; Err       = λ h i s → hintAt s i ≢ h
    ; checkStep = λ h i s → case hintAt s i ≟ h of λ where
        (yes eq) → inj₂ (val-step s i , eq)
        (no neq) → inj₁ neq
    }

  -- An error refutes the step, since the hint of a step is fixed by its
  -- state and input.
  valᶜ-refute : ∀ {h i s} → Checkable.Err valᶜ h i s → ¬ Checkable.StepWith valᶜ h s i
  valᶜ-refute neq (_ , eq) = neq eq
