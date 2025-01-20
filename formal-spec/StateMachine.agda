{-# OPTIONS --safe #-}

module StateMachine where

open import Agda.Primitive using () renaming (Set to Type)

open import Prelude.Init hiding (map)
open import Prelude.InferenceRules

open import Class.Bifunctor

private
  variable S I O : Type
           s s' s'' : S
           i : I
           is : List I
           o : O
           os : List O
           STS : S → I → O → S → Type

module _ (_-⟦_/_⟧⇀_ : S → I → O → S → Type) where
  data _-⟦_/_⟧*⇀_ : S → List I → List O → S → Type where

    BS-base :
        ─────────────────
        s -⟦ [] / [] ⟧*⇀ s

    BS-ind :
      ∙ s  -⟦ i      / o      ⟧⇀  s'
      ∙ s' -⟦ is     / os     ⟧*⇀ s''
        ───────────────────────────────────────
        s  -⟦ i ∷ is / o ∷ os ⟧*⇀ s''

ReflexiveTransitiveClosure = _-⟦_/_⟧*⇀_

data IdSTS {S} : S → ⊤ → ⊤ → S → Type where
  Id-nop : IdSTS s _ _ s

Invariant : (S → I → O → S → Type) → (S → Type) → Type
Invariant _-⟦_/_⟧⇀_ P = ∀ {s i o s'} → s -⟦ i / o ⟧⇀ s' → P s → P s'

Total : (S → I → O → S → Type) → Type
Total _-⟦_/_⟧⇀_ = ∀ {s i} → ∃₂[ o , s' ] s -⟦ i / o ⟧⇀ s'

STS⇒RTC : STS s i o s' → ReflexiveTransitiveClosure STS s (i ∷ []) (o ∷ []) s'
STS⇒RTC sts = BS-ind sts BS-base

RTC-preserves-inv : ∀ {P} → Invariant STS P → Invariant (ReflexiveTransitiveClosure STS) P
RTC-preserves-inv inv (BS-base)      = id
RTC-preserves-inv inv (BS-ind p₁ p₂) = RTC-preserves-inv inv p₂ ∘ inv p₁

RTC-total : Total STS → Total (ReflexiveTransitiveClosure STS)
RTC-total SS-total {s} {[]}     = ([] , s , BS-base)
RTC-total SS-total {s} {i ∷ is} = case SS-total of λ where
  (o , s' , H) → case RTC-total SS-total of λ where
    (os , s'' , H') → (o ∷ os , s'' , BS-ind H H')
