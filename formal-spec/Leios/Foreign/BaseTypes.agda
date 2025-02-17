module Leios.Foreign.BaseTypes where

-- TODO: copied from the formal-ledger project for now
-- Added: * TotalMap

open import Data.Rational

open import Leios.Prelude

open import Data.Fin
open import Function.Related.TypeIsomorphisms
open import Relation.Binary.Structures

open import Tactic.Derive.Convertible
open import Tactic.Derive.HsType

open import Class.Convertible
open import Class.Decidable.Instances
open import Class.HasHsType

open import Leios.Foreign.HsTypes as F
open import Leios.Foreign.Util
open import Foreign.Haskell

instance
  iConvTop    = Convertible-Refl {⊤}
  iConvNat    = Convertible-Refl {ℕ}
  iConvString = Convertible-Refl {String}
  iConvBool   = Convertible-Refl {Bool}

instance

  -- * Unit and empty

  HsTy-⊥ = MkHsType ⊥ F.Empty
  Conv-⊥ = autoConvert ⊥

  HsTy-⊤ = MkHsType ⊤ ⊤

  -- * Rational numbers

  HsTy-Rational = MkHsType ℚ F.Rational
  Conv-Rational : HsConvertible ℚ
  Conv-Rational = λ where
    .to (mkℚ n d _)       → n F., suc d
    .from (n F., zero)    → 0ℚ -- TODO is there a safer way to do this?
    .from (n F., (suc d)) → n Data.Rational./ suc d

  -- * Maps and Sets

  HsTy-HSSet : ∀ {A} → ⦃ HasHsType A ⦄ → HasHsType (ℙ A)
  HsTy-HSSet {A} = MkHsType _ (F.HSSet (HsType A))

  Conv-HSSet : ∀ {A} ⦃ _ : HasHsType A ⦄
             → ⦃ HsConvertible A ⦄
             → HsConvertible (ℙ A)
  Conv-HSSet = λ where
    .to   → F.MkHSSet ∘ to ∘ setToList
    .from → fromList ∘ from ∘ F.HSSet.elems

  Convertible-FinSet : Convertible₁ ℙ_ List
  Convertible-FinSet = λ where
    .to   → map to   ∘ setToList
    .from → fromList ∘ map from

  Convertible-Map : ∀ {K K' V V'} → ⦃ DecEq K ⦄
    → ⦃ Convertible K K' ⦄ → ⦃ Convertible V V' ⦄
    → Convertible (K ⇀ V) (List $ Pair K' V')
  Convertible-Map = λ where
    .to   → to        ∘ proj₁
    .from → fromListᵐ ∘ map from

  HsTy-Map : ∀ {A B} → ⦃ HasHsType A ⦄ → ⦃ HasHsType B ⦄ → HasHsType (A ⇀ B)
  HsTy-Map {A} {B} = MkHsType _ (F.HSMap (HsType A) (HsType B))

  Conv-HSMap : ∀ {A B} ⦃ _ : HasHsType A ⦄ ⦃ _ : HasHsType B ⦄
    → ⦃ DecEq A ⦄
    → ⦃ HsConvertible A ⦄
    → ⦃ HsConvertible B ⦄
    → HsConvertible (A ⇀ B)
  Conv-HSMap = λ where
    .to   → F.MkHSMap ∘ to
    .from → from ∘ F.HSMap.assocList

record Listable (A : Type) : Type where
  field
    listing  : ℙ A
    complete : ∀ {a : A} → a ∈ listing

totalDec : ∀ {A B : Type} → ⦃ DecEq A ⦄ → ⦃ Listable A ⦄ → {R : Rel A B} → Dec (total R)
totalDec {A} {B} {R} with all? (_∈? dom R)
... | yes p = yes λ {a} → p {a} ((Listable.complete it) {a})
... | no ¬p = no λ x → ¬p λ {a} _ → x {a}

instance

  total? : ∀ {A B : Type} → ⦃ DecEq A ⦄ → ⦃ Listable A ⦄ → {R : Rel A B} → ({a : A} → a ∈ dom R) ⁇
  total? = ⁇ totalDec

  Convertible-TotalMap : ∀ {K K' V V'} → ⦃ DecEq K ⦄ → ⦃ Listable K ⦄
    → ⦃ Convertible K K' ⦄ → ⦃ Convertible V V' ⦄
    → Convertible (TotalMap K V) (List $ Pair K' V')
  Convertible-TotalMap {K} = λ where
    .to   → to ∘ TotalMap.rel
    .from → λ x →
      let (r , l) = fromListᵐ (map from x)
      in case (¿ total r ¿) of λ where
           (yes p) → record { rel = r ; left-unique-rel = l ; total-rel = p }
           (no p) → error "Expected total map"

  HsTy-TotalMap : ∀ {A B} → ⦃ HasHsType A ⦄ → ⦃ HasHsType B ⦄ → HasHsType (TotalMap A B)
  HsTy-TotalMap {A} {B} = MkHsType _ (F.HSMap (HsType A) (HsType B))

  Conv-HSTotalMap : ∀ {A B} ⦃ _ : HasHsType A ⦄ ⦃ _ : HasHsType B ⦄
    → ⦃ DecEq A ⦄
    → ⦃ Listable A ⦄
    → ⦃ HsConvertible A ⦄
    → ⦃ HsConvertible B ⦄
    → HsConvertible (TotalMap A B)
  Conv-HSTotalMap = λ where
    .to   → MkHSMap ∘ to
    .from → from ∘ F.HSMap.assocList

  -- * ComputationResult

  open import Class.Computational as C

  HsTy-ComputationResult : ∀ {l} {Err} {A : Type l}
                           → ⦃ HasHsType Err ⦄ → ⦃ HasHsType A ⦄
                           → HasHsType (C.ComputationResult Err A)
  HsTy-ComputationResult {Err = Err} {A} = MkHsType _ (F.ComputationResult (HsType Err) (HsType A))

  Conv-ComputationResult : ConvertibleType C.ComputationResult F.ComputationResult
  Conv-ComputationResult = autoConvertible
