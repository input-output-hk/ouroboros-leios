module CategoricalCrypto where

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec)

--------------------------------------------------------------------------------
-- Channels, which form the objects

record Channel : Set₁ where
  field P : Set
        rcvType sndType : P → Set

infixr 9 _⊗_

I : Channel
I .Channel.P = ⊥

_ᵀ : Channel → Channel
_ᵀ c = let open Channel c in λ where .P → P ; .rcvType → sndType ; .sndType → rcvType

_⊗_ : Channel → Channel → Channel
c₁ ⊗ c₂ = let open Channel c₁ renaming (P to P₁; rcvType to rcvType₁; sndType to sndType₁)
              open Channel c₂ renaming (P to P₂; rcvType to rcvType₂; sndType to sndType₂)
              open Channel
  in λ where
    .P → P₁ ⊎ P₂
    .rcvType (inj₁ a) → rcvType₁ a
    .rcvType (inj₂ b) → rcvType₂ b
    .sndType (inj₁ a) → sndType₁ a
    .sndType (inj₂ b) → sndType₂ b

snd₁ : ∀ {A B} → ∃ (Channel.sndType A) → ∃ (Channel.sndType (A ⊗ B))
snd₁ (p , m) = inj₁ p , m

snd₂ : ∀ {A B} → ∃ (Channel.sndType B) → ∃ (Channel.sndType (A ⊗ B))
snd₂ (p , m) = inj₂ p , m

-- being lazy here, this should be an iso instead
postulate
  ⊗-assoc : ∀ {A B C} → (A ⊗ B) ⊗ C ≡ A ⊗ (B ⊗ C)

--------------------------------------------------------------------------------
-- Machines, which form the morphisms

record Machine (A B : Channel) : Set₁ where
  constructor MkMachine
  open Channel (A ⊗ B ᵀ) public

  field State : Set
        stepRel : ∃ rcvType → State → State × Maybe (∃ sndType) → Set

module _ {A B} (let open Channel (A ⊗ B ᵀ)) where
  MkMachine' : ∀ {State} → (∃ rcvType → State → State × Maybe (∃ sndType) → Set) → Machine A B
  MkMachine' = MkMachine _

  StatelessMachine : (∃ rcvType → Maybe (∃ sndType) → Set) → Machine A B
  StatelessMachine R = MkMachine ⊤ (λ i _ (_ , o) → R i o)

  FunctionMachine : (∃ rcvType → Maybe (∃ sndType)) → Machine A B
  FunctionMachine f = StatelessMachine (λ i o → f i ≡ o)

id : ∀ {A} → Machine A A
id .Machine.State   = ⊤
id .Machine.stepRel (inj₁ a , m) _ (_ , m') = m' ≡ just (inj₂ a , m)
id .Machine.stepRel (inj₂ a , m) _ (_ , m') = m' ≡ just (inj₁ a , m)

module Tensor {A B C D} (M₁ : Machine A B) (M₂ : Machine C D) where
  open Machine M₁ renaming (State to State₁; stepRel to stepRel₁)
  open Machine M₂ renaming (State to State₂; stepRel to stepRel₂)

  State = State₁ × State₂

  AllCs = (A ⊗ B ᵀ) ⊗ (C ⊗ D ᵀ)

  data CompRel : ∃ (Channel.rcvType AllCs) → State → State × Maybe (∃ (Channel.sndType AllCs)) → Set where
    Step₁ : ∀ {p m m' s s' s₂} → stepRel₁ (p , m) s (s' , m')
          → CompRel (inj₁ p , m) (s , s₂) ((s' , s₂) , (snd₁ <$> m'))

    Step₂ : ∀ {p m m' s s' s₁} → stepRel₂ (p , m) s (s' , m')
          → CompRel (inj₂ p , m) (s₁ , s) ((s₁ , s') , (snd₂ <$> m'))


  _⊗'_ : Machine (A ⊗ C) (B ⊗ D)
  _⊗'_ = λ where
    .Machine.State → State
    .Machine.stepRel m s (s' , m') → CompRel
      (case m of λ where
        (inj₁ (inj₁ p) , m) → (inj₁ (inj₁ p) , m)
        (inj₁ (inj₂ p) , m) → (inj₂ (inj₁ p) , m)
        (inj₂ (inj₁ p) , m) → (inj₁ (inj₂ p) , m)
        (inj₂ (inj₂ p) , m) → (inj₂ (inj₂ p) , m))
      s
      (s' , ((λ where
        (inj₁ (inj₁ p) , m) → (inj₁ (inj₁ p) , m)
        (inj₁ (inj₂ p) , m) → (inj₂ (inj₁ p) , m)
        (inj₂ (inj₁ p) , m) → (inj₁ (inj₂ p) , m)
        (inj₂ (inj₂ p) , m) → (inj₂ (inj₂ p) , m)) <$> m'))

open Tensor using (_⊗'_) public

_⊗ˡ_ : ∀ {A B} → (C : Channel) → Machine A B → Machine (C ⊗ A) (C ⊗ B)
C ⊗ˡ M = id ⊗' M

_⊗ʳ_ : ∀ {A B} → Machine A B → (C : Channel) → Machine (A ⊗ C) (B ⊗ C)
M ⊗ʳ C = M ⊗' id

module Comp {A B C} (M₁ : Machine B C) (M₂ : Machine A B) where
  open Machine M₁ renaming (State to State₁; stepRel to stepRel₁)
  open Machine M₂ renaming (State to State₂; stepRel to stepRel₂)

  State = State₁ × State₂

  AllCs = (A ⊗ B ᵀ) ⊗ (B ⊗ C ᵀ)

  data CompRel : ∃ (Channel.rcvType AllCs) → State → State × Maybe (∃ (Channel.sndType AllCs)) → Set where
    Step₁ : ∀ {p m m' s s' s₂} → stepRel₁ (p , m) s (s' , m')
          → CompRel (inj₂ p , m) (s , s₂) ((s' , s₂) , (snd₂ <$> m'))

    Step₂ : ∀ {p m m' s s' s₁} → stepRel₂ (p , m) s (s' , m')
          → CompRel (inj₁ p , m) (s₁ , s) ((s₁ , s') , (snd₁ <$> m'))

    Multi₁ : ∀ {p m m' m'' s s' s''}
           → CompRel m s (s' , just ((inj₂ (inj₁ p) , m')))
           → CompRel (inj₁ (inj₂ p) , m') s' (s'' , m'')
           → CompRel m s (s'' , m'')

    Multi₂ : ∀ {p m m' m'' s s' s''}
           → CompRel m s (s' , just (inj₁ (inj₂ p) , m'))
           → CompRel (inj₂ (inj₁ p) , m') s' (s'' , m'')
           → CompRel m s (s'' , m'')

  infixr 9 _∘_

  _∘_ : Machine A C
  _∘_ = λ where
    .Machine.State → State
    .Machine.stepRel m s (s' , m') →
      CompRel
        (case m of λ where (inj₁ x , m) → inj₁ (inj₁ x) , m ; (inj₂ y , m) → inj₂ (inj₂ y) , m)
        s (s' ,  ((λ where (inj₁ x , m) → inj₁ (inj₁ x) , m ; (inj₂ y , m) → inj₂ (inj₂ y) , m) <$> m'))

open Comp using (_∘_) public

--------------------------------------------------------------------------------
-- Environment model

ℰ-Out : Channel
ℰ-Out .Channel.P = ⊤
ℰ-Out .Channel.sndType _ = Bool
ℰ-Out .Channel.rcvType _ = ⊥

-- Presheaf on the category of channels & machines
-- we just take machines that output a boolean
-- for now, not on the Kleisli construction
ℰ : Channel → Set₁
ℰ C = Machine C ℰ-Out

map-ℰ : ∀ {A B} → Machine A B → ℰ B → ℰ A
map-ℰ M E = E ∘ M

--------------------------------------------------------------------------------
-- UC relations

-- perfect equivalence
_≈ℰ_ : ∀ {A B} → Machine A B → Machine A B → Set₁
_≈ℰ_ {B = B} M M' = (E : ℰ B) → map-ℰ M E ≡ map-ℰ M' E

_≤UC_ : ∀ {A B E E''} → Machine A (B ⊗ E) → Machine A (B ⊗ E'') → Set₁
_≤UC_ {B = B} {E} R I = ∀ E' (A : Machine E E') → ∃[ S ] ((B ⊗ˡ A) ∘ R) ≈ℰ ((B ⊗ˡ S) ∘ I)

-- equivalent to _≤UC_ by "completeness of the dummy adversary"
_≤'UC_ : ∀ {A B E} → Machine A (B ⊗ E) → Machine A (B ⊗ E) → Set₁
_≤'UC_ {B = B} R I = ∃[ S ] R ≈ℰ (B ⊗ˡ S ∘ I)


--------------------------------------------------------------------------------
-- Example functionalities

module LeakyChannel (M : Set) where
  -- authenticated, non-lossy, leaks all messages

  open Channel

  A B E : Channel

  -- can receive messages from Alice (in reverse)
  A .P = ⊤
  A .sndType _ = M
  A .rcvType _ = ⊥

  -- can send messages to Bob (in reverse)
  B .P = ⊤
  B .sndType _ = ⊥
  B .rcvType _ = M

  -- upon request, can send next message to Eve (in reverse)
  E .P = ⊤
  E .sndType _ = ⊤
  E .rcvType _ = M

  open Machine hiding (rcvType; sndType)

  data R : ∃ (rcvType (I ⊗ (A ⊗ B ⊗ E) ᵀ))
         → List M
         → List M × Maybe (∃ (sndType (I ⊗ (A ⊗ B ⊗ E) ᵀ))) → Set where

    Send : ∀ {m s} → R (inj₂ (inj₁ _) , m) s (s ∷ʳ m , just (inj₂ (inj₂ (inj₁ _)) , m))
    Req  : ∀ {m s} → R (inj₂ (inj₂ (inj₂ _)) , _) (m ∷ s) (s , just (inj₂ (inj₂ (inj₂ _)) , m))

  Functionality : Machine I (A ⊗ B ⊗ E)
  Functionality .State = List M -- queue of messages
  Functionality .stepRel = R



module SecureChannel (M : Set) where
  -- authenticated, non-lossy, leaks only message length

  open Channel

  A B E : Channel

  -- can receive messages from Alice (in reverse)
  A .P = ⊤
  A .sndType _ = M
  A .rcvType _ = ⊥

  -- can send messages to Bob (in reverse)
  B .P = ⊤
  B .sndType _ = ⊥
  B .rcvType _ = M

  -- upon request, can send length of the next message to Eve (in reverse)
  E .P = ⊤
  E .sndType _ = ⊤
  E .rcvType _ = ℕ

  module _ (msgLen : M → ℕ) where

    open Machine hiding (rcvType; sndType)

    data R : ∃ (rcvType (I ⊗ (A ⊗ B ⊗ E) ᵀ))
           → List M
           → List M × Maybe (∃ (sndType (I ⊗ (A ⊗ B ⊗ E) ᵀ))) → Set where
      Send : ∀ {m s} → R (inj₂ (inj₁ _) , m) s (s ∷ʳ m , just (inj₂ (inj₂ (inj₁ _)) , m))
      Req  : ∀ {m s} → R (inj₂ (inj₂ (inj₂ _)) , _) (m ∷ s) (s , just (inj₂ (inj₂ (inj₂ _)) , msgLen m))

    Functionality : Machine I (A ⊗ B ⊗ E)
    Functionality .State = List M -- queue of messages
    Functionality .stepRel = R

    Functionality' : Machine I ((A ⊗ B) ⊗ E)
    Functionality' = subst (Machine I) (sym ⊗-assoc) Functionality



module Encryption (PlainText CipherText PubKey PrivKey : Set)
                  ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                  (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey) where
  open Channel
  open Machine hiding (rcvType; sndType)

  C : Channel
  C .P = ⊤
  C .sndType _ = PlainText × PubKey ⊎ CipherText × PrivKey
  C .rcvType _ = CipherText ⊎ Maybe PlainText

  S : Set
  S = List (PubKey × PlainText × CipherText)

  lookup : {A : Set} → List A → (A → Bool) → Maybe A
  lookup [] f = nothing
  lookup (x ∷ l) f with f x
  ... | true  = just x
  ... | false = lookup l f

  lookupPlainText : S → CipherText × PubKey → Maybe PlainText
  lookupPlainText s (c , k) = proj₁ <$> (proj₂ <$> lookup s λ where (k' , _ , c') → ¿ k ≡ k' × c ≡ c' ¿ᵇ)

  data R : ∃ (rcvType (I ⊗ (C ᵀ))) → S → S × Maybe (∃ (sndType (I ⊗ (C ᵀ)))) → Set where
    Enc : ∀ {p k s} → let c = genCT (length s)
       in R (inj₂ tt , inj₁ (p , k)) s ((k , p , c) ∷ s , just (inj₂ tt , inj₁ c))
    Dec : ∀ {c k s} → let p = lookupPlainText s (c , getPubKey k)
       in R (inj₂ tt , inj₂ (c , k)) s (s , just (inj₂ tt , inj₂ p))

  Functionality : Machine I C
  Functionality .State   = S
  Functionality .stepRel = R

module EncryptionShim (PlainText CipherText PubKey PrivKey : Set)
                      ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                      (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey)
                      (pubKey : PubKey) (privKey : PrivKey) where
  open Channel
  open Machine hiding (rcvType; sndType)

  module L = LeakyChannel CipherText
  module S = SecureChannel PlainText
  module E = Encryption PlainText CipherText PubKey PrivKey genCT getPubKey

  data R : ∃ (rcvType ((L.A ⊗ L.B ⊗ L.E) ⊗ ((S.A ⊗ S.B ⊗ S.E) ᵀ)))
         → E.Functionality .State
         → E.Functionality .State × Maybe (∃ (sndType ((L.A ⊗ L.B ⊗ L.E) ⊗ ((S.A ⊗ S.B ⊗ S.E) ᵀ))))
         → Set where
    EncSend : ∀ {m m' s s'}
            → E.R (inj₂ _ , inj₁ (m , pubKey)) s (s' , just (inj₂ _ , inj₁ m'))
            → R (inj₂ (inj₁ _) , m) s (s' , just (inj₁ (inj₁ _) , m'))
    DecRcv  : ∀ {m m' s s'}
            → E.R (inj₂ _ , inj₂ (m , privKey)) s (s' , just (inj₂ _ , inj₂ (just m')))
            → R (inj₁ (inj₂ (inj₁ _)) , m) s (s' , just (inj₂ (inj₂ (inj₁ _)) , m'))

  Functionality : Machine (L.A ⊗ L.B ⊗ L.E) (S.A ⊗ S.B ⊗ S.E)
  Functionality .State   = E.Functionality .State
  Functionality .stepRel = R

module SecureFromAuthenticated (PlainText CipherText PubKey PrivKey : Set)
                               ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                               (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey)
                               (pubKey : PubKey) (privKey : PrivKey)
                               (msgLength : PlainText → ℕ) where

  module L  = LeakyChannel CipherText
  module S  = SecureChannel PlainText
  module SH = EncryptionShim PlainText CipherText PubKey PrivKey genCT getPubKey pubKey privKey

  Functionality : Machine I (S.A ⊗ S.B ⊗ S.E)
  Functionality = SH.Functionality ∘ L.Functionality

  Functionality' : Machine I ((S.A ⊗ S.B) ⊗ S.E)
  Functionality' = subst (Machine I) (sym ⊗-assoc) Functionality

  -- F≤Secure : Functionality' ≤'UC S.Functionality' msgLength
  -- F≤Secure = {!!}
