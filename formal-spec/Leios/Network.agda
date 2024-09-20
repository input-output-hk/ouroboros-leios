module Leios.Network where

open import Prelude hiding (_∘_; _⊗_)
open import Ledger.Prelude using (ℙ_; _∈_; _∪_; ❴_❵; _∉_)
open import CategoricalCrypto

record Abstract : Set₁ where
  field Header Body ID : Set
        match : Header → Body → Set
        msgID : Header → ID

module Broadcast (M Peer : Set) where
  open Channel

  C : Channel
  C .P = Peer
  C .rcvType _ = Peer × M
  C .sndType _ = M

  postulate Functionality : Machine I C

  Single : Channel
  Single .P = ⊤
  Single .rcvType _ = Peer × M
  Single .sndType _ = M

  postulate SingleFunctionality : Machine I Single

  -- connectWithBroadcast : ∀ {A} → (Peer → Machine Single A) → Machine I A
  -- connectWithBroadcast = {!!}

module HeaderDiffusion (a : Abstract) (Peer : Set) (self : Peer) where
  open Channel
  open Abstract a
  module B = Broadcast Header Peer

  data Port : Set where
    Send    : Port -- we want to send a header
    Forward : Port -- we want to forward a header

  C : Channel
  C .P = Port
  C .sndType _ = Header
  C .rcvType Forward = Header
  C .rcvType Send = ⊥

  data Input : Set where
    S : Header → Input
    F : Header → Input
    R : Peer → Header → Input

  data Output : Set where
    Verify : Header → Output

  private variable
    h : Header
    s : ℙ ID

  data Step : ∃ (rcvType (B.Single ⊗ C ᵀ)) → ℙ ID → ℙ ID × Maybe (∃ (sndType (B.Single ⊗ C ᵀ))) → Set where
    Init : Step (inj₂ Send , h) s (s ∪ ❴ msgID h ❵ , just (inj₁ _ , h))
    Receive1  : ∀ {p} → Step (inj₁ _ , p , h) s (s , just (inj₂ Forward , h))
    Receive2  : msgID h ∉ s → Step (inj₂ Forward , h) s (s ∪ ❴ msgID h ❵ , just (inj₁ _ , h))
    Receive2' : msgID h ∈ s → Step (inj₂ Forward , h) s (s , nothing)

  step : ∃ (rcvType (B.Single ⊗ C ᵀ)) → ∃ (sndType (B.Single ⊗ C ᵀ))
  step (inj₁ _   , _ , h) = (inj₂ Forward , h)
  step (inj₂ Forward , h) = (inj₁ _ , h)
  step (inj₂ Send    , h) = (inj₁ _ , h)

  Functionality : Machine I C
  Functionality = MkMachine' Step ∘ B.SingleFunctionality
