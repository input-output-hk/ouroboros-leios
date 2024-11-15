{-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract
open import Leios.VRF

module Leios.KeyRegistration (a : LeiosAbstract) (open LeiosAbstract a)
  (vrf : LeiosVRF a) (let open LeiosVRF vrf) where

record KeyRegistrationAbstract : Type₁ where

  data Input : Type₁ where
    INIT : PubKey → PubKey → PubKey → Input

  data Output : Type where
    PUBKEYS : List PubKey → Output

  record Functionality : Type₁ where
    field State : Type
          _⇀⟦_⟧_ : State → Input → State × Output → Type

    open Input public
    open Output public
