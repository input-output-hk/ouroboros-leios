{-# OPTIONS --safe #-}

module Leios.FFD where

open import Leios.Prelude

record FFDAbstract : Type₁ where
  field Header Body ID : Type
        match : Header → Body → Type
        msgID : Header → ID

  data Input : Type where
    Send  : Header → Maybe Body → Input
    Fetch : Input

  data Output : Type where
    SendRes  : Output
    FetchRes : List (Header ⊎ Body) → Output

  record Functionality : Type₁ where
    field State : Type
          initFFDState : State
          _-⟦_/_⟧⇀_ : State → Input → Output → State → Type

    open Input public
    open Output public
