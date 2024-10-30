{-# OPTIONS --erasure #-}

module Leios.FFD where

open import Leios.Prelude
open import Leios.Abstract

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
          stepRel : Input → State → State × Output → Type
