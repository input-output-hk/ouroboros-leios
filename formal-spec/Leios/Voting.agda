{-# OPTIONS --safe #-}

open import Leios.Prelude

module Leios.Voting where

record VotingAbstract (X : Type) : Type₁ where
  field VotingState     : Type
        initVotingState : VotingState
        isVoteCertified : VotingState → X → Type

        ⦃ isVoteCertified⁇ ⦄ : ∀ {vs x} → isVoteCertified vs x ⁇
