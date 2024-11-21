{-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract

module Leios.Voting (a : LeiosAbstract) (open LeiosAbstract a) where

open import Leios.Blocks a using (EndorserBlock)

record VotingAbstract : Type₁ where
  field VotingState : Type
        initVotingState : VotingState
        isVote1Certified : VotingState → EndorserBlock → Type
        isVote2Certified : VotingState → EndorserBlock → Type

        ⦃ isVote1Certified⁇ ⦄ : ∀ {vs eb} → isVote1Certified vs eb ⁇
        ⦃ isVote2Certified⁇ ⦄ : ∀ {vs eb} → isVote2Certified vs eb ⁇
