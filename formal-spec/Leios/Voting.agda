{-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract

module Leios.Voting (a : LeiosAbstract) (open LeiosAbstract a) where

open import Leios.Blocks a using (EndorserBlock)

record VotingAbstract (b : Type) : Type₁ where
  field isVote1Certified : b → EndorserBlock → Type
        isVote2Certified : b → EndorserBlock → Type
