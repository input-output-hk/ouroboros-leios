module Leios.Abstract where

open import Leios.Prelude

record LeiosAbstract : Type₁ where
  field Tx : Type
        PoolID : Type
        BodyHash VrfPf PrivKey Sig Hash : Type -- these could have been byte strings, but this is safer
        ⦃ DecEq-Hash ⦄ : DecEq Hash
        Vote : Type
        vote : Hash → Vote
        sign : PrivKey → Hash → Sig
        ⦃ Hashable-Txs ⦄ : Hashable (List Tx) Hash
        L Λ μ : ℕ
        ⦃ NonZero-L ⦄ : NonZero L
