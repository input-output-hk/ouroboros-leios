{-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract
open import Leios.VRF

module Leios.Base (a : LeiosAbstract) (open LeiosAbstract a) (vrf' : LeiosVRF a)
  (let open LeiosVRF vrf') where

open import Leios.Blocks a using (EndorserBlock)

StakeDistr : Type
StakeDistr = PoolID ⇀ ℕ

RankingBlock : Type
RankingBlock = These EndorserBlock (List Tx)

record BaseAbstract : Type₁ where
  field Cert : Type
        VTy : Type
        initSlot : VTy → ℕ
        V-chkCerts : List PubKey → EndorserBlock × Cert → Type

  data Input : Type₁ where
    INIT   : (EndorserBlock × Cert → Type) → Input
    SUBMIT : RankingBlock → Input
    FTCH-LDG : Input

  data Output : Type where
    STAKE : StakeDistr → Output
    EMPTY : Output
    BASE-LDG : List RankingBlock → Output

  record Functionality : Type₁ where
    field State : Type
          _-⟦_/_⟧⇀_ : State → Input → Output → State → Type

    open Input public
    open Output public
