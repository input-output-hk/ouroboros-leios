-- Instantiates PraosAbstract with the actual Praos formal specification
-- (ouroboros-praos-formal-spec, library praos-spec), i.e. the honest-node
-- functions of Protocol.Semantics with Txs := RankingBlock.
--
-- NOT --safe: Protocol.Semantics transitively imports Protocol.Chain, whose
-- chainFromBlock is {-# TERMINATING #-}. Consequently this module is kept out
-- of formal-spec.lagda.md and checked separately (see Makefile).

open import Leios.Prelude hiding (_⊗_)
open import Leios.Abstract
open import Leios.VRF

open import Tactic.Defaults
open import Tactic.Derive.DecEq

import Protocol.Params as P
open import Protocol.Assumptions using (Assumptions)

module Leios.Base.Praos.Instance
  (a    : LeiosAbstract) (open LeiosAbstract a)
  (vrf' : LeiosVRF a   ) (open LeiosVRF vrf'  )
  ⦃ DecEq-EBCert : DecEq EBCert ⦄
  (numParties : ℕ)
  -- the leader schedule, to be derived from the Leios VRF
  (winner : Fin numParties → ℕ → Type)
  ⦃ winner⁇² : winner ⁇² ⦄
  where

open import Leios.Base a vrf' using (RankingBlock)
open import Leios.Base.Praos a vrf' using (PraosAbstract)

unquoteDecl DecEq-RankingBlock =
  derive-DecEq ((quote RankingBlock , DecEq-RankingBlock) ∷ [])

instance
  praosParams : P.Params
  praosParams = record
    { numParties = numParties
    ; Txs        = RankingBlock
    ; Hash       = Hash
    ; winner     = winner
    ; DecEq-Txs  = DecEq-RankingBlock
    ; DecEq-Hash = DecEq-Hash
    ; winnerᵈ    = winner⁇²
    }

-- The Assumptions record supplies the concrete block tree (Tree TreeImpl),
-- honesty assignment and corrupt behaviors; no concrete Tree implementation
-- with discharged laws exists upstream yet, so it stays a parameter.
module WithAssumptions
  ⦃ assumptions : Assumptions ⦄ (open Assumptions assumptions)
  (p : Fin numParties)
  where

  open import Protocol.Semantics ⦃ praosParams ⦄ ⦃ assumptions ⦄
  open import Protocol.Block   ⦃ praosParams ⦄
  open import Protocol.Message ⦃ praosParams ⦄ using (newBlock; projBlock)
  open import Protocol.Tree    ⦃ praosParams ⦄

  praosNode : PraosAbstract
  praosNode = record
    { Block       = Block
    ; DecEq-Block = DecEq-Block
    ; LocalState  = LocalState
    ; initState   = record { tree = tree₀ }
    ; processMsgs = λ bs → processMsgsʰ (L.map newBlock bs)
    ; makeBlock   = λ sl rb ls →
        let (msgs , ls′) = makeBlockʰ sl rb p ls
        in L.map projBlock msgs , ls′
    ; readChain   = λ sl ls → bestChain sl (ls .tree)
    ; payloadOf   = Block.txs
    }
