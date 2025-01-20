## Short-Pipeline Leios
<!--
```agda
{-# OPTIONS --safe #-}
```
-->
```agda
open import Leios.Prelude hiding (id)
open import Leios.FFD
open import Leios.SpecStructure
open import Data.Fin.Patterns
```
Uniform Short Pipeline:

1. If elected, propose IB
2. Wait
3. Wait
4. If elected, propose EB
5. If elected, vote
   If elected, propose RB
```agda
module Leios.Short (⋯ : SpecStructure 1)
  (let open SpecStructure ⋯ renaming (isVoteCertified to isVoteCertified')) where
```
```agda
data SlotUpkeep : Type where
  Base IB-Role EB-Role V-Role : SlotUpkeep

allUpkeep : ℙ SlotUpkeep
allUpkeep = (((∅ ∪ ❴ IB-Role ❵) ∪ ❴ EB-Role ❵) ∪ ❴ V-Role ❵) ∪ ❴ Base ❵
```
```agda
open import Leios.Protocol (⋯) SlotUpkeep public
open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open FFD hiding (_-⟦_/_⟧⇀_)
open GenFFD

isVoteCertified : LeiosState → EndorserBlock → Type
isVoteCertified s eb = isVoteCertified' (LeiosState.votingState s) (0F , eb)
```
```agda
module Protocol where

  private variable s s'   : LeiosState
                   ffds'  : FFD.State
                   π      : VrfPf
                   bs'    : B.State
                   ks ks' : K.State
                   msgs   : List (FFDAbstract.Header ffdAbstract ⊎ FFDAbstract.Body ffdAbstract)
                   eb     : EndorserBlock
                   rbs    : List RankingBlock
                   txs    : List Tx
                   V      : VTy
                   SD     : StakeDistr
                   pks    : List PubKey
```
```agda
  data _↝_ : LeiosState → LeiosState → Type where
```
#### Block/Vote production rules
```agda
    IB-Role : let open LeiosState s renaming (FFDState to ffds)
                  b = ibBody (record { txs = ToPropose })
                  h = ibHeader (mkIBHeader slot id π sk-IB ToPropose)
            in
            ∙ needsUpkeep IB-Role
            ∙ canProduceIB slot sk-IB (stake s) π
            ∙ ffds FFD.-⟦ Send h (just b) / SendRes ⟧⇀ ffds'
            ─────────────────────────────────────────────────────────────────────────
            s ↝ addUpkeep record s { FFDState = ffds' } IB-Role
```
```agda
    EB-Role : let open LeiosState s renaming (FFDState to ffds)
                  LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
                  h = mkEB slot id π sk-EB LI []
            in
            ∙ needsUpkeep EB-Role
            ∙ canProduceEB slot sk-EB (stake s) π
            ∙ ffds FFD.-⟦ Send (ebHeader h) nothing / SendRes ⟧⇀ ffds'
            ─────────────────────────────────────────────────────────────────────────
            s ↝ addUpkeep record s { FFDState = ffds' } EB-Role
```
```agda
    V-Role  : let open LeiosState s renaming (FFDState to ffds)
                  EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
                  votes = map (vote sk-V ∘ hash) EBs'
            in
            ∙ needsUpkeep V-Role
            ∙ canProduceV slot sk-V (stake s)
            ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
            ─────────────────────────────────────────────────────────────────────────
            s ↝ addUpkeep record s { FFDState = ffds' } V-Role
```
#### Negative Block/Vote production rules
```agda
    No-IB-Role : let open LeiosState s in
               ∙ needsUpkeep IB-Role
               ∙ ¬ canProduceIB slot sk-IB (stake s) π
               ─────────────────────────────────────────────
               s ↝ addUpkeep s IB-Role
```
```agda
    No-EB-Role : let open LeiosState s in
               ∙ needsUpkeep EB-Role
               ∙ ¬ canProduceEB slot sk-EB (stake s) π
               ─────────────────────────────────────────────
               s ↝ addUpkeep s EB-Role
```
```agda
    No-V-Role  : let open LeiosState s in
               ∙ needsUpkeep V-Role
               ∙ ¬ canProduceV slot sk-V (stake s)
               ─────────────────────────────────────────────
               s ↝ addUpkeep s V-Role
```
### Uniform short-pipeline
```agda
  data _-⟦_/_⟧⇀_ : Maybe LeiosState → LeiosInput → LeiosOutput → LeiosState → Type where
```
#### Initialization
```agda
    Init :
         ∙ ks K.-⟦ K.INIT pk-IB pk-EB pk-V / K.PUBKEYS pks ⟧⇀ ks'
         ∙ initBaseState B.-⟦ B.INIT (V-chkCerts pks) / B.STAKE SD ⟧⇀ bs'
         ────────────────────────────────────────────────────────────────
         nothing -⟦ INIT V / EMPTY ⟧⇀ initLeiosState V SD bs'
```
#### Network and Ledger
```agda
    Slot : let open LeiosState s renaming (FFDState to ffds; BaseState to bs) in
         ∙ Upkeep ≡ᵉ allUpkeep
         ∙ bs B.-⟦ B.FTCH-LDG / B.BASE-LDG rbs ⟧⇀ bs'
         ∙ ffds FFD.-⟦ Fetch / FetchRes msgs ⟧⇀ ffds'
         ───────────────────────────────────────────────────────────────────────
         just s -⟦ SLOT / EMPTY ⟧⇀ record s
             { FFDState  = ffds'
             ; BaseState = bs'
             ; Ledger    = constructLedger rbs
             ; slot      = suc slot
             ; Upkeep    = ∅
             } ↑ L.filter isValid? msgs
```
```agda
    Ftch :
         ────────────────────────────────────────────────────────
         just s -⟦ FTCH-LDG / FTCH-LDG (LeiosState.Ledger s) ⟧⇀ s
```
#### Base chain

Note: Submitted data to the base chain is only taken into account
      if the party submitting is the block producer on the base chain
      for the given slot
```agda
    Base₁   :
            ───────────────────────────────────────────────────────────────────
            just s -⟦ SUBMIT (inj₂ txs) / EMPTY ⟧⇀ record s { ToPropose = txs }
```
```agda
    Base₂a  : let open LeiosState s renaming (BaseState to bs) in
            ∙ needsUpkeep Base
            ∙ eb ∈ filter (λ eb → isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs
            ∙ bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ bs'
            ───────────────────────────────────────────────────────────────────────
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { BaseState = bs' } Base

    Base₂b  : let open LeiosState s renaming (BaseState to bs) in
            ∙ needsUpkeep Base
            ∙ [] ≡ filter (λ eb → isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs
            ∙ bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ bs'
            ───────────────────────────────────────────────────────────────────────
            just s -⟦ SLOT / EMPTY ⟧⇀ addUpkeep record s { BaseState = bs' } Base
```
#### Protocol rules
```agda
    Roles :
          ∙ s ↝ s'
          ─────────────────────────────
          just s -⟦ SLOT / EMPTY ⟧⇀ s'
```
