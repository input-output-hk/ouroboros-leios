open import Leios.Prelude hiding (id)

module Parser where

{-# FOREIGN GHC
  {-# LANGUAGE OverloadedStrings #-}
#-}

{-# FOREIGN GHC
  import Data.Word
  import Data.Fixed
  import Data.Map
  import qualified Data.ByteString.Lazy.Char8 as BSL8
  import LeiosEvents
#-}

postulate
  Int : Set
  Word64 : Set
  Micro : Set
  Map : Set → Set → Set

{-# COMPILE GHC Word64 = type Data.Word.Word64 #-}
{-# COMPILE GHC Micro = type Data.Fixed.Micro #-}
{-# COMPILE GHC Map = type Data.Map.Map #-}
{-# COMPILE GHC Int = type Int #-}

Bytes = Word64
SlotNo = Word64
Time = Micro

data NetworkAction : Type where
  Sent Received : NetworkAction

{-# COMPILE GHC NetworkAction = data NetworkAction (Sent | Received) #-}

data BlockKind : Type where
  IB EB VT RB : BlockKind

{-# COMPILE GHC BlockKind = data BlockKind (IB | EB | VT | RB) #-}

Node = String

record BlockRef : Type where
  field id : String

{-# COMPILE GHC BlockRef = data BlockRef (BlockRef) #-}

record Endorsement : Type where
  field eb : BlockRef

{-# COMPILE GHC Endorsement = data Endorsement (Endorsement) #-}

data Event : Type where
  Cpu : String → Time → String → Event
  IBSent EBSent VTBundleSent RBSent IBReceived EBReceived VTBundleReceived RBReceived : Maybe Node → Node → Maybe Bytes → Maybe Time → Maybe String → Maybe (List String) → Event
  IBEnteredState EBEnteredState VTBundleEnteredState RBEnteredState : String → String → Word64 → Event
  IBGenerated : String → String → SlotNo → Maybe Bytes → Maybe Bytes → Maybe String → Event
  EBGenerated : String → String → Word64 → Word64 → List BlockRef → Event
  RBGenerated : String → Maybe String → Maybe Int → Word64 → Maybe Word64 → Maybe Endorsement → Maybe (List Endorsement) → Maybe Word64 → Event
  VTBundleGenerated : String → String → Word64 → Word64 → Map String Word64 → Event

{-# COMPILE GHC Event = data Event (Cpu | IBSent | EBSent | VTBundleSent | RBSent | IBReceived | EBReceived | VTBundleReceived | RBReceived
  | IBEnteredState | EBEnteredState | VTBundleEnteredState | RBEnteredState | IBGenerated | EBGenerated | RBGenerated | VTBundleGenerated) #-}

record TraceEvent : Type where
  field time_s : Time
        message : Event

{-# COMPILE GHC TraceEvent = data TraceEvent (TraceEvent) #-}

open import Leios.SpecStructure using (SpecStructure)
open import Leios.Defaults 2 fzero using (st; sd; LeiosState; initLeiosState; isb; hpe; hhs; htx; SendIB; FFDState; Dec-SimpleFFD; send-total)
open import Leios.Trace.Verifier st
open SpecStructure st hiding (Hashable-IBHeader; Hashable-EndorserBlock)

open import Leios.Short st hiding (LeiosState; initLeiosState)
open import Prelude.Closures _↝_
open GenFFD

EventLog = List TraceEvent

data Action : Type where
  IB-Role-Action EB-Role-Action V-Role-Action : Action
  No-IB-Role-Action No-EB-Role-Action No-V-Role-Action : Action

traceEvent→action : TraceEvent → Maybe Action
traceEvent→action record { message = Cpu x x₁ x₂ } = nothing
traceEvent→action record { message = IBSent x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = EBSent x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = VTBundleSent x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = RBSent x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = IBReceived x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = EBReceived x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = VTBundleReceived x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = RBReceived x x₁ x₂ x₃ x₄ x₅ } = nothing
traceEvent→action record { message = IBEnteredState x x₁ x₂ } = nothing
traceEvent→action record { message = EBEnteredState x x₁ x₂ } = nothing
traceEvent→action record { message = VTBundleEnteredState x x₁ x₂ } = nothing
traceEvent→action record { message = RBEnteredState x x₁ x₂ } = nothing
traceEvent→action record { message = IBGenerated p _ s _ _ _ } = just IB-Role-Action
traceEvent→action record { message = EBGenerated p _ s _ ibs } = just EB-Role-Action
traceEvent→action record { message = RBGenerated x x₁ x₂ x₃ x₄ x₅ x₆ x₇ } = nothing
traceEvent→action record { message = VTBundleGenerated x x₁ x₂ x₃ x₄ } = just V-Role-Action

Actions = List Action

private variable
  s s′ : LeiosState
  α : Action

data ValidAction : Action → LeiosState → Type where

  IB-Role : let open LeiosState s renaming (FFDState to ffds)
                b = record { txs = ToPropose }
                h = mkIBHeader slot id tt sk-IB ToPropose
                ffds' = proj₁ (send-total {ffds} {ibHeader h} {just (ibBody b)})
            in .(needsUpkeep IB-Role) →
               .(canProduceIB slot sk-IB (stake s) tt) →
               .(ffds FFD.-⟦ FFD.Send (ibHeader h) (just (ibBody b)) / FFD.SendRes ⟧⇀ ffds') →
               ValidAction IB-Role-Action s

  EB-Role : let open LeiosState s renaming (FFDState to ffds)
                LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
                h = mkEB slot id tt sk-EB LI []
                ffds' = proj₁ (send-total {ffds} {ebHeader h} {nothing})
            in .(needsUpkeep EB-Role) →
               .(canProduceEB slot sk-EB (stake s) tt) →
               .(ffds FFD.-⟦ FFD.Send (ebHeader h) nothing / FFD.SendRes ⟧⇀ ffds') →
               ValidAction EB-Role-Action s

  V-Role  : let open LeiosState s renaming (FFDState to ffds)
                EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
                votes = map (vote sk-V ∘ hash) EBs'
                ffds' = proj₁ (send-total {ffds} {vHeader votes} {nothing})
            in .(needsUpkeep V-Role) →
               .(canProduceV slot sk-V (stake s)) →
               .(ffds FFD.-⟦ FFD.Send (vHeader votes) nothing / FFD.SendRes ⟧⇀ ffds') →
               ValidAction V-Role-Action s

  No-IB-Role : let open LeiosState s
               in needsUpkeep IB-Role →
                  (∀ π → ¬ canProduceIB slot sk-IB (stake s) π) →
                  ValidAction No-IB-Role-Action s

  No-EB-Role : let open LeiosState s
               in needsUpkeep EB-Role →
                  (∀ π → ¬ canProduceEB slot sk-EB (stake s) π) →
                  ValidAction No-EB-Role-Action s

  No-V-Role : let open LeiosState s
              in needsUpkeep V-Role →
                 (¬ canProduceV slot sk-V (stake s)) →
                 ValidAction No-V-Role-Action s

⟦_⟧ : ValidAction α s → LeiosState
⟦ IB-Role {s} x x₁ x₂ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      b = record { txs = ToPropose }
      h = mkIBHeader slot id tt sk-IB ToPropose
      ffds' = proj₁ (send-total {ffds} {ibHeader h} {just (ibBody b)})
  in addUpkeep record s { FFDState = ffds' } IB-Role
⟦ EB-Role {s} x x₁ x₂ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
      h = mkEB slot id tt sk-EB LI []
      ffds' = proj₁ (send-total {ffds} {ebHeader h} {nothing})
  in addUpkeep record s { FFDState = ffds' } EB-Role
⟦ V-Role {s} x x₁ x₂ ⟧ =
  let open LeiosState s renaming (FFDState to ffds)
      EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
      votes = map (vote sk-V ∘ hash) EBs'
      ffds' = proj₁ (send-total {ffds} {vHeader votes} {nothing})
  in addUpkeep record s { FFDState = ffds' } V-Role
⟦ No-IB-Role {s} x x₁ ⟧ = addUpkeep s IB-Role
⟦ No-EB-Role {s} x x₁ ⟧ = addUpkeep s EB-Role
⟦ No-V-Role {s} x x₁ ⟧ = addUpkeep s V-Role

instance
  Dec-ValidAction : ValidAction ⁇²
  Dec-ValidAction {IB-Role-Action} {s} .dec
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (IB-Role x y z)
  ... | no ¬p | _ | _ = no λ where (IB-Role p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (IB-Role _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (IB-Role _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {EB-Role-Action} {s} .dec
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (EB-Role x y z)
  ... | no ¬p | _ | _ = no λ where (EB-Role p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (EB-Role _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (EB-Role _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {V-Role-Action} {s} .dec
    with dec | dec | dec
  ... | yes x | yes y | yes z = yes (V-Role x y z)
  ... | no ¬p | _ | _ = no λ where (V-Role p _ _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | no ¬p | _ = no λ where (V-Role _ p _) → ⊥-elim (¬p (recompute dec p))
  ... | _ | _ | no ¬p = no λ where (V-Role _ _ p) → ⊥-elim (¬p (recompute dec p))
  Dec-ValidAction {No-IB-Role-Action} {s} .dec
    with dec | dec
  ... | yes p | yes q = yes (No-IB-Role p q)
  ... | no ¬p | _ = no λ where (No-IB-Role p _) → ⊥-elim (¬p p)
  ... | _ | no ¬q = no λ where (No-IB-Role _ q) → ⊥-elim (¬q q)
  Dec-ValidAction {No-EB-Role-Action} {s} .dec
    with dec | dec
  ... | yes p | yes q = yes (No-EB-Role p q)
  ... | no ¬p | _ = no λ where (No-EB-Role p _) → ⊥-elim (¬p p)
  ... | _ | no ¬q = no λ where (No-EB-Role _ q) → ⊥-elim (¬q q)
  Dec-ValidAction {No-V-Role-Action} {s} .dec
    with dec | dec
  ... | yes p | yes q = yes (No-V-Role p q)
  ... | no ¬p | _ = no λ where (No-V-Role p _) → ⊥-elim (¬p p)
  ... | _ | no ¬q = no λ where (No-V-Role _ q) → ⊥-elim (¬q q)


mutual
  data ValidTrace : Actions → Type where
    [] :
      ─────────────
      ValidTrace []

    _∷_⊣_ : ∀ α {αs} →
      ∀ (tr : ValidTrace αs) →
      ∙ ValidAction α ⟦ tr ⟧∗
        ───────────────────
        ValidTrace (α ∷ αs)

  ⟦_⟧∗ : ∀ {αs : Actions} → ValidTrace αs → LeiosState
  ⟦_⟧∗ [] = initLeiosState tt sd tt
  ⟦_⟧∗ (_ ∷ _ ⊣ vα) = ⟦ vα ⟧

Irr-ValidAction : Irrelevant (ValidAction α s)
Irr-ValidAction (IB-Role x x₁ x₂) (IB-Role x₃ x₄ x₅) = refl
Irr-ValidAction (EB-Role x x₁ x₂) (EB-Role x₃ x₄ x₅) = refl
Irr-ValidAction (V-Role x x₁ x₂) (V-Role x₃ x₄ x₅)   = refl
Irr-ValidAction (No-IB-Role x x₁) (No-IB-Role x₂ x₃) = refl
Irr-ValidAction (No-EB-Role x x₁) (No-EB-Role x₂ x₃) = refl
Irr-ValidAction (No-V-Role _ _) (No-V-Role _ _)     = refl

Irr-ValidTrace : ∀ {αs} → Irrelevant (ValidTrace αs)
Irr-ValidTrace [] [] = refl
Irr-ValidTrace (α ∷ vαs ⊣ vα) (.α ∷ vαs′ ⊣ vα′)
  rewrite Irr-ValidTrace vαs vαs′ | Irr-ValidAction vα vα′
  = refl

instance
  Dec-ValidTrace : ValidTrace ⁇¹
  Dec-ValidTrace {tr} .dec with tr
  ... | [] = yes []
  ... | α ∷ αs
    with ¿ ValidTrace αs ¿
  ... | no ¬vαs = no λ where (_ ∷ vαs ⊣ _) → ¬vαs vαs
  ... | yes vαs
    with ¿ ValidAction α ⟦ vαs ⟧∗ ¿
  ... | no ¬vα = no λ where
    (_ ∷ tr ⊣ vα) → ¬vα
                  $ subst (ValidAction α) (cong ⟦_⟧∗ $ Irr-ValidTrace tr vαs) vα
  ... | yes vα = yes $ _ ∷ vαs ⊣ vα

getLabel : s ↝ s′ → Action
getLabel (IB-Role _ _ _)  = IB-Role-Action
getLabel (EB-Role _ _ _)  = EB-Role-Action
getLabel (V-Role _ _ _)   = V-Role-Action
getLabel (No-IB-Role _ _) = No-IB-Role-Action
getLabel (No-EB-Role _ _) = No-EB-Role-Action
getLabel (No-V-Role _ _)  = No-V-Role-Action

ValidAction-sound : (va : ValidAction α s) → s ↝ ⟦ va ⟧
ValidAction-sound (IB-Role {s} x x₁ x₂) = IB-Role {s} (recompute dec x) (recompute dec x₁) (recompute dec x₂)
ValidAction-sound (EB-Role {s} x x₁ x₂) = EB-Role {s} (recompute dec x) (recompute dec x₁) (recompute dec x₂)
ValidAction-sound (V-Role {s} x x₁ x₂) = V-Role {s} (recompute dec x) (recompute dec x₁) (recompute dec x₂)
ValidAction-sound (No-IB-Role {s} x x₁) = No-IB-Role {s} x x₁
ValidAction-sound (No-EB-Role {s} x x₁) = No-EB-Role {s} x x₁
ValidAction-sound (No-V-Role {s} x x₁)  = No-V-Role {s} x x₁

ValidAction-complete : (st : s ↝ s′) → ValidAction (getLabel st) s
ValidAction-complete {s} {s′} (IB-Role {s} {π} {ffds'} x x₁ x₂) =
  let open LeiosState s renaming (FFDState to ffds)
      b = record { txs = ToPropose }
      h = mkIBHeader slot id tt sk-IB ToPropose
      pr = proj₂ (send-total {ffds} {ibHeader h} {just (ibBody b)})
  in IB-Role {s} x x₁ pr
ValidAction-complete {s} (EB-Role x x₁ x₂) =
  let open LeiosState s renaming (FFDState to ffds)
      LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
      h = mkEB slot id tt sk-EB LI []
      pr = proj₂ (send-total {ffds} {ebHeader h} {nothing})
  in EB-Role {s} x x₁ pr
ValidAction-complete {s} (V-Role x x₁ x₂)  =
  let open LeiosState s renaming (FFDState to ffds)
      EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
      votes = map (vote sk-V ∘ hash) EBs'
      pr = proj₂ (send-total {ffds} {vHeader votes} {nothing})
  in V-Role {s} x x₁ pr
ValidAction-complete {s} (No-IB-Role x x₁) = No-IB-Role {s} x x₁
ValidAction-complete {s} (No-EB-Role x x₁) = No-EB-Role {s} x x₁
ValidAction-complete {s} (No-V-Role x x₁)  = No-V-Role {s} x x₁

verifyTrace : EventLog → Bool
verifyTrace l =
  let αs = L.catMaybes $ L.map traceEvent→action l
  in ¿ ValidTrace αs ¿ᵇ

{-# COMPILE GHC verifyTrace as verifyTrace #-}
