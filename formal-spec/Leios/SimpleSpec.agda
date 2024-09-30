{-# OPTIONS --allow-unsolved-metas #-}

module Leios.SimpleSpec where

open import Ledger.Prelude
open import Data.List using (upTo)

fromTo : ℕ → ℕ → List ℕ
fromTo m n = map (_+ m) (upTo (n ∸ m))

-- High level structure:


--                                      (simple) Leios
--                                        /         |
-- +-------------------------------------+          |
-- | Header Diffusion     Body Diffusion |          |
-- +-------------------------------------+       Base Protocol
--                                        \      /
--                                        Network


record FFDAbstract : Type₁ where
  field Header Body ID : Type
        match : Header → Body → Type
        msgID : Header → ID

module FFD (a : FFDAbstract) (let open FFDAbstract a) where

  data Input : Type where
    Send  : Header → Maybe Body → Input
    Fetch : Input

  data Output : Type where
    SendRes  : Output
    FetchRes : List (Header ⊎ Body) → Output

  record Functionality : Type₁ where
    field State : Type
          stepRel : Input → State → State × Output → Type

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

module Leios (a : LeiosAbstract) (let open LeiosAbstract a) (id : PoolID) (pKey : PrivKey) where

  OSig : Bool → Type
  OSig true  = Sig
  OSig false = ⊤

  IBRef = Hash
  EBRef = Hash

  slice : (L : ℕ) → ⦃ NonZero L ⦄ → ℕ → ℕ → ℙ ℕ
  slice L s x = fromList (fromTo s' (s' + (L ∸ 1)))
    where s' = ((s / L) ∸ x) * L -- equivalent to the formula in the paper

  -- IsBlock typeclass (could do a closed-world approach instead)
  -- Q: should votes have an instance of this class?
  record IsBlock (B : Type) : Type where
    field slotNumber : B → ℕ
          producerID : B → PoolID
          lotteryPf  : B → VrfPf

    infix 4 _∈ᴮ_

    _∈ᴮ_ : B → ℙ ℕ → Type
    b ∈ᴮ X = slotNumber b ∈ X

  open IsBlock ⦃...⦄ public

  record IBHeaderOSig (b : Bool) : Type where
    field slotNumber : ℕ
          producerID : PoolID
          lotteryPf  : VrfPf
          bodyHash   : Hash
          signature  : OSig b

  instance
    IsBlock-IBHeaderOSig : ∀ {b} → IsBlock (IBHeaderOSig b)
    IsBlock-IBHeaderOSig = record { IBHeaderOSig }

  IBHeader    = IBHeaderOSig true
  PreIBHeader = IBHeaderOSig false

  instance postulate Hashable-PreIBHeader : Hashable PreIBHeader Hash

  mkIBHeader : ℕ → PoolID → VrfPf → List Tx → IBHeader
  mkIBHeader slot id π txs = record { signature = sign pKey (hash h) ; IBHeaderOSig h }
    where
      h : IBHeaderOSig false
      h = record { slotNumber = slot
                 ; producerID = id
                 ; lotteryPf  = π
                 ; bodyHash   = hash txs
                 ; signature  = _
                 }

  record IBBody : Type where
    field txs : List Tx

  record InputBlock : Type where
    field header : IBHeader
          body   : IBBody

    open IBHeaderOSig header public

  instance
    Hashable-IBBody : Hashable IBBody Hash
    Hashable-IBBody .hash b = hash (b .IBBody.txs)

    IsBlock-InputBlock : IsBlock InputBlock
    IsBlock-InputBlock = record { InputBlock }

  record EndorserBlockOSig (b : Bool) : Type where
    field slotNumber : ℕ
          producerID : PoolID
          lotteryPf  : VrfPf
          ibRefs     : List IBRef
          ebRefs     : List EBRef
          signature  : OSig b

  EndorserBlock    = EndorserBlockOSig true
  PreEndorserBlock = EndorserBlockOSig false

  instance
    postulate Hashable-PreEndorserBlock : Hashable PreEndorserBlock Hash

    Hashable-EndorserBlock : Hashable EndorserBlock Hash
    Hashable-EndorserBlock .hash b = hash {T = PreEndorserBlock}
      record { EndorserBlockOSig b hiding (signature) ; signature = _ }

    IsBlock-EndorserBlockOSig : ∀ {b} → IsBlock (EndorserBlockOSig b)
    IsBlock-EndorserBlockOSig {b} = record { EndorserBlockOSig }

  mkEB : ℕ → PoolID → VrfPf → List IBRef → List EBRef → EndorserBlock
  mkEB slot id π LI LE = record { signature = sign pKey (hash b) ; EndorserBlockOSig b }
    where
      b : PreEndorserBlock
      b = record { slotNumber = slot
                 ; producerID = id
                 ; lotteryPf  = π
                 ; ibRefs     = LI
                 ; ebRefs     = LE
                 ; signature  = _
                 }

  postulate getIBRef : InputBlock    → IBRef -- I assume these two are just the regular hashes?
            getEBRef : EndorserBlock → EBRef

  -- TODO
  -- record ebValid (eb : EndorserBlock) : Type where
  --   field lotteryPfValid : {!!}
  --         signatureValid : {!!}
  --         ibRefsValid : {!!}
  --         ebRefsValid : {!!}

  module GenFFD where
    data Header : Type where
      ibHeader : IBHeader → Header
      ebHeader : EndorserBlock → Header
      vHeader  : List Vote → Header

    data Body : Type where
      ibBody : IBBody → Body

    ID : Type
    ID = ℕ × PoolID

    match : Header → Body → Type
    match (ibHeader h) (ibBody b) = bodyHash ≡ hash b
      where open IBHeaderOSig h; open IBBody b
    match _ _ = ⊥

    -- can we express uniqueness wrt pipelines as a property?
    msgID : Header → ID
    msgID (ibHeader h) = (slotNumber h , producerID h)
    msgID (ebHeader h) = (slotNumber h , producerID h) -- NOTE: this isn't in the paper
    msgID (vHeader h)  = {!!}

  ffdAbstract : FFDAbstract
  ffdAbstract = record { GenFFD }

  module BaseFunctionality where
    postulate StakeDistr Cert : Type

    data Input : Type₁ where
      INIT   : (EndorserBlock × Cert → Type) → Input
      SUBMIT : EndorserBlock ⊎ List Tx → Input -- maybe we have both

    data Output : Type where
      STAKE : StakeDistr → Output

    postulate State : Type
              _⇀⟦_⟧_ : State → Input → State × Output → Type

  module _ (FFD : FFD.Functionality ffdAbstract) where
    module FFD' = FFD.Functionality FFD using (State) renaming (stepRel to _⇀⟦_⟧_)
    module B = BaseFunctionality

    postulate VTy FTCHTy : Type
              initSlot : VTy → ℕ
              initFFDState : FFD'.State

    data LeiosInput : Type where
      INIT     : VTy → LeiosInput
      SLOT     : LeiosInput
      FTCH-LDG : LeiosInput

    data LeiosOutput : Type where
      FTCH-LDG : FTCHTy → LeiosOutput
      EMPTY : LeiosOutput

    record LeiosState : Type where
      field V : VTy
            SD : B.StakeDistr
            FFDState : FFD'.State
            Ledger : List Tx
            MemPool : List Tx
            IBs : List InputBlock
            EBs : List EndorserBlock
            Vs  : List (List Vote)
            slot : ℕ

    initLeiosState : VTy → B.StakeDistr → LeiosState
    initLeiosState V SD = record
      { V        = V
      ; SD       = SD
      ; FFDState = initFFDState
      ; Ledger   = []
      ; MemPool  = []
      ; IBs      = []
      ; EBs      = []
      ; Vs       = []
      ; slot     = initSlot V
      }

    postulate canProduceIB : ℕ → VrfPf → Type
              canProduceEB : ℕ → VrfPf → Type
              canProduceV1 : ℕ → Type
              canProduceV2 : ℕ → Type

    -- some predicates about EBs
    module _ (s : LeiosState) (eb : EndorserBlock) where
      open EndorserBlockOSig eb
      open LeiosState s

      postulate isVote1Certified : Type -- Q: what's the threshold? (pg 7, (5))

      vote2Eligible : Type
      vote2Eligible = length ebRefs ≥ lengthˢ candidateEBs / 2 -- should this be `>`?
                    × fromList ebRefs ⊆ candidateEBs
        where candidateEBs : ℙ Hash
              candidateEBs = mapˢ getEBRef $ filterˢ (_∈ᴮ slice L slot (μ + 3)) (fromList EBs)

      allIBRefsKnown : Type
      allIBRefsKnown = ∀[ ref ∈ fromList ibRefs ] ref ∈ˡ map getIBRef IBs

    postulate instance isVote1Certified? : ∀ {s eb} → isVote1Certified s eb ⁇

    private variable s     : LeiosState
                     ffds' : FFD'.State
                     π     : VrfPf

    open LeiosState using (FFDState; MemPool)

    data _⇀⟦_⟧_ : Maybe LeiosState → LeiosInput → LeiosState × LeiosOutput → Type where
      Init : ∀ {V bs bs' SD} →
           ∙ {!!} -- create & register the IB/EB lottery and voting keys with key reg
           ∙ bs B.⇀⟦ B.INIT {!V_chkCerts!} ⟧ (bs' , B.STAKE SD)
           ────────────────────────────────
           nothing ⇀⟦ INIT V ⟧ (initLeiosState V SD , EMPTY)

      -- fix: we need to do Slot before every other SLOT transition
      Slot : ∀ {msgs} → let ffds = s .FFDState
                            l = {!!} -- construct ledger l
             in
           ∙ FFD.Fetch FFD'.⇀⟦ ffds ⟧ (ffds' , FFD.FetchRes msgs)
           ────────────────────────────────
             just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' ; Ledger = l } , EMPTY)

      Ftch : ∀ {l} →
           ────────────────────────────────
           just s ⇀⟦ FTCH-LDG ⟧ (s , FTCH-LDG l)

      -- TODO: Base chain

      IB-Role : let open LeiosState s
                    txs = s .MemPool
                    ffds = s .FFDState
                    b = GenFFD.ibBody (record { txs = txs })
                    h = GenFFD.ibHeader (mkIBHeader slot id π txs)
              in
              ∙ canProduceIB slot π
              ∙ FFD.Send h (just b) FFD'.⇀⟦ ffds ⟧ (ffds' , FFD.SendRes)
              ────────────────────────────────
              just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

      EB-Role : let open LeiosState s
                    LI = map getIBRef $ setToList $ filterˢ (_∈ᴮ slice L slot (Λ + 1)) (fromList IBs)
                    LE = map getEBRef $ setToList $ filterˢ (isVote1Certified s) $
                               filterˢ (_∈ᴮ slice L slot (μ + 2)) (fromList EBs)
                    h = mkEB slot id π LI LE
                    ffds = s .FFDState
              in
              ∙ canProduceEB slot π
              ∙ FFD.Send (GenFFD.ebHeader h) nothing FFD'.⇀⟦ ffds ⟧ (ffds' , FFD.SendRes)
              ────────────────────────────────
              just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

      V1-Role : let open LeiosState s
                    EBs' = filterˢ (allIBRefsKnown s) $ filterˢ (_∈ᴮ slice L slot (μ + 1)) (fromList EBs)
                    votes = map (vote ∘ hash) (setToList EBs')
                    ffds = s .FFDState
              in
              ∙ canProduceV1 slot
              ∙ FFD.Send (GenFFD.vHeader votes) nothing FFD'.⇀⟦ ffds ⟧ (ffds' , FFD.SendRes)
              ────────────────────────────────
              just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)

      V2-Role : let open LeiosState s
                    EBs' = filterˢ (vote2Eligible s) $ filterˢ (_∈ᴮ slice L slot 1) (fromList EBs)
                    votes = map (vote ∘ hash) (setToList EBs')
                    ffds = s .FFDState
              in
              ∙ canProduceV2 slot
              ∙ FFD.Send (GenFFD.vHeader votes) nothing FFD'.⇀⟦ ffds ⟧ (ffds' , FFD.SendRes)
              ────────────────────────────────
              just s ⇀⟦ SLOT ⟧ (record s { FFDState = ffds' } , EMPTY)
