{-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract
open import Leios.FFD

module Leios.Blocks (a : LeiosAbstract) (let open LeiosAbstract a) where

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

OSig : Bool → Type
OSig true  = Sig
OSig false = ⊤

IBRef = Hash
EBRef = Hash

--------------------------------------------------------------------------------
-- Input Blocks
--------------------------------------------------------------------------------

record IBHeaderOSig (b : Bool) : Type where
  field slotNumber : ℕ
        producerID : PoolID
        lotteryPf  : VrfPf
        bodyHash   : Hash
        signature  : OSig b

IBHeader    = IBHeaderOSig true
PreIBHeader = IBHeaderOSig false

record IBBody : Type where
  field txs : List Tx

record InputBlock : Type where
  field header : IBHeader
        body   : IBBody

  open IBHeaderOSig header public

instance
  IsBlock-IBHeaderOSig : ∀ {b} → IsBlock (IBHeaderOSig b)
  IsBlock-IBHeaderOSig = record { IBHeaderOSig }

  Hashable-IBBody : Hashable IBBody Hash
  Hashable-IBBody .hash b = hash (b .IBBody.txs)

  IsBlock-InputBlock : IsBlock InputBlock
  IsBlock-InputBlock = record { InputBlock }

mkIBHeader : ⦃ Hashable PreIBHeader Hash ⦄ → ℕ → PoolID → VrfPf → PrivKey → List Tx → IBHeader
mkIBHeader slot id π pKey txs = record { signature = sign pKey (hash h) ; IBHeaderOSig h }
  where
    h : IBHeaderOSig false
    h = record { slotNumber = slot
               ; producerID = id
               ; lotteryPf  = π
               ; bodyHash   = hash txs
               ; signature  = _
               }

getIBRef : ⦃ Hashable IBHeader Hash ⦄ → InputBlock → IBRef
getIBRef = hash ∘ InputBlock.header

-- TODO
record ibHeaderValid (h : IBHeader) : Type where
record ibBodyValid (b : IBBody) : Type where

ibHeaderValid? : (h : IBHeader) → Dec (ibHeaderValid h)
ibHeaderValid? _ = yes record {}

ibBodyValid? : (b : IBBody) → Dec (ibBodyValid b)
ibBodyValid? _ = yes record {}

ibValid : InputBlock → Type
ibValid record { header = h ; body = b } = ibHeaderValid h × ibBodyValid b

ibValid? : (ib : InputBlock) → Dec (ibValid ib)
ibValid? record { header = h ; body = b } = ibHeaderValid? h ×-dec ibBodyValid? b

--------------------------------------------------------------------------------
-- Endorser Blocks
--------------------------------------------------------------------------------

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
  Hashable-EndorserBlock : ⦃ Hashable PreEndorserBlock Hash ⦄ → Hashable EndorserBlock Hash
  Hashable-EndorserBlock .hash b = hash {T = PreEndorserBlock}
    record { EndorserBlockOSig b hiding (signature) ; signature = _ }

  IsBlock-EndorserBlockOSig : ∀ {b} → IsBlock (EndorserBlockOSig b)
  IsBlock-EndorserBlockOSig {b} = record { EndorserBlockOSig }

mkEB : ⦃ Hashable PreEndorserBlock Hash ⦄ → ℕ → PoolID → VrfPf → PrivKey → List IBRef → List EBRef → EndorserBlock
mkEB slot id π pKey LI LE = record { signature = sign pKey (hash b) ; EndorserBlockOSig b }
  where
    b : PreEndorserBlock
    b = record { slotNumber = slot
               ; producerID = id
               ; lotteryPf  = π
               ; ibRefs     = LI
               ; ebRefs     = LE
               ; signature  = _
               }

getEBRef : ⦃ Hashable PreEndorserBlock Hash ⦄ → EndorserBlock → EBRef
getEBRef = hash

-- TODO
record ebValid (eb : EndorserBlock) : Type where
--   field lotteryPfValid : {!!}
--         signatureValid : {!!}
--         ibRefsValid : {!!}
--         ebRefsValid : {!!}

ebValid? : (eb : EndorserBlock) → Dec (ebValid eb)
ebValid? _ = yes record {}

--------------------------------------------------------------------------------
-- Votes
--------------------------------------------------------------------------------

-- TODO
record vsValid (vs : List Vote) : Type where

vsValid? : (vs : List Vote) → Dec (vsValid vs)
vsValid? _ = yes record {}

--------------------------------------------------------------------------------
-- FFD for Leios Blocks
--------------------------------------------------------------------------------

module GenFFD ⦃ _ : IsBlock (List Vote) ⦄ where
  data Header : Type where
    ibHeader : IBHeader → Header
    ebHeader : EndorserBlock → Header
    vHeader  : List Vote → Header

  data Body : Type where
    ibBody : IBBody → Body

  ID : Type
  ID = ℕ × PoolID

  matchIB : IBHeader → IBBody → Type
  matchIB h b = bodyHash ≡ hash b
    where open IBHeaderOSig h; open IBBody b

  matchIB? :  ∀ (h : IBHeader) → (b : IBBody) → Dec (matchIB h b)
  matchIB? h b = bodyHash ≟ hash b
    where open IBHeaderOSig h; open IBBody b

  match : Header → Body → Type
  match (ibHeader h) (ibBody b) = matchIB h b
  match _ _ = ⊥

  headerValid : Header → Type
  headerValid (ibHeader h) = ibHeaderValid h
  headerValid (ebHeader h) = ebValid h
  headerValid (vHeader h)  = vsValid h

  headerValid? : (h : Header) → Dec (headerValid h)
  headerValid? (ibHeader h) = ibHeaderValid? h
  headerValid? (ebHeader h) = ebValid? h
  headerValid? (vHeader h)  = vsValid? h

  bodyValid : Body → Type
  bodyValid (ibBody b) = ibBodyValid b

  bodyValid? : (b : Body) → Dec (bodyValid b)
  bodyValid? (ibBody b) = ibBodyValid? b

  isValid : Header ⊎ Body → Type
  isValid (inj₁ h) = headerValid h
  isValid (inj₂ b) = bodyValid b

  isValid? : ∀ (x : Header ⊎ Body) → Dec (isValid x)
  isValid? (inj₁ h) = headerValid? h
  isValid? (inj₂ b) = bodyValid? b

  -- can we express uniqueness wrt pipelines as a property?
  msgID : Header → ID
  msgID (ibHeader h) = (slotNumber h , producerID h)
  msgID (ebHeader h) = (slotNumber h , producerID h) -- NOTE: this isn't in the paper
  msgID (vHeader  h) = (slotNumber h , producerID h) -- NOTE: this isn't in the paper

ffdAbstract : ⦃ _ : IsBlock (List Vote) ⦄ → FFDAbstract
ffdAbstract = record { GenFFD }
