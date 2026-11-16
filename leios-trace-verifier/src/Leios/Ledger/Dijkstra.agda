{- Module: Leios.Ledger.Dijkstra

   The Leios abstract interface ('Leios.Abstract.LeiosAbstract' of leios-spec)
   instantiated with the types of the Dijkstra-era ledger specification
   (formal-ledger-specifications, 'Ledger.Dijkstra.Specification.Leios*').

   The module is parametric over a 'GovStructure', which is all that
   'Ledger.Dijkstra.Specification.Leios' (committee, certificate) and
   'Leios.Types' (endorser block, its hash) need.  'TransactionStructure' and
   'AbstractFunctions' are needed only by the EB validity and chain rules
   ('Leios.Validity', 'Chain'), which read transaction bodies; the traces carry
   no transaction bodies, so nothing here depends on them.  A concrete,
   compilable instance is 'Leios.Ledger.Dijkstra.Foreign'.

   Correspondences (leios-spec field := Dijkstra notion):

   - Tx := TxRefHash × ℕ, a transaction reference of a Dijkstra
     'EndorserBlock' (reference hash and declared size).  leios-spec uses Tx
     only as an opaque payload (EB contents, 'splitTxs', 'Hashable (List Tx)')
     and never inspects a transaction, so the reference is what the Leios
     protocol layer actually needs; it is also what a trace records
     ('EBGenerated.transactions' carries ids and sizes).  With this choice a
     leios-spec EB's tx list *is* a Dijkstra 'EndorserBlock' ('toDijkstraEB'),
     and the leios-spec EB hash *is* Dijkstra's 'hashEB' ('hash-pre≡hashEB').
     Caveat: a trace records transaction ids, while a 'TxRefHash' covers the
     complete transaction bytes, witnesses included (see 'Leios.Types').

   - Hash := EBHash ⊎ RBHeaderHash.  leios-spec has a single 'Hash' for both
     EB identifiers ('EBRef = Hash') and ranking-block hashes (votes and
     certificates are keyed by 'hash currentRB'); Dijkstra keeps the two
     apart.  The sum keeps them apart here too.

   - EBCert := 'LeiosCert', a Dijkstra 'EBCert' (signers, aggregate signature)
     tagged with the ranking-block header hash it certifies.  leios-spec
     requires 'getCertRef : EBCert → Hash'; a Dijkstra certificate does not
     carry its message (the chain rule supplies it from the previous block),
     so the reference has to be added.

   - PoolID := Fin n, with an injection 'keyOf : Fin n → KeyHash' into
     Dijkstra's pool ids.  PoolID := KeyHash is not usable: leios-spec's
     'StakeDistr' is a 'TotalMap PoolID ℕ', and in the finite set theory both
     specs use, a total map over an infinite type such as KeyHash (ℕ in the
     Foreign instance) cannot be constructed.  'Fin n' is also the party index
     of the verifier and of the Praos base layer.

   - Vote := Fin n × Hash, the voter and the signed hash.  Dijkstra has no
     per-vote type (votes are off-ledger; only their aggregate appears).

   - VrfPf, PrivKey, Sig, BodyHash, sign, splitTxs: Dijkstra has no
     counterpart (no VRF, no individual signing, no mempool split), so they
     are parameters ('OffLedger').
-}
{-# OPTIONS --safe #-}

open import Ledger.Dijkstra.Specification.Gov.Base using (GovStructure)

module Leios.Ledger.Dijkstra (gs : GovStructure) (open GovStructure gs) where

open import Ledger.Prelude
import Class.Hashable as LH
open import Data.Fin using (Fin)
open import Leios.Abstract using (LeiosAbstract)
import Leios.Blocks

open import Ledger.Dijkstra.Specification.Leios gs as DL using () renaming (EBCert to DijkstraEBCert)
open import Ledger.Dijkstra.Specification.Leios.Types cryptoStructure leiosCryptoStructure as DT
  using (hashEB) renaming (EndorserBlock to DijkstraEB)

-- A transaction reference of an endorser block.
TxRef : Type
TxRef = TxRefHash × ℕ

-- EB identifiers and ranking-block header hashes, kept apart.
LHash : Type
LHash = EBHash ⊎ RBHeaderHash

-- A certificate together with the ranking-block header hash it certifies.
record LeiosCert : Type where
  constructor ⟨_,_⟩ᶜ
  field certRef   : RBHeaderHash
        certBody  : DijkstraEBCert

open LeiosCert public

-- What the Leios protocol layer needs and the ledger specification does not
-- provide.
record OffLedger : Type₁ where
  field
    n         : ℕ
    keyOf     : Fin n → KeyHash
    LVrfPf LPrivKey LSig LBodyHash : Type
    ⦃ DecEq-LVrfPf ⦄ : DecEq LVrfPf
    ⦃ DecEq-LSig ⦄   : DecEq LSig
    voterOf   : LPrivKey → Fin n
    lsign     : LPrivKey → LHash → LSig
    lsplitTxs : List TxRef → List TxRef × List TxRef

module _ (o : OffLedger) (open OffLedger o) where

  dijkstraAbstract : LeiosAbstract
  dijkstraAbstract = record
    { Tx           = TxRef
    ; PoolID       = Fin n
    ; BodyHash     = LBodyHash
    ; VrfPf        = LVrfPf
    ; PrivKey      = LPrivKey
    ; Sig          = LSig
    ; Hash         = LHash
    ; EBCert       = LeiosCert
    ; Vote         = Fin n × LHash
    ; vote         = λ sk h → voterOf sk , h
    ; sign         = lsign
    ; getCertRef   = inj₂ ∘ certRef
    ; splitTxs     = lsplitTxs
    ; Hashable-Txs = record { hash = inj₁ ∘ hashEBRefs }
    }

  open Leios.Blocks dijkstraAbstract
    using (EndorserBlockOSig; PreEndorserBlock)

  -- leios-spec's EB hash is Dijkstra's: the hash of the reference list only.
  -- (Slot, producer and VRF proof are not part of the identifier, as in
  -- Dijkstra and as in 'Defaults.hpe'.)
  Hashable-PreEndorserBlock : LH.Hashable PreEndorserBlock LHash
  Hashable-PreEndorserBlock = record { hash = inj₁ ∘ hashEBRefs ∘ EndorserBlockOSig.txs }

  -- The Dijkstra endorser block of a leios-spec one: its transaction list.
  toDijkstraEB : ∀ {S} → EndorserBlockOSig S → DijkstraEB
  toDijkstraEB eb = record { ebTxRefs = EndorserBlockOSig.txs eb }

  hash-pre≡hashEB : (eb : PreEndorserBlock)
    → LH.Hashable.hash Hashable-PreEndorserBlock eb ≡ inj₁ (hashEB (toDijkstraEB eb))
  hash-pre≡hashEB _ = refl
