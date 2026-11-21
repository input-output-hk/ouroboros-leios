{- Module: Leios.Ledger.Dijkstra.Foreign

   The Dijkstra instance of 'Leios.Ledger.Dijkstra' at the ledger's own
   executable structures ('Ledger.Dijkstra.Foreign.HSStructures', with the
   dummy external functions).  All ledger hashes and key hashes are ℕ there,
   so the instance is concrete and compiles to Haskell.

   Not '--safe': 'Ledger.Dijkstra.Foreign.ExternalStructures' postulates the
   well-formedness of parameter updates ('HsGovParams.ppWF', two 'trustMe's),
   which nothing here uses.
-}
module Leios.Ledger.Dijkstra.Foreign where

open import Ledger.Prelude
open import Ledger.Dijkstra.Foreign.HSStructures using (DummyGovStructure)
open import Leios.Abstract using (LeiosAbstract)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-injective)

open import Leios.Ledger.Dijkstra DummyGovStructure public
import Leios.Ledger.Dijkstra.Committee
import Leios.Ledger.Dijkstra.Certificate
module Committee   = Leios.Ledger.Dijkstra.Committee DummyGovStructure
module Certificate = Leios.Ledger.Dijkstra.Certificate DummyGovStructure

-- Party i is the pool with key hash i, as in the trace verifier's indexing.
-- The off-ledger primitives are the trivial ones of 'Defaults'.
hsOffLedger : ℕ → OffLedger
hsOffLedger n = record
  { n         = n
  ; keyOf     = toℕ
  ; LVrfPf    = ⊤
  ; LPrivKey  = Fin n
  ; LSig      = ⊤
  ; LBodyHash = ⊤
  ; voterOf   = id
  ; lsign     = λ _ _ → tt
  ; lsplitTxs = [] ,_
  }

keyOf-injective : ∀ {n} {i j : Fin n} → toℕ i ≡ toℕ j → i ≡ j
keyOf-injective = toℕ-injective

hsAbstract : ℕ → LeiosAbstract
hsAbstract n = dijkstraAbstract (hsOffLedger n)
