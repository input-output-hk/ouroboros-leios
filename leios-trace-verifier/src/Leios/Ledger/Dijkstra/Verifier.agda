{- Module: Leios.Ledger.Dijkstra.Verifier

   The Dijkstra-era ledger instance the trace verifier runs ('Defaults').

   - 'verifierGov': the ledger's executable 'DummyGovStructure', except for
     the Leios crypto structure.  The executable instance hashes an endorser
     block as the *sum* of its reference hashes, so distinct EBs would share an
     identifier, and the verifier identifies EBs by hash.  Here an EB's
     identifier is the list of its reference hashes and a ranking block's
     header hash is a list of numbers, as in the verifier before; both are
     injective on what the traces record.

   - 'committeeOf': the voting committee, by the ledger's 'selectCommittee',
     for the verifier's stake distribution over its parties.  Party 'i' is the
     pool with key hash 'toℕ i' ('keyOf'), registered with a voting key at
     epoch 0; the committee is selected for epoch 0, when that key is
     honoured.  Only 'leiosCommitteeSize' of the protocol parameters matters
     to 'selectCommittee'; the others are zero.

   - 'inCommittee': the 'SpecStructure' field of the same name, membership of
     a party with a keyed seat.

   - 'unsignedCert': the certificate body the traces can supply.
-}
module Leios.Ledger.Dijkstra.Verifier where

open import Ledger.Prelude
open import Ledger.Prelude.Numeric using (0ᵘⁱ)
open import Ledger.Dijkstra.Foreign.HSStructures using (DummyGovStructure)
open import Ledger.Dijkstra.Specification.Gov.Base using (GovStructure)
open import Ledger.Dijkstra.Specification.Crypto using (LeiosCryptoStructure)
open import Data.Fin using (Fin; toℕ)
open import Data.Maybe using (Is-just)
import Data.Maybe.Relation.Unary.Any as MAny
open import Data.List.Relation.Unary.Any using () renaming (Any to Anyˡ; any? to anyˡ?)

private
  module DG = GovStructure DummyGovStructure

verifierLeiosCrypto : LeiosCryptoStructure DG.cryptoStructure
verifierLeiosCrypto = record
  { BlsVKey              = DG.BlsVKey
  ; BlsSig               = DG.BlsSig
  ; BlsPoP               = DG.BlsPoP
  ; isValidPoP           = DG.isValidPoP
  ; isSignedByAggregate  = DG.isSignedByAggregate
  ; _≤ᵏʰ_                = DG._≤ᵏʰ_
  ; ≤ᵏʰ-isDTO            = DG.≤ᵏʰ-isDTO
  ; EBHash               = List ℕ
  ; TxRefHash            = ℕ
  ; RBHeaderHash         = List ℕ
  ; hashEBRefs           = map proj₁
  ; rbHeaderHashBytes    = λ _ → 0
  }

verifierGov : GovStructure
verifierGov = record DummyGovStructure { leiosCryptoStructure = verifierLeiosCrypto }

open GovStructure verifierGov using (PParams; KeyHash; Credential)
open Credential using (KeyHashObj)
open import Ledger.Dijkstra.Specification.Certs verifierGov using (Pools; StakePoolState)
open import Ledger.Dijkstra.Specification.Leios verifierGov
  using (LeiosSeat; LeiosCommittee; selectCommittee; EBCert)
open LeiosSeat

-- A certificate as a trace records it: no signers, no signature.  The
-- traces name the certified EB, never the votes behind the certificate.
unsignedCert : EBCert
unsignedCert = record { signers = ∅ ; sig = 0 }

-- Protocol parameters with the given committee size, all others zero.
verifierPParams : ℕ → PParams
verifierPParams nc = record
  { maxBlockSize                = 0
  ; maxTxSize                   = 0
  ; maxHeaderSize               = 0
  ; maxTxExUnits                = 0 , 0
  ; maxBlockExUnits             = 0 , 0
  ; maxValSize                  = 0
  ; maxCollateralInputs         = 0
  ; pv                          = 0 , 0
  ; leiosHeaderPeriod           = 0
  ; leiosVotingPeriod           = 0
  ; leiosDiffusionPeriod        = 0
  ; leiosMaxEBSize              = 0
  ; leiosMaxEBTxsSize           = 0
  ; leiosCommitteeSize          = nc
  ; leiosQuorumStakeThreshold   = 0ᵘⁱ
  ; leiosMaxEBExUnits           = 0 , 0
  ; leiosMaxRefScriptSizePerEB  = 0
  ; a                           = 0
  ; b                           = 0
  ; keyDeposit                  = 0
  ; poolDeposit                 = 0
  ; minPoolCost                 = 0
  ; monetaryExpansion           = 0ᵘⁱ
  ; treasuryCut                 = 0ᵘⁱ
  ; coinsPerUTxOByte            = 0
  ; prices                      = tt
  ; minFeeRefScriptCoinsPerByte = 0ℚ
  ; maxRefScriptSizePerTx       = 0
  ; maxRefScriptSizePerBlock    = 0
  ; refScriptCostStride         = record { value = 1 ; proof = _ }
  ; refScriptCostMultiplier     = 0ℚ
  ; minUTxOValue                = 0
  ; Emax                        = 0
  ; nopt                        = 0
  ; a0                          = 0ℚ
  ; collateralPercentage        = 0
  ; costmdlsAssoc               = record { languageCostModels = [] }
  ; poolThresholds              = record { Q1 = 0ℚ ; Q2a = 0ℚ ; Q2b = 0ℚ ; Q4 = 0ℚ ; Q5 = 0ℚ }
  ; drepThresholds              = record { P1 = 0ℚ ; P2a = 0ℚ ; P2b = 0ℚ ; P3 = 0ℚ ; P4 = 0ℚ
                                         ; P5a = 0ℚ ; P5b = 0ℚ ; P5c = 0ℚ ; P5d = 0ℚ ; P6 = 0ℚ }
  ; ccMinSize                   = 0
  ; ccMaxTermLength             = 0
  ; govActionLifetime           = 0
  ; govActionDeposit            = 0
  ; drepDeposit                 = 0
  ; drepActivity                = 0
  }
  where open import Data.Rational using () renaming (0ℚ to 0ℚ)

-- The pool of a party.
keyOf : ∀ {n} → Fin n → KeyHash
keyOf = toℕ

module _ {n : ℕ} (stake : TotalMap (Fin n) ℕ) (committeeSize : ℕ) where

  private
    parties : List (Fin n)
    parties = allFin' n
      where
        allFin' : (m : ℕ) → List (Fin m)
        allFin' m = Data.List.allFin m
          where import Data.List

  -- The stake distribution, by pool key hash.
  stakeByKey : KeyHash ⇀ Coin
  stakeByKey = fromListᵐ (map (λ i → keyOf i , TotalMap.lookup stake i) parties)

  -- Every party as a registered pool with a voting key, registered at epoch 0.
  poolOf : Fin n → StakePoolState
  poolOf i = record
    { owners        = ∅
    ; cost          = 0
    ; margin        = 0ᵘⁱ
    ; pledge        = 0
    ; rewardAccount = record { net = 0 ; stake = KeyHashObj (keyOf i) }
    ; vrf           = keyOf i
    ; bls           = just (keyOf i , 0)
    }

  verifierPools : Pools
  verifierPools = fromListᵐ (map (λ i → keyOf i , poolOf i) parties)

  committeeOf : LeiosCommittee
  committeeOf = selectCommittee (verifierPParams committeeSize) 0 stakeByKey verifierPools

  -- Party 'i' holds a seat of the committee that can sign.
  inCommittee : Fin n → Type
  inCommittee i = Anyˡ (λ s → s .pool ≡ keyOf i × Is-just (s .key)) committeeOf

  inCommittee? : ∀ i → Dec (inCommittee i)
  inCommittee? i = anyˡ? (λ s → (s .pool ≟ keyOf i) ×-dec MAny.dec (λ _ → yes tt) (s .key)) committeeOf
