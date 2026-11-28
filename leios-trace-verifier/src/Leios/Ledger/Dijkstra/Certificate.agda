{- Module: Leios.Ledger.Dijkstra.Certificate

   Dijkstra's certificate validity ('ValidEBCert') read as the certificate
   condition of leios-spec.

   What leios-spec requires of a certificate is the following:

   - 'Leios.Linear.Cert₁': a certificate embedded in the RB must certify the
     queried reference, 'getCertRef cert ≡ hash currentRB';
   - 'Leios.Voting.Certifier.Certified' (and 'Voting.Real.RealCertified'): the
     voting functionality answers a query positively iff the vote log holds
     votes for the reference from at least 'threshold' distinct parties; the
     certificate itself is then 'mkCert ref', built from the reference alone.

   'ValidCertFor cmt τ r c' is Dijkstra validity at reference r: r must be a
   ranking-block header hash (an EB hash is never certified), the certificate
   must name it, and 'ValidEBCert' must hold for its serialisation, which is
   the premise of Dijkstra's 'CHAIN-EB' rule ('ValidCertFor⇔ValidEBCert').
   It implies the 'Cert₁' premise ('ValidCertFor⇒certRef',
   'ValidCertFor⇒Cert₁').

   Disagreements, field by field:

   - reference: leios-spec 'getCertRef cert'; Dijkstra none, the message is
     the previous block's 'headerHash', supplied by 'CHAIN-EB'.  Bridged by
     'LeiosCert.certRef'.
   - quorum: leios-spec counts distinct voters, 'threshold ≤ length votes'
     (a natural number of parties, every party weighing one); Dijkstra sums
     stake weights, 'τ ≤ Σ weight' with τ = 'leiosQuorumStakeThreshold' a
     fraction of the *total* stake.  They coincide only under uniform
     weights.  No implication holds in general in either direction.
   - voters: leios-spec any party ('Fin n' slot of the certifier); Dijkstra a
     seat index of the committee, which must hold an honoured BLS key
     ('signersSeated', 'signersKeyed').
   - signature: leios-spec none in the certificate (individual votes are
     checked by the 'Valid' predicate of 'Voting.Real'); Dijkstra one
     aggregate BLS signature over the header hash ('validSignature').
   - construction: leios-spec 'mkCert : EBRef → EBCert' from the reference
     alone; a Dijkstra certificate needs the signer set and the aggregate
     signature, so 'mkCert' has no Dijkstra counterpart without the votes.
   - timing: 'certificationDelay' (Dijkstra, milliseconds converted to slots)
     corresponds to leios-spec's '3 * Lhdr + Lvote + Ldiff' in 'certRequest'
     (slots); Dijkstra additionally requires announcing and certifying
     blocks to share an epoch.  Neither belongs to the certificate itself.
-}
{-# OPTIONS --safe #-}

open import Ledger.Dijkstra.Specification.Gov.Base using (GovStructure)

module Leios.Ledger.Dijkstra.Certificate (gs : GovStructure) (open GovStructure gs) where

open import Ledger.Prelude
open import Ledger.Prelude.Numeric.UnitInterval using (UnitInterval)
open import Ledger.Dijkstra.Specification.Leios gs
  using (LeiosCommittee; ValidEBCert; Dec-ValidEBCert) renaming (EBCert to DijkstraEBCert)
open import Leios.Ledger.Dijkstra gs using (LHash; LeiosCert; ⟨_,_⟩ᶜ; certRef; certBody)

import Data.Maybe.Relation.Unary.All as Maybe
open import Relation.Nullary.Decidable using (_×-dec_)

ValidCertFor : LeiosCommittee → UnitInterval → LHash → LeiosCert → Type
ValidCertFor cmt τ (inj₁ _) _ = ⊥
ValidCertFor cmt τ (inj₂ h) c =
  certRef c ≡ h × ValidEBCert cmt τ (rbHeaderHashBytes h) (certBody c)

instance
  Dec-ValidCertFor : ∀ {cmt τ r c} → ValidCertFor cmt τ r c ⁇
  Dec-ValidCertFor {r = inj₁ _} = ⁇ no λ ()
  Dec-ValidCertFor {cmt} {τ} {inj₂ h} {c} =
    ⁇ (certRef c ≟ h ×-dec ¿ ValidEBCert cmt τ (rbHeaderHashBytes h) (certBody c) ¿)

-- leios-spec's 'getCertRef' of the instance in 'Leios.Ledger.Dijkstra'.
getCertRef : LeiosCert → LHash
getCertRef = inj₂ ∘ certRef

ValidCertFor⇒certRef : ∀ {cmt τ r c} → ValidCertFor cmt τ r c → getCertRef c ≡ r
ValidCertFor⇒certRef {r = inj₂ _} (refl , _) = refl

-- A query answer valid in Dijkstra's sense satisfies the 'Cert₁' premise
-- 'Maybe.All (λ cert → getCertRef cert ≡ hash currentRB) c'.
ValidCertFor⇒Cert₁ : ∀ {cmt τ r mc} → Maybe.All (ValidCertFor cmt τ r) mc
  → Maybe.All (λ c → getCertRef c ≡ r) mc
ValidCertFor⇒Cert₁ = Maybe.map ValidCertFor⇒certRef

-- The 'CHAIN-EB' premise is validity at the announcing header's hash.
ValidCertFor⇔ValidEBCert : ∀ {cmt τ h cert}
  → ValidCertFor cmt τ (inj₂ h) ⟨ h , cert ⟩ᶜ ⇔ ValidEBCert cmt τ (rbHeaderHashBytes h) cert
ValidCertFor⇔ValidEBCert = mk⇔ proj₂ (refl ,_)
