
/-!
BLS types, functions, and axioms.
-/

namespace Leioscrypto.BLS


namespace Spec

  /-- Scalars for G1 and G2. -/
  def Scalar := Vector UInt8 256
  deriving Inhabited

  /-- Compressed representation of G1. -/
  def G1.Point := Vector UInt8 48
  deriving Inhabited, BEq

  /-- Sum of group elements. -/
  opaque G1.product : List G1.Point → G1.Point

  /-- Multiply a group element by a scalar. -/
  opaque G1.power : Scalar → G1.Point → G1.Point

  /-- Compressed representation of G2. -/
  def G2.Point := Vector UInt8 96
  deriving Inhabited, BEq

  /-- Sum of group elements. -/
  opaque G2.product : List G2.Point → G2.Point

  /-- Multiply a group element by a scalar. -/
  opaque G2.power : Scalar → G2.Point → G2.Point

  /-- The secret key is just a scalar. -/
  abbrev SecretKey := Scalar

  /-- Use the larger G2 for the public keys. -/
  abbrev PublicKey := G2.Point

  /-- Use the smaller G1 for the signatures. -/
  abbrev Signature := G1.Point

  /-- Conforms to https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-keygen -/
  opaque KeyGen (seed : ByteArray) : seed.size ≥ 32 → SecretKey

  /-- Conforms to https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-sktopk -/
  opaque SkToPk : SecretKey → PublicKey

  /-- Conforms to https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-keyvalidate -/
  opaque KeyValidate : PublicKey → Prop

  /-- This is the analog of `KeyValidate`, but in the other group. -/
  opaque SignatureValidate : Signature → Prop

  /-- Conforms to https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-coresign -/
  opaque CoreSign : SecretKey → ByteArray → Signature

  /-- Conforms to https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-coreverify -/
  opaque CoreVerify : PublicKey → ByteArray → Signature → Prop

  /-- Conforms to https://datatracker.ietf.org/doc/html/rfc6234#section-4.1 -/
  opaque sha256 : ByteArray → Scalar

end Spec

/-- The domain separator for Leios. -/
def dstLeios : ByteArray := "Leios".toUTF8


/-- Leios secret key. -/
def SecretKey := Spec.SecretKey
deriving Inhabited


/-- Leios public key. -/
def PublicKey := Spec.G2.Point
deriving BEq

/-- The public key is a valid point. -/
def PublicKey.WellFormed : PublicKey → Prop :=
  Spec.KeyValidate

/-- Serialize a public key. -/
private def PublicKey.toByteArray : PublicKey → ByteArray :=
  ByteArray.mk ∘ Vector.toArray

/-- Proof of possession of a public key. -/
structure ProofOfPossession where
  /-- Signature on the public key. -/
  μ₁ : Spec.G1.Point
  /-- Analog of the public key, but in the other group. -/
  μ₂ : Spec.G1.Point
deriving BEq

/-- The proof of possession has valid points. -/
def ProofOfPossession.WellFormed : ProofOfPossession → Prop
| ⟨ μ₁ , μ₂ ⟩ => Spec.SignatureValidate μ₁ ∧ Spec.SignatureValidate μ₂

/-- The message that is signed in a proof of possession. -/
private def PublicKey.popMessage (mvk : PublicKey) : ByteArray :=
  dstLeios ++ "PoP".toUTF8 ++ mvk.toByteArray

/-- Generate a public key and the proof of its possession. -/
def KeyGen (sk : SecretKey) : PublicKey × ProofOfPossession :=
  let mvk : PublicKey := Spec.SkToPk sk
  let μ₁ := Spec.CoreSign sk mvk.popMessage
  -- Note that the following line differs from the original Leios paper, but is equivalent to it.
  let μ₂ := Spec.CoreSign sk dstLeios
  ⟨ mvk , ⟨ μ₁ , μ₂ ⟩ ⟩

/-- Generated keys are well formed. -/
axiom wf_keygen (sk : SecretKey) : (KeyGen sk).fst.WellFormed ∧ (KeyGen sk).snd.WellFormed

/-- A proof of possession is cryptographically authentic. -/
def Check : PublicKey → ProofOfPossession → Prop
| mvk , ⟨ μ₁ , μ₂ ⟩ =>
    let b₁ := Spec.CoreVerify mvk mvk.popMessage μ₁
  -- Note that the following line differs from the original Leios paper, but its implication is equivalent.
    let b₂ := Spec.CoreVerify mvk dstLeios μ₂
    b₁ ∧ b₂


/-- Leios signature. -/
def Signature := Spec.G1.Point

/-- A signature is a valid point. -/
def Signature.WellFormed : Signature → Prop :=
  Spec.SignatureValidate

/-- Serialize a signature. -/
def Signature.toByteArray : Signature → ByteArray :=
  ByteArray.mk ∘ Vector.toArray

/-- Message for signing. -/
private def sigMessage (m : ByteArray) : ByteArray :=
  dstLeios ++ "M".toUTF8 ++ m

/-- Sign a message using a secret key. -/
def Sign (sk : SecretKey) (m : ByteArray) : Signature :=
  Spec.CoreSign sk (sigMessage m)

/-- Verify a message's signature using a public key. -/
def Ver (mvk : PublicKey) (m : ByteArray) (σ : Signature) : Prop :=
  Spec.CoreVerify mvk (sigMessage m) σ

/-- Signing yields a void point. -/
axiom wf_sign (sk : SecretKey) (m : ByteArray) : (Sign sk m).WellFormed

/-- Verification authenticates a signature. -/
axiom verify_sign (sk : SecretKey) (m : ByteArray) : Ver (Spec.SkToPk sk) m (Sign sk m)

/-- A Leios aggregate public key. -/
def AKey : List PublicKey → PublicKey :=
  Spec.G2.product

/-- A Leios agggregate signature. -/
def ASig : List Signature → Signature :=
  Spec.G1.product


/-- Hash together a list of signatures. -/
private def hashSignatures : List Signature → Spec.Scalar :=
  Spec.sha256 ∘ List.foldl (fun acc sig ↦ acc ++ sig.toByteArray) default

/-- Serialize a natural number to 32 bytes. -/
private def natToBytes (n : Nat) : ByteArray :=
  -- There's no point in expanding to more bytes because that would be larger than the scalar.
  let b0 := n.toUInt8
  let b1 := (n >>> 8).toUInt8
  let b2 := (n >>> 16).toUInt8
  let b3 := (n >>> 24).toUInt8
  ByteArray.mk #[b0, b1, b2, b3]

/-- Hash a natural-number prefix with data. -/
private def hashWithIndex (n : Nat) (bytes : ByteArray) : Spec.Scalar :=
  Spec.sha256 $ natToBytes n ++ bytes


/-- A Leios aggregate public key for eligibility -/
def BKey (mvks : List PublicKey) (σs : List Signature) : PublicKey :=
  let e_σ := ByteArray.mk (hashSignatures σs).toArray
  Spec.G2.product
    $ List.map (fun ⟨ mvk , i ⟩ ↦ Spec.G2.power (hashWithIndex i e_σ) mvk)
    $ mvks.zip
    $ List.range mvks.length

/-- A Leios aggregate signature for eligibility. -/
def BSig (σs : List Signature) : Signature :=
  let e_σ := ByteArray.mk (hashSignatures σs).toArray
  Spec.G1.product
    $ List.map (fun ⟨ σ , i ⟩ ↦ Spec.G1.power (hashWithIndex i e_σ) σ)
    $ σs.zip
    $ List.range σs.length


/-- Aggrefate signatures verify. -/
axiom verify_aggregate_signatures
    (keys : List PublicKey)
    (sigs : List Signature)
    (msg : ByteArray)
    (h_len : keys.length = sigs.length)
    (h_valid : ∀ i (h : i < keys.length),
    Ver (keys.get ⟨i, h⟩) msg (sigs.get ⟨i, by rw [←h_len]; exact h⟩))
  : Ver (AKey keys) msg (ASig sigs)
-- FIXME: Needs review.

/-- Aggregate eligibility signatures verify. -/
axiom verify_eligibility_aggregate
    (keys : List PublicKey)
    (sigs : List Signature)
    (msg : ByteArray)
    (h_len : keys.length = sigs.length)
    (h_valid : ∀ i (h : i < keys.length),
       Ver (keys.get ⟨i, h⟩) msg (sigs.get ⟨i, by rw [←h_len]; exact h⟩))
  : Ver (BKey keys sigs) msg (BSig sigs)
-- FIXME: Needs review.


end Leioscrypto.BLS
