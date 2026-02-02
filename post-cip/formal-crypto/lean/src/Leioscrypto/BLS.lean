
namespace Leioscrypto.BLS


namespace Spec

  -- Scalars for G1 and G2.
  def Scalar := Vector UInt8 256
  deriving Inhabited

  -- Compressed representation of G1.
  def G1.Point := Vector UInt8 48
  deriving Inhabited, BEq

  -- Sum of group elements.
  opaque G1.product : List G1.Point → G1.Point

  -- Multiply a group element by a scalar.
  opaque G1.power : Scalar → G1.Point → G1.Point

  -- Compressed representation of G2.
  def G2.Point := Vector UInt8 96
  deriving Inhabited, BEq

  -- Sum of group elements.
  opaque G2.product : List G2.Point → G2.Point

  -- Multiply a group element by a scalar.
  opaque G2.power : Scalar → G2.Point → G2.Point

  -- The secret key is just a scalar.
  abbrev SecretKey := Scalar

  -- Use the larger G2 for the public keys.
  abbrev PublicKey := G2.Point

  -- Use the smaller G1 for the signatures.
  abbrev Signature := G1.Point

  -- https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-keygen
  opaque KeyGen (seed : ByteArray) : seed.size ≥ 32 → SecretKey

  -- https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-sktopk
  opaque SkToPk : SecretKey → PublicKey

  -- https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-keyvalidate
  opaque KeyValidate : PublicKey → Prop

  -- This is the analog of `KeyValidate`, but in the other group.
  opaque SignatureValidate : Signature → Prop

  -- https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-coresign
  opaque CoreSign : SecretKey → ByteArray → Signature

  -- https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-coreverify
  opaque CoreVerify : PublicKey → ByteArray → Signature → Prop

  -- https://datatracker.ietf.org/doc/html/rfc6234#section-4.1
  opaque sha256 : ByteArray → Scalar

end Spec


def dstLeios : ByteArray := "Leios".toUTF8


def SecretKey := Spec.SecretKey
deriving Inhabited


def PublicKey := Spec.G2.Point
deriving BEq

def PublicKey.WellFormed : PublicKey → Prop :=
  Spec.KeyValidate

private def PublicKey.toByteArray : PublicKey → ByteArray :=
  ByteArray.mk ∘ Vector.toArray

structure ProofOfPossession where
  μ₁ : Spec.G1.Point
  μ₂ : Spec.G1.Point
deriving BEq

def ProofOfPossession.WellFormed : ProofOfPossession → Prop
| ⟨ μ₁ , μ₂ ⟩ => Spec.SignatureValidate μ₁ ∧ Spec.SignatureValidate μ₂

private def PublicKey.popMessage (mvk : PublicKey) : ByteArray :=
  dstLeios ++ "PoP".toUTF8 ++ mvk.toByteArray

def KeyGen (sk : SecretKey) : PublicKey × ProofOfPossession :=
  let mvk : PublicKey := Spec.SkToPk sk
  let μ₁ := Spec.CoreSign sk mvk.popMessage
  -- Note that the following line differs from the original Leios paper, but is equivalent to it.
  let μ₂ := Spec.CoreSign sk dstLeios
  ⟨ mvk , ⟨ μ₁ , μ₂ ⟩ ⟩

def Check : PublicKey → ProofOfPossession → Prop
| mvk , ⟨ μ₁ , μ₂ ⟩ =>
    let b₁ := Spec.CoreVerify mvk mvk.popMessage μ₁
  -- Note that the following line differs from the original Leios paper, but its implication is equivalent.
    let b₂ := Spec.CoreVerify mvk dstLeios μ₂
    b₁ ∧ b₂


def Signature := Spec.G1.Point

def Signature.WellFormed : Signature → Prop :=
  Spec.SignatureValidate

private def Signature.toByteArray : Signature → ByteArray :=
  ByteArray.mk ∘ Vector.toArray

private def sigMessage (m : ByteArray) : ByteArray :=
  dstLeios ++ "M".toUTF8 ++ m

def Sign (sk : SecretKey) (m : ByteArray) : Signature :=
  Spec.CoreSign sk (sigMessage m)

def Ver (mvk : PublicKey) (m : ByteArray) (σ : Signature) : Prop :=
  Spec.CoreVerify mvk (sigMessage m) σ


def AKey : List PublicKey → PublicKey :=
  Spec.G2.product

def ASig : List Signature → Signature :=
  Spec.G1.product


private def hashSignatures : List Signature → Spec.Scalar :=
  Spec.sha256 ∘ List.foldl (fun acc sig ↦ acc ++ sig.toByteArray) default

private def natToBytes (n : Nat) : ByteArray :=
  -- There's no point in expanding to more bytes because that would be larger than the scalar.
  let b0 := n.toUInt8
  let b1 := (n >>> 8).toUInt8
  let b2 := (n >>> 16).toUInt8
  let b3 := (n >>> 24).toUInt8
  ByteArray.mk #[b0, b1, b2, b3]

private def hashWithIndex (n : Nat) (bytes : ByteArray) : Spec.Scalar :=
  Spec.sha256 $ natToBytes n ++ bytes

def BKey (mvks : List PublicKey) (σs : List Signature) : PublicKey :=
  let e_σ := ByteArray.mk (hashSignatures σs).toArray
  Spec.G2.product
    $ List.map (fun ⟨ mvk , i ⟩ ↦ Spec.G2.power (hashWithIndex i e_σ) mvk)
    $ mvks.zip
    $ List.range mvks.length

def BSig (σs : List Signature) : Signature :=
  let e_σ := ByteArray.mk (hashSignatures σs).toArray
  Spec.G1.product
    $ List.map (fun ⟨ σ , i ⟩ ↦ Spec.G1.power (hashWithIndex i e_σ) σ)
    $ σs.zip
    $ List.range σs.length


end Leioscrypto.BLS
