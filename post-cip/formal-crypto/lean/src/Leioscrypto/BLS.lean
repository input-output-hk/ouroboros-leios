
namespace Leioscrypto.BLS


def dstLeios : ByteArray := "Leios".toUTF8


def SecretKey := Vector UInt8 256
deriving Inhabited


namespace Spec

  def G1.Point := Vector UInt8 48
  deriving Inhabited

  -- Group multiplication.
  opaque G1.product : List G1.Point → G1.Point

  def G2.Point := Vector UInt8 96
  deriving Inhabited

  -- Group multiplication.
  opaque G2.product : List G2.Point → G2.Point

  abbrev PublicKey := G2.Point

  abbrev Signature := G1.Point

  -- https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-keygen
  opaque KeyGen (seed : ByteArray) : seed.size ≥ 32 → SecretKey

  -- https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-sktopk
  opaque SkToPk : SecretKey → PublicKey

  -- https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-keyvalidate
  opaque KeyValidate : PublicKey → Prop

  -- https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-coresign
  opaque CoreSign : SecretKey → ByteArray → Signature

  -- https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#name-coreverify
  opaque CoreVerify : PublicKey → ByteArray → Signature → Prop

end Spec


def PublicKey := Spec.G2.Point

def PublicKey.WellFormed : PublicKey → Prop :=
  Spec.KeyValidate

private def PublicKey.toByteArray : PublicKey → ByteArray :=
  ByteArray.mk ∘ Vector.toArray

structure ProofOfPossession where
  μ₁ : Spec.G1.Point
  μ₂ : Spec.G1.Point

private def PublicKey.popMessage (mvk : PublicKey) : ByteArray :=
  dstLeios ++ "PoP".toUTF8 ++ mvk.toByteArray

def KeyGen (sk : SecretKey) : PublicKey × ProofOfPossession :=
  let mvk : PublicKey := Spec.SkToPk sk
  let μ₁ := Spec.CoreSign sk mvk.popMessage
  let μ₂ := Spec.CoreSign sk dstLeios
  ⟨ mvk , ⟨ μ₁ , μ₂ ⟩ ⟩

def Check : PublicKey → ProofOfPossession → Prop
| mvk , ⟨ μ₁ , μ₂ ⟩ =>
    let b₁ := Spec.CoreVerify mvk mvk.popMessage μ₁
    let b₂ := Spec.CoreVerify mvk dstLeios μ₂
    b₁ ∧ b₂


def Signature := Spec.G1.Point

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


end Leioscrypto.BLS
