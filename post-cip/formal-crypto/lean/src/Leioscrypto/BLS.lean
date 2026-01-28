
namespace Leioscrypto.BLS


namespace G1

  def Point := Fin (2^192)
  deriving Repr, BEq

  opaque Point.valid : Point → Prop

end G1


namespace G2

  def Point := Fin (2^96)
  deriving Repr, BEq

  opaque Point.valid : Point → Prop

end G2


def PublicKey := G2.Point
  deriving Repr, BEq


def PoP := G2.Point
  deriving Repr, BEq


def Signature := G1.Point
  deriving Repr


opaque verify : ByteArray → PublicKey → Signature → Prop


end Leioscrypto.BLS
