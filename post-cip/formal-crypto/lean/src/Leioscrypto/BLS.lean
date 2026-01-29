
namespace Leioscrypto.BLS


namespace G1

  def Point := Fin (2^192)
  deriving BEq

  opaque Point.WellFormed : Point → Prop

end G1


namespace G2

  def Point := Fin (2^96)
  deriving BEq

  opaque Point.WellFormed : Point → Prop

end G2


def PublicKey := G2.Point
  deriving BEq


def PoP := G2.Point
  deriving BEq


def Signature := G1.Point

namespace Signature

  def WellFormed : Signature → Prop := G1.Point.WellFormed

end Signature

opaque verify : ByteArray → PublicKey → Signature → Prop


end Leioscrypto.BLS
