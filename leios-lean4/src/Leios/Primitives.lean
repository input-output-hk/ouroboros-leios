import Leios.Primitives.ByteString


namespace Leios.Primitives


abbrev Encoding := Nat


class Encode (a : Type) where
  encode : Encoding → Nat


end Leios.Primitives
