import Mathlib.Basic.Real.Basic

/-!
# Protocol parameters of Linear Leios

Times are measured in slots (`ℕ`). The fields are filled in with the model.
-/

namespace Leios

/-- Protocol and environment parameters. -/
structure Params where
  /-- Announcement period: time for an RB header to reach the network. -/
  Lhdr : ℕ

end Leios
