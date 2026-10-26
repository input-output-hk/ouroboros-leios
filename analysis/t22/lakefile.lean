import Lake
open Lake DSL

/-! Minimal Lean 4 model of Linear Leios.
Lean v4.34.1 and Mathlib are pinned to a fixed commit; bump both together. -/
package leios where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- The model and its theorems. Must be free of `sorry`. -/
@[default_target] lean_lib Leios where
  globs := #[`Leios, `Leios.+]
