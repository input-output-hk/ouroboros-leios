
namespace List

-- Adapted from `Mathlib.Data.List.Defs`.

/-- `l.Forall p` is equivalent to `∀ a ∈ l, p a`, but unfolds directly to a conjunction, i.e.
`List.Forall p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
@[simp]
def Forall {α : Type} (p : α → Prop) : List α → Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ Forall p l

end List
