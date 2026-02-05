
namespace Leioscrypto


def lookup₀ {α : Type} [BEq α] [LawfulBEq α] {β : Type} (p : β → α) (xs : List β) (k : α) (h : k ∈ xs.map p) : β :=
  let test (k' : β) : Bool := p k' == k
  match h_find : xs.find? test with
  | some x => x
  | none =>
      have impossible : False :=
        by
          simp only [List.mem_map] at h
          obtain ⟨r, r_in_list, r_has_id⟩ := h
          rw [List.find?_eq_none] at h_find
          specialize h_find r r_in_list
          rw [beq_iff_eq] at h_find
          rw [r_has_id] at h_find
          simp at h_find
      impossible.elim

def lookup₁ {α : Type} [BEq α] [LawfulBEq α] {β : Type} (kvs : List (α × β)) (k : α) (h : k ∈ kvs.map Prod.fst) : β :=
  Prod.snd $ lookup₀ Prod.fst kvs k h

def lookup₃ {α : Type} [BEq α] [LawfulBEq α] {β : Type} (p : β → α) (xs : List β) (k : α) (h : k ∈ xs.map p) : Nat :=
  let test (k' : β) : Bool := p k' == k
  match h_find : xs.findIdx? test with
  | some i => i
  | none =>
      have impossible : False :=
        by
          simp only [List.mem_map] at h
          obtain ⟨r, r_in_list, r_has_id⟩ := h
          rw [List.findIdx?_eq_none_iff] at h_find
          specialize h_find r r_in_list
          dsimp [test] at h_find
          rw [r_has_id] at h_find
          simp at h_find
      impossible.elim

def lookup₄ {α : Type} [BEq α] [LawfulBEq α] {β : Type} (kvs : List (α × β)) (k : α) (h : k ∈ kvs.map Prod.fst) : Nat :=
  lookup₃ Prod.fst kvs k h


end Leioscrypto
