import Mathlib.Tactic
--9.Linear Algebra
--9.2. Subspaces and quotients
--9.2.3 Bir küme tarafından gerilen alt uzay (Subspace spanned by a set)
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-----------------------------------------------------------
example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le
-----------------------------------------------------------
example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
  Submodule.gi K V
-----------------------------------------------------------
example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  induction h using Submodule.span_induction with
  | mem x hx => sorry
  | zero => sorry
  | add x y hx hy ihx ihy => sorry
  | smul c x hx ihx => sorry
--**Since the "apply" line was causing an error here, I replaced it with the line starting with "induction".**
----------------------------------------------------------- 


