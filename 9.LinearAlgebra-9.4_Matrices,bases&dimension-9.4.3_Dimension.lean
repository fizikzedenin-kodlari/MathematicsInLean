import Mathlib.Tactic
--9.Linear Algebra
--9.4 Matrices, bases and dimension
--9.4.3 Dimension
variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
--------------------------------------------------------
open Module
--------------------------------------------------------
section
--------------------------------------------------------
#check (Module.finrank K V : ℕ)
--------------------------------------------------------
-- `Fin n → K` is the archetypical space with dimension `n` over `K`.
example (n : ℕ) : Module.finrank K (Fin n → K) = n :=
  Module.finrank_fin_fun K
--------------------------------------------------------
-- Seen as a vector space over itself, `ℂ` has dimension one.
example : Module.finrank ℂ ℂ = 1 :=
  Module.finrank_self ℂ
--------------------------------------------------------
-- But as a real vector space it has dimension two.
example : Module.finrank ℝ ℂ = 2 :=
  Submodule.finrank_real_complex
--**This code has the bugs. I'll update it once I fix them.**
--------------------------------------------------------
example [FiniteDimensional K V] : 0 < Module.finrank K V ↔ Nontrivial V :=
  Module.finrank_pos_iff
--------------------------------------------------------
example [FiniteDimensional K V] (h : 0 < Module.finrank K V) : Nontrivial V := by
  apply (Module.finrank_pos_iff (R := K)).1
  exact h
--------------------------------------------------------
variable {ι : Type*} (B : Basis ι K V)
--------------------------------------------------------
example [Finite ι] : FiniteDimensional K V := FiniteDimensional.of_fintype_basis B
--------------------------------------------------------
example [FiniteDimensional K V] : Finite ι :=
  (FiniteDimensional.fintypeBasisIndex B).finite
end
--------------------------------------------------------
section
--------------------------------------------------------
variable (E F : Submodule K V) [FiniteDimensional K V]
--------------------------------------------------------
example : finrank K (E ⊔ F : Submodule K V) + finrank K (E ⊓ F : Submodule K V) =
    finrank K E + finrank K F :=
  Submodule.finrank_sup_add_finrank_inf_eq E F
--------------------------------------------------------
example : finrank K E ≤ finrank K V := Submodule.finrank_le E
--------------------------------------------------------
example (h : finrank K V < finrank K E + finrank K F) :
  Nontrivial (E ⊓ F : Submodule K V) := by
  sorry
--------------------------------------------------------
end
--------------------------------------------------------
#check V -- Type u_2
--------------------------------------------------------
#check Module.rank K V -- Cardinal.{u_2}
--------------------------------------------------------
universe u v
--------------------------------------------------------
variable {ι : Type u} (B : Basis ι K V)
--------------------------------------------------------
variable {ι' : Type v} (B' : Basis ι' K V)
--------------------------------------------------------
example : Cardinal.lift.{v, u} (.mk ι) = Cardinal.lift.{u, v} (.mk ι') :=
  mk_eq_mk_of_basis B B'
--------------------------------------------------------
example [FiniteDimensional K V] :
  (Module.finrank K V : Cardinal) = Module.rank K V :=
  Module.finrank_eq_rank K V
--------------------------------------------------------