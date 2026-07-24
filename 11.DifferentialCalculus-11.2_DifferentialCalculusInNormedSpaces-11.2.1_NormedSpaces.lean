import Mathlib.Tactic
--11.Differential Calculus
--11.2 Differential Calculus in Normed Spaces
--11.2.1 Normed spaces
variable {E : Type*} [NormedAddCommGroup E]
-----------------------------------------------------------
example (x : E) : 0 ≤ ‖x‖ :=
  norm_nonneg x
-----------------------------------------------------------
example {x : E} : ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero
-----------------------------------------------------------
example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y
-----------------------------------------------------------
example : MetricSpace E := by infer_instance
-----------------------------------------------------------
example {X : Type*} [TopologicalSpace X] {f : X → E} (hf : Continuous f) :
    Continuous fun x ↦ ‖f x‖ :=
  hf.norm
-----------------------------------------------------------
variable [NormedSpace ℝ E]
-----------------------------------------------------------
example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
  norm_smul a x
-----------------------------------------------------------
example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance
-----------------------------------------------------------
example (K : Type*) [NontriviallyNormedField K] (x y : K) : ‖x * y‖ = ‖x‖ * ‖y‖ :=
  norm_mul x y
-----------------------------------------------------------
example (K : Type*) [NontriviallyNormedField K] : ∃ x : K, 1 < ‖x‖ :=
  NormedField.exists_one_lt_norm K
-----------------------------------------------------------
example (K : Type*) [NontriviallyNormedField K] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace K E] [CompleteSpace K] [FiniteDimensional K E] : CompleteSpace E :=
  FiniteDimensional.complete K E
-----------------------------------------------------------
--**This code has the bugs. I'll update it once I fix them.**