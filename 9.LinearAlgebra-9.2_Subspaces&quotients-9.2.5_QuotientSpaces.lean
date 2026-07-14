import Mathlib.Tactic
--9.Linear Algebra
--9.2 Subspaces and quotients
--9.2.5 Quotient spaces
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-----------------------------------------------------------
variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)
-----------------------------------------------------------
variable (E : Submodule K V) 
-----------------------------------------------------------
open LinearMap
-----------------------------------------------------------
example : Module K (V ⧸ E) := inferInstance
-----------------------------------------------------------
example : V →ₗ[K] V ⧸ E := E.mkQ
-----------------------------------------------------------
example : ker E.mkQ = E := E.ker_mkQ
-----------------------------------------------------------
example : range E.mkQ = ⊤ := E.range_mkQ
-----------------------------------------------------------
example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ
-----------------------------------------------------------
example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ
-----------------------------------------------------------
noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange
-----------------------------------------------------------
open Submodule
-----------------------------------------------------------
#check Submodule.map_comap_eq
-----------------------------------------------------------
#check Submodule.comap_map_eq
-----------------------------------------------------------
example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
-----------------------------------------------------------


