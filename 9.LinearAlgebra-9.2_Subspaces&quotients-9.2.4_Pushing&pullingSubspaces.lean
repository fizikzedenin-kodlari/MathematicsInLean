import Mathlib.Tactic
--9.Linear Algebra
--9.2. Subspaces and quotients
--9.2.4 Pushing and pulling subspaces
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-----------------------------------------------------------
section
-----------------------------------------------------------
variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)
-----------------------------------------------------------
variable (E : Submodule K V) in
-----------------------------------------------------------
#check (Submodule.map φ E : Submodule K W)
-----------------------------------------------------------
variable (F : Submodule K W) in
-----------------------------------------------------------
#check (Submodule.comap φ F : Submodule K V)
-----------------------------------------------------------
example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ
-----------------------------------------------------------
example : LinearMap.ker φ = .comap φ ⊥ := Submodule.comap_bot φ  -- or `rfl`
-----------------------------------------------------------
open Function LinearMap
-----------------------------------------------------------
example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm
-----------------------------------------------------------
example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm
-----------------------------------------------------------
#check Submodule.mem_map_of_mem
-----------------------------------------------------------
#check Submodule.mem_map
-----------------------------------------------------------
#check Submodule.mem_comap
-----------------------------------------------------------
example (E : Submodule K V) (F : Submodule K W) :
  Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
  sorry
-----------------------------------------------------------

