import Mathlib.Tactic
--9.Linear Algebra
--9.2 Subspaces and quotients
--9.2.1 Subspaces
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-----------------------------------------------------------
example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
  x + y ∈ U :=
  U.add_mem hx hy
-----------------------------------------------------------
example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
  a • x ∈ U :=
  U.smul_mem a hx
-----------------------------------------------------------
noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    use c * a
    simp
-----------------------------------------------------------
def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
  Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    sorry
-----------------------------------------------------------
example (U : Submodule K V) : Module K U := inferInstance
-----------------------------------------------------------
example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance
-----------------------------------------------------------
