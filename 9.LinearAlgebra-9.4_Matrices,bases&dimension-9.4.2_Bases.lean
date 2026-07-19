import Mathlib.Tactic
--9.Linear Algebra
--9.4 Matrices, bases and dimension
--9.4.2 Bases
variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
--------------------------------------------------------
section
--------------------------------------------------------
open Module 
--------------------------------------------------------
variable (ι : Type*) (B : Basis ι K V) (v : V) (i : ι)
--------------------------------------------------------
-- The basis vector with index ``i``
#check (B i : V)
--------------------------------------------------------
-- the linear isomorphism with the model space given by ``B``
#check (B.repr : V ≃ₗ[K] ι →₀ K)
--------------------------------------------------------
-- the component function of ``v``
#check (B.repr v : ι →₀ K)
--------------------------------------------------------
-- the component of ``v`` with index ``i``
#check (B.repr v i : K)
--------------------------------------------------------
noncomputable example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
  Basis.mk b_indep (fun v _ ↦ b_spans v)
--------------------------------------------------------
-- The family of vectors underlying the above basis is indeed ``b``.
example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) (i : ι) :
    Basis.mk b_indep (fun v _ ↦ b_spans v) i = b i :=
  Basis.mk_apply b_indep (fun v _ ↦ b_spans v) i
--------------------------------------------------------
variable [DecidableEq ι]
--------------------------------------------------------
example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl
--------------------------------------------------------
example (i : ι) : Finsupp.basisSingleOne i = Finsupp.single i 1 :=
  rfl
--------------------------------------------------------
example [Finite ι] (x : ι → K) (i : ι) : (Pi.basisFun K ι).repr x i = x i := by
  simp
--------------------------------------------------------
example [Fintype ι] : ∑ i : ι, B.repr v i • (B i) = v :=
  B.sum_repr v
--------------------------------------------------------
example (c : ι →₀ K) (f : ι → V) (s : Finset ι) (h : c.support ⊆ s) :
    Finsupp.linearCombination K f c = ∑ i ∈ s, c i • f i :=
  Finsupp.linearCombination_apply_of_mem_supported K h
--------------------------------------------------------
example : Finsupp.linearCombination K B (B.repr v) = v :=
  B.linearCombination_repr v
--------------------------------------------------------
variable (f : ι → V) in
--------------------------------------------------------
#check (Finsupp.linearCombination K f : (ι →₀ K) →ₗ[K] V)
--------------------------------------------------------
section
--------------------------------------------------------
variable {W : Type*} [AddCommGroup W] [Module K W]
  (φ : V →ₗ[K] W) (u : ι → W)
--------------------------------------------------------
#check (B.constr K : (ι → W) ≃ₗ[K] (V →ₗ[K] W))
--------------------------------------------------------
#check (B.constr K u : V →ₗ[K] W)
--------------------------------------------------------
example (i : ι) : B.constr K u (B i) = u i :=
  B.constr_basis K u i
--------------------------------------------------------
example (φ ψ : V →ₗ[K] W) (h : ∀ i, φ (B i) = ψ (B i)) : φ = ψ :=
  B.ext h
--------------------------------------------------------
variable {ι' : Type*} (B' : Basis ι' K W) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
--------------------------------------------------------
open LinearMap
--------------------------------------------------------
#check (toMatrix B B' : (V →ₗ[K] W) ≃ₗ[K] Matrix ι' ι K)
--------------------------------------------------------
open Matrix -- get access to the ``*ᵥ`` notation for multiplication between matrices and vectors.
--------------------------------------------------------
example (φ : V →ₗ[K] W) (v : V) : (toMatrix B B' φ) *ᵥ (B.repr v) = B'.repr (φ v) :=
  toMatrix_mulVec_repr B B' φ v
--------------------------------------------------------
variable {ι'' : Type*} (B'' : Basis ι'' K W) [Fintype ι''] [DecidableEq ι'']
--------------------------------------------------------
example (φ : V →ₗ[K] W) : (toMatrix B B'' φ) = (toMatrix B' B'' .id) * (toMatrix B B' φ) := by
  simp
--------------------------------------------------------
end
--------------------------------------------------------

open Module LinearMap Matrix

---- Some lemmas coming from the fact that `LinearMap.toMatrix` is an algebra morphism.
#check toMatrix_comp
#check id_comp
#check comp_id
#check toMatrix_id

-- Some lemmas coming from the fact that ``Matrix.det`` is a multiplicative monoid morphism.

#check Matrix.det_mul
#check Matrix.det_one

example [Fintype ι] (B' : Basis ι K V) (φ : End K V) :
    (toMatrix B B φ).det = (toMatrix B' B' φ).det := by
  set M := toMatrix B B φ
  set M' := toMatrix B' B' φ
  set P := (toMatrix B B') LinearMap.id
  set P' := (toMatrix B' B) LinearMap.id
  sorry
end