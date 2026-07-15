import Mathlib.Tactic
--9.Linear Algebra
--9.3 Endomorphisms
@[expose] public section
universe u v w
namespace Module
namespace End
open Module Set
variable {K R : Type v} {V M : Type w} [CommRing R] [AddCommGroup M] [Module R M] [Field K]
  [AddCommGroup V] [Module K V]
def genEigenspace (f : End R M) (μ : R) : ℕ∞ →o Submodule R M where
  toFun k := ⨆ l : ℕ, ⨆ _ : l ≤ k, LinearMap.ker ((f - μ • 1) ^ l)
  monotone' _ _ hkl := biSup_mono fun _ hi ↦ hi.trans hkl
abbrev eigenspace (f : End R M) (μ : R) : Submodule R M :=
  f.genEigenspace μ 1
def HasUnifEigenvalue (f : End R M) (μ : R) (k : ℕ∞) : Prop :=
  f.genEigenspace μ k ≠ ⊥
abbrev HasEigenvalue (f : End R M) (a : R) : Prop :=
  HasUnifEigenvalue f a 1
def HasUnifEigenvector (f : End R M) (μ : R) (k : ℕ∞) (x : M) : Prop :=
  x ∈ f.genEigenspace μ k ∧ x ≠ 0
abbrev HasEigenvector (f : End R M) (μ : R) (x : M) : Prop :=
  HasUnifEigenvector f μ 1 x
def UnifEigenvalues (f : End R M) (k : ℕ∞) : Type _ :=
  { μ : R // f.HasUnifEigenvalue μ k }
abbrev Eigenvalues (f : End R M) : Type _ :=
  UnifEigenvalues f 1
theorem HasEigenvalue.exists_hasEigenvector {f : End R M} {μ : R} (hμ : f.HasEigenvalue μ) :
    ∃ v, f.HasEigenvector μ v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ
lemma HasUnifEigenvector.hasUnifEigenvalue {f : End R M} {μ : R} {k : ℕ∞} {x : M}
    (h : f.HasUnifEigenvector μ k x) : f.HasUnifEigenvalue μ k := by
  rw [HasUnifEigenvalue, Submodule.ne_bot_iff]
  use x; exact h
theorem hasEigenvalue_of_hasEigenvector {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) :
    HasEigenvalue f μ :=
  h.hasUnifEigenvalue
--**I added the lines of code above to be able to run code containing 'eigen'.**
--**from: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/Eigenspace/Basic.lean**
--**I couldn't find a shorter way. If anyone does, let me know: leanonmath@gmail.com**
-----------------------------------------------------------
variable {W : Type*} [AddCommGroup W] [Module K W]
-----------------------------------------------------------
open Polynomial Module LinearMap
---------------------------------------------------------
example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ := 
  LinearMap.mul_eq_comp φ ψ -- `rfl` would also work
-----------------------------------------------------------
-- evaluating `P` on `φ`
noncomputable example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P
-----------------------------------------------------------
-- evaluating `X` on `φ` gives back `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ
-----------------------------------------------------------
#check Submodule.eq_bot_iff
-----------------------------------------------------------
#check Submodule.mem_inf
-----------------------------------------------------------
#check LinearMap.mem_ker
-----------------------------------------------------------
example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
  sorry
-----------------------------------------------------------
#check Submodule.add_mem_sup
-----------------------------------------------------------
#check map_mul
-----------------------------------------------------------
#check LinearMap.mul'_apply
-----------------------------------------------------------
#check LinearMap.ker_le_ker_comp
-----------------------------------------------------------
example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
  sorry
-----------------------------------------------------------
example (a : K) : algebraMap K (End K V) a = a • LinearMap.id := rfl
----------------------------------------------------------- 
example (φ : End K V) (a : K) :
    (φ).eigenspace a = LinearMap.ker (φ - algebraMap K (End K V) a) :=
  rfl
-----------------------------------------------------------
example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl
-----------------------------------------------------------
example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩
-----------------------------------------------------------
example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl
-----------------------------------------------------------
--**This code has the bugs. I'll update it once I fix them.**
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue
-----------------------------------------------------------
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.haseigenvalue_iff_isRoot
-----------------------------------------------------------
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly
-----------------------------------------------------------