import Mathlib.Tactic
--9.Linear Algebra
--9.2 Subspaces and quotients
--9.2.2 Complete lattice structure and internal direct sums
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-----------------------------------------------------------
example (H H' : Submodule K V) :
  ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl
-----------------------------------------------------------
example (H H' : Submodule K V) :
  ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]
-----------------------------------------------------------
example (x : V) : x ∈ (⊤ : Submodule K V) := trivial
-----------------------------------------------------------
example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K
-----------------------------------------------------------
-- If two subspaces are in direct sum then they span the whole space.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top
-----------------------------------------------------------
-- If two subspaces are in direct sum then they intersect only at zero.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot
-----------------------------------------------------------
section
-----------------------------------------------------------
open DirectSum
-----------------------------------------------------------
variable {ι : Type*} [DecidableEq ι]
-----------------------------------------------------------
-- If subspaces are in direct sum then they span the whole space.
example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top
-----------------------------------------------------------
-- If subspaces are in direct sum then they pairwise intersect only at zero.
example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
  {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  (h.submodule_independent.pairwiseDisjoint hij).eq_bot
--**This code has the bugs. I'll update it once I fix them.**
-----------------------------------------------------------
-- Those conditions characterize direct sums.
#check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top
-----------------------------------------------------------
-- The relation with external direct sums: if a family of subspaces is
-- in internal direct sum then the map from their external direct sum into `V`
-- is a linear isomorphism.
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
  (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coeLinearMap U) h
-----------------------------------------------------------
end
-----------------------------------------------------------

