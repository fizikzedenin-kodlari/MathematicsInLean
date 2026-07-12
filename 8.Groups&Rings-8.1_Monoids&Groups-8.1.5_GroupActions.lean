import Mathlib.Tactic
--8.Groups&Rings
--8.1 Monoids and Groups
--8.1.5 Group actions
noncomputable section GroupActions
---------------------------------------------------------------
example {G X : Type*} [Group G] [MulAction G X] (g g' : G) (x : X) :
  g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm
---------------------------------------------------------------
example {G X : Type*} [AddGroup G] [AddAction G X] (g g' : G) (x : X) :
  g +ᵥ (g' +ᵥ x) = (g + g') +ᵥ x :=
  (add_vadd g g' x).symm
---------------------------------------------------------------
open MulAction
---------------------------------------------------------------
example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  toPermHom G X
---------------------------------------------------------------
----**I'll update it after I fix the bugs in the code.**-------------
def CayleyIsomorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G
---------------------------------------------------------------
example {G X : Type*} [Group G] [MulAction G X] : Setoid X := orbitRel G X
---------------------------------------------------------------
example {G X : Type*} [Group G] [MulAction G X] :
  X ≃ (w : orbitRel.Quotient G X) × (orbit G (Quotient.out w)) :=
MulAction.selfEquivSigmaOrbits G X
---------------------------------------------------------------
example {G X : Type*} [Group G] [MulAction G X] (x : X) :
  orbit G x ≃ G ⧸ stabilizer G x :=
MulAction.orbitEquivQuotientStabilizer G x
---------------------------------------------------------------
example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  groupEquivQuotientProdSubgroup
---------------------------------------------------------------
variable {G : Type*} [Group G]
---------------------------------------------------------------
lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  sorry
---------------------------------------------------------------
instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
    sorry
  mul_smul := by
    sorry
---------------------------------------------------------------
end GroupActions
---------------------------------------------------------------