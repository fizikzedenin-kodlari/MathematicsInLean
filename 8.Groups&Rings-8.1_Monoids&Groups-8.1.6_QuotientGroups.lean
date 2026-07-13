import Mathlib.Tactic
--8.Groups&Rings
--8.1 Monoids and Groups
--8.1.6 Quotient groups
noncomputable section QuotientGroup
---------------------------------------------------------------
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) :=
  inferInstance
---------------------------------------------------------------
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H
---------------------------------------------------------------
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
  [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  QuotientGroup.lift N φ h
---------------------------------------------------------------
example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
  G ⧸ MonoidHom.ker φ ≃* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ
---------------------------------------------------------------
example {G G' : Type*} [Group G] [Group G']
  {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
  (φ : G →* G') (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G' ⧸ N' :=
  QuotientGroup.map N N' φ h
---------------------------------------------------------------
example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
  [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq h
---------------------------------------------------------------
section
---------------------------------------------------------------
variable {G : Type*} [Group G] {H K : Subgroup G}
---------------------------------------------------------------
open MonoidHom
---------------------------------------------------------------
#check Nat.card_pos -- The nonempty argument will be automatically inferred for subgroups
---------------------------------------------------------------
#check Subgroup.index_eq_card
---------------------------------------------------------------
#check Subgroup.index_mul_card
---------------------------------------------------------------
#check Nat.eq_of_mul_eq_mul_right
---------------------------------------------------------------
lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
  Nat.card (G ⧸ H) = Nat.card K := by
  sorry
---------------------------------------------------------------
variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)
---------------------------------------------------------------
#check Nat.bijective_iff_injective_and_card
---------------------------------------------------------------
#check ker_eq_bot_iff
---------------------------------------------------------------
#check restrict
---------------------------------------------------------------
#check ker_restrict
---------------------------------------------------------------
def iso₁ [Fintype G] (h : Disjoint H K) (h' : Nat.card G = Nat.card H * Nat.card K) :
  K ≃* G ⧸ H := by
  sorry
---------------------------------------------------------------
def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
  sorry
---------------------------------------------------------------
#check MulEquiv.prodCongr
---------------------------------------------------------------
def finalIso : G ≃* H × K := by
  sorry
---------------------------------------------------------------