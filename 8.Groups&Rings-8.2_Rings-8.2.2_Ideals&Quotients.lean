import Mathlib.Tactic
--8.Groups&Rings
--8.2 Rings
--8.2.2 Ideals and quotients
example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I
---------------------------------------------------------------
example {R : Type*} [CommRing R] {a : R} (I : Ideal R) :
  Ideal.Quotient.mk I a = 0 ↔ a ∈ I := Ideal.Quotient.eq_zero_iff_mem
---------------------------------------------------------------
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
  (H : I ≤ RingHom.ker f) : R ⧸ I →+* S := Ideal.Quotient.lift I f H
---------------------------------------------------------------
noncomputable example {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
  R ⧸ RingHom.ker f ≃+* f.range :=
RingHom.quotientKerEquivRange f
---------------------------------------------------------------
variable {R : Type*} [CommRing R] {I J : Ideal R}
---------------------------------------------------------------
example : I + J = I ⊔ J := rfl
---------------------------------------------------------------
example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  simp [Submodule.mem_sup]
---------------------------------------------------------------
example : I * J ≤ J := Ideal.mul_le_left
---------------------------------------------------------------
example : I * J ≤ I := Ideal.mul_le_right
---------------------------------------------------------------
example : I * J ≤ I ⊓ J := Ideal.mul_le_inf
---------------------------------------------------------------
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
  (H : I ≤ Ideal.comap f J) : R ⧸ I →+* S ⧸ J :=
  Ideal.quotientMap J f H
---------------------------------------------------------------
example {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  Ideal.quotEquivOfEq h
---------------------------------------------------------------
noncomputable example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (f : ι → Ideal R)
  (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+*  Π i , R ⧸ f i :=
Ideal.quotientInfRingEquivPiQuotient f hf
---------------------------------------------------------------
open BigOperators PiNotation
---------------------------------------------------------------
example {ι : Type*} [Fintype ι] (a : ι → ℕ) (coprime : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
  ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
  ZMod.prodEquivPi a coprime
----**I'll update it after I fix the bug in the code.**-------------
---------------------------------------------------------------
variable {ι R : Type*} [CommRing R]
---------------------------------------------------------------
open Ideal Quotient Function
---------------------------------------------------------------
#check Pi.ringHom
---------------------------------------------------------------
#check ker_Pi_Quotient_mk
---------------------------------------------------------------
/-- The homomorphism from ``R  ⨅ i, I i`` to ``Π i, R  I i`` featured in the Chinese
Remainder Theorem. -/
---------------------------------------------------------------
def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
  sorry
---------------------------------------------------------------
lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
    chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Ideal.Quotient.mk (I i) x :=
  sorry
---------------------------------------------------------------
lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
    chineseMap I (mk _ x) i = mk (I i) x :=
  sorry
---------------------------------------------------------------
#check injective_lift_iff
---------------------------------------------------------------
lemma chineseMap_inj (I : ι → Ideal R) : Injective (chineseMap I) := by
  sorry
---------------------------------------------------------------
#check IsCoprime
---------------------------------------------------------------
#check isCoprime_iff_add
---------------------------------------------------------------
#check isCoprime_iff_exists
---------------------------------------------------------------
#check isCoprime_iff_sup_eq
---------------------------------------------------------------
#check isCoprime_iff_codisjoint
---------------------------------------------------------------
#check Finset.mem_insert_of_mem
---------------------------------------------------------------
#check Finset.mem_insert_self
---------------------------------------------------------------
theorem isCoprime_Inf {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
  (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  induction s using Finset.induction with
  | empty =>
    simp
  | @insert i s _ hs =>
    rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
    set K := ⨅ j ∈ s, J j
    calc
      1 = I + K                  := sorry
      _ = I + K * (I + J i)      := sorry
      _ = (1 + K) * I + K * J i  := sorry
      _ ≤ I + K ⊓ J i            := sorry
---------------------------------------------------------------
lemma chineseMap_surj [Fintype ι] {I : ι → Ideal R}
  (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) : Surjective (chineseMap I) := by
  classical
  intro g
  choose f hf using fun i ↦ Ideal.Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
      sorry
    sorry
  choose e he using key
  use mk _ (∑ i, f i * e i)
  sorry
---------------------------------------------------------------
noncomputable def chineseIso [Fintype ι] (f : ι → Ideal R)
  (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Πi, R ⧸ f i :=
{ Equiv.ofBijective _ ⟨chineseMap_inj f, chineseMap_surj hf⟩,
  chineseMap f with }
---------------------------------------------------------------