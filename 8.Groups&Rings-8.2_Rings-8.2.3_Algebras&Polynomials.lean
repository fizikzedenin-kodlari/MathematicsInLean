import Mathlib.Tactic
--8.Groups&Rings
--8.2 Rings
--8.2.3 Algebras and polynomials
example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
  (r + r') • a = r • a + r' • a :=
  add_smul r r' a
---------------------------------------------------------------
example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
  (r * r') • a = r • (r' • a) :=
  mul_smul r r' a
---------------------------------------------------------------
open Polynomial
---------------------------------------------------------------
noncomputable example {R : Type*} [CommRing R] : R[X] := X
---------------------------------------------------------------
noncomputable example {R : Type*} [CommRing R] (r : R) := X - C r
---------------------------------------------------------------
example {R : Type*} [CommRing R] (r : R) : (X + C r) * (X - C r) = X ^ 2 - C (r ^ 2) :=
  by
  rw [C.map_pow]
  ring
---------------------------------------------------------------
example {R : Type*} [CommRing R] (r : R) : (C r).coeff 0 = r := by simp
---------------------------------------------------------------
example {R : Type*} [CommRing R] : (X ^ 2 + 2 * X + C 3 : R[X]).coeff 1 = 2 := by simp
---------------------------------------------------------------
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    degree (p * q) = degree p + degree q :=
  Polynomial.degree_mul
---------------------------------------------------------------
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  Polynomial.natDegree_mul hp hq
---------------------------------------------------------------
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    natDegree (comp p q) = natDegree p * natDegree q :=
  Polynomial.natDegree_comp
---------------------------------------------------------------
example {R : Type*} [CommRing R] (P : R[X]) (x : R) := P.eval x
---------------------------------------------------------------
example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp
---------------------------------------------------------------
example {R : Type*} [CommRing R] (P : R[X]) (r : R) : IsRoot P r ↔ P.eval r = 0 :=
  Iff.rfl
---------------------------------------------------------------
example {R : Type*} [CommRing R] [IsDomain R] (r : R) : (X - C r).roots = {r} :=
  roots_X_sub_C r
---------------------------------------------------------------
example {R : Type*} [CommRing R] [IsDomain R] (r : R) (n : ℕ) :
    ((X - C r) ^ n).roots = n • {r} :=
  by simp
---------------------------------------------------------------
example : aeval Complex.I (X ^ 2 + 1 : ℝ[X]) = 0 := by simp
---------------------------------------------------------------
open Complex Polynomial
---------------------------------------------------------------
example : aroots (X ^ 2 + 1 : ℝ[X]) ℂ = {Complex.I, -I} := by
  suffices roots (X ^ 2 + 1 : ℂ[X]) = {I, -I} by simpa [aroots_def]
  have factored : (X ^ 2 + 1 : ℂ[X]) = (X - C I) * (X - C (-I)) := by
    have key : (C I * C I : ℂ[X]) = -1 := by simp [← C_mul]
    rw [C_neg]
    linear_combination key
  have p_ne_zero : (X - C I) * (X - C (-I)) ≠ 0 := by
    intro H
    apply_fun eval 0 at H
    simp [eval] at H
  simp only [factored, roots_mul p_ne_zero, roots_X_sub_C]
  rfl
---------------------------------------------------------------
-- Mathlib knows about D'Alembert-Gauss theorem: ``ℂ`` is algebraically closed.
example : IsAlgClosed ℂ := inferInstance
---------------------------------------------------------------
#check (Complex.ofReal : ℝ → ℂ)
---------------------------------------------------------------
example : (X ^ 2 + 1 : ℝ[X]).eval₂ Complex.ofReal Complex.I = 0 := by simp
----**I'll update it after I fix the bug in the code.**-------------
---------------------------------------------------------------
open MvPolynomial
---------------------------------------------------------------
noncomputable def circleEquation : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2 - 1
---------------------------------------------------------------
example : MvPolynomial.eval ![0, 1] circleEquation = 0 := by simp [circleEquation]
---------------------------------------------------------------