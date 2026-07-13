import Mathlib.Tactic
--8.Groups&Rings
--8.2 Rings
--8.2.1 Rings, their units, morphisms and subrings
example {R : Type*} [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y :=
  by ring
---------------------------------------------------------------
example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring
---------------------------------------------------------------
example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x
---------------------------------------------------------------
example {M : Type*} [Monoid M] (x : Mˣ) : (x : M) * x⁻¹ = 1 := Units.mul_inv x
---------------------------------------------------------------
example {M : Type*} [Monoid M] : Group Mˣ := inferInstance
---------------------------------------------------------------
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
  f (x + y) = f x + f y := f.map_add x y
---------------------------------------------------------------
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : Rˣ →* Sˣ :=
  Units.map f
---------------------------------------------------------------
example {R : Type*} [Ring R] (S : Subring R) : Ring S := inferInstance
---------------------------------------------------------------
