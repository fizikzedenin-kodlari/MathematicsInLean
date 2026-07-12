import Mathlib.Tactic
--8.Groups&Rings
--8.1 Monoids and Groups
--8.1.1 Monoids and their morphisms
example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x
---------------------------------------------------------------
example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y
---------------------------------------------------------------
example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y
---------------------------------------------------------------
example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero
---------------------------------------------------------------
example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
(f : M →+ N) (g : N →+ P) : M →+ P := g.comp f
---------------------------------------------------------------
