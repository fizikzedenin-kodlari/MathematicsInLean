import Mathlib.Tactic
--9.Linear Algebra
--9.1 Vector spaces and linear maps
--9.1.1 Vector spaces
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-----------------------------------------------------------
example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v
-----------------------------------------------------------
example (a b : K) (u : V) : (a + b) • u = a • u + b • u :=
  add_smul a b u
-----------------------------------------------------------
example (a b : K) (u : V) : a • b • u = b • a • u :=
  smul_comm a b u
-----------------------------------------------------------
example {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] :
  Module (Ideal R) (Submodule R M) :=
inferInstance
-----------------------------------------------------------
