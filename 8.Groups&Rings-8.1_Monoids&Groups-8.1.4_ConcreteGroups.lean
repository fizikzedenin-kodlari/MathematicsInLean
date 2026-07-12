import Mathlib.Tactic
--8.Groups&Rings
--8.1 Monoids and Groups
--8.1.4 Concrete groups
open Equiv
---------------------------------------------------------------
example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
  Perm.closure_isCycle
----**I'll update it after I fix the bugs in the code.**-------------
#simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]  
---------------------------------------------------------------
section FreeGroup
---------------------------------------------------------------
inductive S | a | b | c
---------------------------------------------------------------
open S
---------------------------------------------------------------
def myElement : FreeGroup S := (.of a) * (.of b)⁻¹
---------------------------------------------------------------
def myMorphism : FreeGroup S →* Perm (Fin 5) :=
  FreeGroup.lift fun | .a => c[1, 2, 3]
                     | .b => c[2, 3, 1]
                     | .c => c[2, 3]
---------------------------------------------------------------
def myGroup := PresentedGroup {.of () ^ 3} deriving Group
---------------------------------------------------------------
def myMap : Unit → Equiv.Perm (Fin 5)
  | () => c[1, 2, 3]
---------------------------------------------------------------
lemma compat_myMap :
  ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by
  rintro _ rfl
  simp
  decide
---------------------------------------------------------------
def myNewMorphism : myGroup →* Equiv.Perm (Fin 5) := PresentedGroup.toGroup compat_myMap
---------------------------------------------------------------
end FreeGroup
---------------------------------------------------------------
