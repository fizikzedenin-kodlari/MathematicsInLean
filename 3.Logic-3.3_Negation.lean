import Mathlib.Tactic
--3.Logic
--3.3 Negation
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (a b : ℝ){f : ℝ → ℝ}
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this
--------------------------------------
example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith
--------------------------------------
example (h : ∀ a, ∃ x, f x < a) : ¬ FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≥ a := fnlba x
  linarith
--------------------------------------
example : ¬ FnHasUb fun x ↦ x := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  have : a + 1 ≤ a := fnuba (a + 1)
  linarith
--------------------------------------
#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)
--------------------------------------
example (h : Monotone f) (h' : f a < f b) : a < b := by
  by_contra hnot
  push_neg at hnot
  have : f b ≤ f a := h hnot
  linarith
--------------------------------------
example (h : a ≤ b) (h' : f b < f a) : ¬ Monotone f := by
  intro hmono
  have : f a ≤ f b := hmono h
  linarith
--------------------------------------
example : ¬ ∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro x y hxy
    rfl
  have h' : f 1 ≤ f 0 := le_rfl
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith
--------------------------------------
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra hgt
  push_neg at hgt
  have hx := h x hgt
  linarith
--------------------------------------
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬ ∃ x, P x) : ∀ x, ¬ P x := by
  intro x hPx
  apply h
  use x
--------------------------------------
example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x := by
  intro h_exists
  rcases h_exists with ⟨x, hPx⟩
  exact h x hPx
--------------------------------------
example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  exact h' ⟨x, h''⟩
--------------------------------------
example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x := by
  intro h_forall
  rcases h with ⟨x, hnPx⟩
  exact hnPx (h_forall x)
--------------------------------------
example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'
--------------------------------------
example (h : Q) : ¬¬Q := by
  intro h'
  exact h' h
--------------------------------------
variable (f : ℝ → ℝ)

example (h : ¬ FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  by_contra h''
  apply h'
  use x
  push_neg at h''
  exact h''
--------------------------------------
example (h : ¬ ∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h
--------------------------------------
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h
--------------------------------------
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp [Monotone] at h
  push_neg at h
  exact h
--------------------------------------
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h
--------------------------------------
example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith
--------------------------------------
example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h
--------------------------------------
example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)
--------------------------------------
example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction
--------------------------------------