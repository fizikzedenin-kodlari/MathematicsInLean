import Mathlib.Tactic
--3.Logic
--3.1 Implication and the Universal Quantifier
variable {f g : ℝ → ℝ} (a b : ℝ)
#check ∀ x : ℝ, 0 ≤ x → |x| = x
-----------------------------------------------
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε
-----------------------------------------------
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  sorry
-----------------------------------------------
section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end
-----------------------------------------------
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  sorry
-----------------------------------------------
section
variable (a b δ : ℝ)
variable (h0 : 0 < δ) (h1 : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h0 h1 ha hb
end
-----------------------------------------------
theorem my_lemma3 :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry
-----------------------------------------------
theorem my_lemma4:
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * ε       := mul_le_mul_of_nonneg_left (le_of_lt ylt) (abs_nonneg x)
    _ < 1 * ε         := sorry
    _ = ε             := one_mul ε
-----------------------------------------------
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a
-----------------------------------------------
def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x
-----------------------------------------------
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  · apply hfa
  · apply hgb
-----------------------------------------------
example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  apply mul_nonneg
  · apply nnf
  · apply nng
-----------------------------------------------
example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  dsimp
  apply mul_le_mul
  · apply hfa
  · apply hgb
  · apply nng
  · apply nna
-----------------------------------------------
variable {α : Type*} 

#check add_le_add

def FnUb' (f : α → ℝ ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → ℝ} {a b : ℝ} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)
-----------------------------------------------
example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h
-----------------------------------------------
example (c : ℝ) (mf : Monotone f) (nnc : 0 ≤ c) : Monotone (fun x ↦ c * f x) := by
  intro a b aleb
  dsimp
  apply mul_le_mul_of_nonneg_left
  · apply mf aleb
  · exact nnc
-----------------------------------------------
example (mf : Monotone f) (mg : Monotone g) : Monotone (fun x ↦ f (g x)) := by
  intro a b aleb
  dsimp
  apply mf
  apply mg aleb
-----------------------------------------------
def FnEven (f : ℝ → ℝ) : Prop := 
  ∀ x, f x = f (-x) 
-----------------------------------------------
def FnOdd (f : ℝ → ℝ) : Prop :=  
  ∀ x, f x = - f (-x)
-----------------------------------------------
example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]
-----------------------------------------------
example (of : FnOdd f) (og : FnOdd g) : FnEven (fun x ↦ f x * g x) := by
  intro x
  dsimp
  rw [of x, og x]
  ring
-----------------------------------------------
example (ef : FnEven f) (og : FnOdd g) : FnOdd (fun x ↦ f x * g x) := by
  intro x
  dsimp
  rw [ef x, og x]
  ring
-----------------------------------------------
example (ef : FnEven f) (og : FnOdd g) : FnEven (fun x ↦ f (g x)) := by
  sorry
-----------------------------------------------
variable {α : Type*} (r s t : Set α)
theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro hrs hst x hxr
  apply hst
  apply hrs
  exact hxr
-----------------------------------------------
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a


example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x hxs
  dsimp [SetUb] at h
  have hxa : x ≤ a := h x hxs
  exact le_trans hxa h'
-----------------------------------------------
open Function

example {c : ℝ} (h : c ≠ 0) : Injective (fun x ↦ c * x) := by
  intro x₁ x₂ h'
  dsimp at h'
  exact (mul_right_inj' h).mp h'
-----------------------------------------------
variable {α : Type*} {β : Type*} {γ : Type*}
variable (g : β → γ) (f : α → β)

example (injg : Injective g) (injf : Injective f) : Injective (fun x ↦ g (f x)) := by
  intro x₁ x₂ h
  dsimp at h
  apply injf
  apply injg
  exact h
-----------------------------------------------

