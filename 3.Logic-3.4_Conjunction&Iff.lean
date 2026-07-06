import Mathlib.Tactic
--3.Logic
--3.4 Conjunction and Iff
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]
----------------------------------------------------
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩
----------------------------------------------------
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  exact ⟨h₀, h⟩
----------------------------------------------------
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁
----------------------------------------------------
example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')
----------------------------------------------------
example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')
----------------------------------------------------
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁
----------------------------------------------------
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁
----------------------------------------------------
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁
----------------------------------------------------
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  match h with
  | ⟨h₀, h₁⟩ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁
----------------------------------------------------
example (x y : ℝ) (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'
----------------------------------------------------
example (x y : ℝ) (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')
----------------------------------------------------
example (m n : ℕ) (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬ n ∣ m := by
  rcases h with ⟨h1, h2⟩
  constructor
  · exact h1
  · intro h3
    apply h2
    exact Nat.dvd_antisymm h1 h3
----------------------------------------------------
example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩
----------------------------------------------------
example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty
----------------------------------------------------
example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty
----------------------------------------------------
example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num
----------------------------------------------------
example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num
----------------------------------------------------
example (x y : ℝ) : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x := by
  rintro ⟨h0, h1⟩
  constructor
  · use h0
  · exact fun h' ↦ h1 (le_antisymm h0 h')
----------------------------------------------------
example (x y : ℝ) (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  · contrapose!
    exact le_antisymm h
----------------------------------------------------
example (x y : ℝ) (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
  ⟨fun h0 h1 ↦ h0 (by rw [h1]), fun h0 h1 ↦ h0 (le_antisymm h h1)⟩
----------------------------------------------------
example (x y : ℝ) : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · exact h1
    · intro h3
      apply h2
      rw [h3]
  · rintro ⟨h1, h2⟩
    constructor
    · exact h1
    · intro h3
      apply h2
      exact le_antisymm h1 h3
----------------------------------------------------
theorem aux (x y : ℝ) (h : x^2 + y^2 = 0) : x = 0 := by
  have h' : x^2 ≤ 0 := by
    have hy : 0 ≤ y^2 := pow_two_nonneg y
    linarith
  have h'' : 0 ≤ x^2 := pow_two_nonneg x
  have h''' : x^2 = 0 := by linarith
  exact eq_zero_of_pow_eq_zero h'''
----------------------------------------------------
example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hx : x ^ 2 ≥ 0 := sq_nonneg x
    have hy : y ^ 2 ≥ 0 := sq_nonneg y
    have hx0 : x ^ 2 = 0 := by nlinarith
    have hy0 : y ^ 2 = 0 := by nlinarith
    constructor
    · exact sq_eq_zero_iff.mp hx0
    · exact sq_eq_zero_iff.mp hy0
  · rintro ⟨rfl, rfl⟩
    ring
----------------------------------------------------
example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith
----------------------------------------------------
example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num
----------------------------------------------------
example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · exact aux x y h
    · 
      have h_symm : y^2 + x^2 = 0 := by linarith
      exact aux y x h_symm
  · rintro ⟨rfl, rfl⟩
    norm_num
----------------------------------------------------
theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl
----------------------------------------------------
example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff]
  use 0, 1
  norm_num
----------------------------------------------------
variable {α : Type*} [PartialOrder α]
variable (a b : α)
----------------------------------------------------
example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_and_ne]
---------------------------------------------------- 
variable {α : Type*} [Preorder α]
variable (a b c : α)
----------------------------------------------------
example : ¬ a < a := by
  sorry
----------------------------------------------------
example : a < b → b < c → a < c := by
  sorry
----------------------------------------------------

