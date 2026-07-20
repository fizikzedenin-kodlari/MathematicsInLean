import Mathlib.Tactic
--10.Topology
--10.2 Metric spaces
--10.2.5 Completeness
variable {X : Type*} [MetricSpace X] 
--------------------------------------------------------
example (u : ℕ → X) :
  CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
Metric.cauchySeq_iff
--------------------------------------------------------
example (u : ℕ → X) :
  CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
Metric.cauchySeq_iff'
--------------------------------------------------------
open Filter Topology
example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
  ∃ x, Tendsto u atTop (𝓝 x) :=
cauchySeq_tendsto_of_complete hu
--**This code has the bugs. I'll update it once I fix them.**
--------------------------------------------------------
open Set
--------------------------------------------------------
theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
  (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by sorry
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := sorry
    _ ≤ ∑ i ∈ range k, dist (u (N + i)) (u (N + (i + 1))) := sorry
    _ ≤ ∑ i ∈ range k, (1 / 2 : ℝ) ^ (N + i) := sorry
    _ = 1 / 2 ^ N * ∑ i ∈ range k, (1 / 2 : ℝ) ^ i := sorry
    _ ≤ 1 / 2 ^ N * 2 := sorry
    _ < ε := sorry
--------------------------------------------------------
open Metric
--------------------------------------------------------
example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
  Dense (∩ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n
  sorry
  /- Translate the density assumption into two functions `center` and `radius`
     associating to any n, x, δ, δpos a center and a positive radius such that
     `closedBall center radius` is included both in `f n` and in `closedBall x δ`.
     We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence
     later. -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
  by sorry
  choose! center radius Hpos HB Hball using this
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x`
     belonging to all `f n`. For this, we construct inductively a sequence
     `F n = (c n, r n)` such that the closed ball `closedBall (c n) (r n)` is included
     in the previous ball and in `f n`, and such that `r n` is small enough to ensure
     that `c n` is a Cauchy sequence. Then `c n` converges to a limit which belongs
     to all the `f n`. -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by sorry
  have rB : ∀ n, r n ≤ B n := by sorry
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    sorry
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by sorry
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by sorry
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by sorry
  sorry 
--------------------------------------------------------
