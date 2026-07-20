import Mathlib.Tactic
--10.Topology
--10.2 Metric spaces
--10.2.2 Balls, open sets and closed sets
variable (r a b: ℝ)
--------------------------------------------------------
example : Metric.ball a r = { b | dist b a < r } :=
  rfl
--------------------------------------------------------
example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl
--------------------------------------------------------
example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr
--------------------------------------------------------
example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr
  --------------------------------------------------------
variable {X : Type*} [MetricSpace X] (a c : X)
--------------------------------------------------------
example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff
--------------------------------------------------------
example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm
--------------------------------------------------------
open Filter Topology
--------------------------------------------------------
example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝒩 a))
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (Eventually.of_forall hus)
--**This code has the bugs. I'll update it once I fix them.**
--------------------------------------------------------
example {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff
--------------------------------------------------------
-- Do the next exercise without using mem_closure_iff_seq_limit
example {u : ℕ → X} (hu : Tendsto u atTop (𝒩 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ closure s :=
  sorry
--------------------------------------------------------
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff
--------------------------------------------------------
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff
--------------------------------------------------------
