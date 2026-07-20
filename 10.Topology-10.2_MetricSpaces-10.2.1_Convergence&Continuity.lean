import Mathlib.Tactic
--10.Topology
--10.2 Metric spaces
variable {X : Type*} [MetricSpace X] (a b c : X)
--------------------------------------------------------
#check (dist a b : ℝ)
--------------------------------------------------------
#check (dist_nonneg : 0 ≤ dist a b)
--------------------------------------------------------
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
--------------------------------------------------------
#check (dist_comm a b : dist a b = dist b a)
--------------------------------------------------------
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)
--------------------------------------------------------
--10.2.1 Convergence and continuity
--------------------------------------------------------
open Filter Topology
--**This code has the bugs. I'll update it once I fix them.**
example {u : ℕ → X} {a : X} :
  Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
Metric.tendsto_atTop
--------------------------------------------------------
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
  Continuous f ↔
    ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
Metric.continuous_iff
--------------------------------------------------------
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
  Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity
--------------------------------------------------------
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous (fun p : X × X ↦ dist (f p.1) (f p.2)) :=
  continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))
--------------------------------------------------------
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
  Continuous (fun p : X × X => dist (f p.1) (f p.2)) := by
  apply Continuous.dist
  exact hf.comp continuous_fst
  exact hf.comp continuous_snd
--------------------------------------------------------
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
  Continuous (fun p : X × X => dist (f p.1) (f p.2)) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)
--------------------------------------------------------
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
  Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'
--------------------------------------------------------
example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
  sorry
--------------------------------------------------------
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
  ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
Metric.continuousAt_iff
--------------------------------------------------------
