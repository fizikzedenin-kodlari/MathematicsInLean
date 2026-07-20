import Mathlib.Tactic
--10.Topology
--10.2 Metric spaces
--10.2.4 Uniformly continuous functions
example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
  UniformContinuous f ↔
    ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
Metric.uniformContinuous_iff
--------------------------------------------------------
example {X : Type*} [MetricSpace X] [CompactSpace X]
  {Y : Type*} [MetricSpace Y] {f : X → Y}
  (hf : Continuous f) : UniformContinuous f :=
sorry
--------------------------------------------------------