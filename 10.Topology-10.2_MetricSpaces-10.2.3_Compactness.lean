import Mathlib.Tactic
--10.Topology
--10.2 Metric spaces
--10.2.3 Compactness
variable {X : Type*} [MetricSpace X] 
--------------------------------------------------------
example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc
--------------------------------------------------------
example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

--**This code has the bugs. I'll update it once I fix them.**
--------------------------------------------------------
example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
    (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_isMinOn hs' hfs
--------------------------------------------------------
example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
    (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_isMaxOn hs' hfs
--------------------------------------------------------
example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed
--------------------------------------------------------
example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ
--------------------------------------------------------