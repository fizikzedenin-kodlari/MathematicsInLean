import Mathlib.Tactic
--10.Topology
--10.3 Topological spaces
--10.3.1 Fundamentals
open Set
--------------------------------------------------------
section
--------------------------------------------------------
variable {X : Type*} [TopologicalSpace X]
--------------------------------------------------------
example : IsOpen (univ : Set X) :=
  isOpen_univ
--------------------------------------------------------
example : IsOpen (∅ : Set X) :=
  isOpen_empty
--------------------------------------------------------
example {ι : Type*} {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) : IsOpen (⋃ i, s i) :=
  isOpen_iUnion hs
--------------------------------------------------------
example {ι : Type*} [Fintype ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) :
    IsOpen (⋂ i, s i) :=
  isOpen_iInter_of_finite hs
--------------------------------------------------------
variable {Y : Type*} [TopologicalSpace Y]
--------------------------------------------------------
example {f : X → Y} : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def
--------------------------------------------------------
open Topology Filter
--------------------------------------------------------
example {f : X → Y} {x : X} : ContinuousAt f x ↔ map f (𝓝 x) ≤ 𝓝 (f x) :=
  Iff.rfl
--------------------------------------------------------
example {f : X → Y} {x : X} : ContinuousAt f x ↔ ∀ U ∈ 𝓝 (f x), ∀ᶠ x in 𝓝 x, f x ∈ U :=
  Iff.rfl
--------------------------------------------------------
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff
--------------------------------------------------------
example (x : X) : pure x ≤ 𝓝 x :=
  pure_le_nhds x
--------------------------------------------------------
example (x : X) (P : X → Prop) (h : ∀ᶠ y in 𝓝 x, P y) : P x :=
  h.self_of_nhds
--------------------------------------------------------
example {P : X → Prop} {x : X} (h : ∀ᶠ y in 𝓝 x, P y) : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z :=
  eventually_eventually_nhds.mpr h
--------------------------------------------------------
example {α : Type*} (n : α → Filter α) (H₀ : ∀ a, pure a ≤ n a)
  (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → ∀ᶠ y in n a, ∀ᶠ x in n y, p x) :
  ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' :=
sorry
--------------------------------------------------------
variable {X Y : Type*}
--------------------------------------------------------
example (f : X → Y) : TopologicalSpace X → TopologicalSpace Y :=
  TopologicalSpace.coinduced f
--------------------------------------------------------
example (f : X → Y) : TopologicalSpace Y → TopologicalSpace X :=
  TopologicalSpace.induced f
--------------------------------------------------------
example (f : X → Y) (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) :
    TopologicalSpace.coinduced f T_X ≤ T_Y ↔ T_X ≤ TopologicalSpace.induced f T_Y :=
  coinduced_le_iff_le_induced
--------------------------------------------------------
example {T T' : TopologicalSpace X} : T ≤ T' ↔ ∀ s, T'.IsOpen s → T.IsOpen s :=
  Iff.rfl
--------------------------------------------------------
example (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) (f : X → Y) :
    Continuous f ↔ TopologicalSpace.coinduced f T_X ≤ T_Y :=
  continuous_iff_coinduced_le
--------------------------------------------------------
example {Z : Type*} (f : X → Y) (T_X : TopologicalSpace X) (T_Z : TopologicalSpace Z)
    (g : Y → Z) :
    @Continuous Y Z (TopologicalSpace.coinduced f T_X) T_Z g ↔
      @Continuous X Z T_X T_Z (g ∘ f) := by
  rw [continuous_iff_coinduced_le, coinduced_compose, continuous_iff_coinduced_le]
--------------------------------------------------------
example (ι : Type*) (X : ι → Type*) (T_X : ∀ i, TopologicalSpace (X i)) :
  (Pi.topologicalSpace : TopologicalSpace (∀ i, X i)) =
    ⨅ i, TopologicalSpace.induced (fun x ↦ x i) (T_X i) :=
rfl
--------------------------------------------------------

