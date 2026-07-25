import Mathlib
--12.Integration and Measure Theory
--12.2 Measure Theory
variable {α : Type*} [MeasurableSpace α]
-----------------------------------------------------------
example : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty
-----------------------------------------------------------
open Set
-----------------------------------------------------------
example : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ
-----------------------------------------------------------
example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl
-----------------------------------------------------------
example : Encodable ℕ := by infer_instance
-----------------------------------------------------------
example (n : ℕ) : Encodable (Fin n) := by infer_instance
-----------------------------------------------------------
variable {ι : Type*} [Encodable ι]
-----------------------------------------------------------
example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h
-----------------------------------------------------------
example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.iInter h
-----------------------------------------------------------