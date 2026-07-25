import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
--11.Differential Calculus
--11.2 Differential Calculus in Normed Spaces
--11.2.4 Differentiability
open Topology
-----------------------------------------------------------
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
-----------------------------------------------------------
example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔ (fun x ↦ f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] fun x ↦ x - x₀ :=
  hasFDerivAt_iff_isLittleO
-----------------------------------------------------------
example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) : fderiv 
    𝕜 f x₀ = f' :=
  hff'.fderiv
-----------------------------------------------------------
noncomputable example (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
  iteratedFDeriv 𝕜 n f
-----------------------------------------------------------
example (n : ℕ∞) (f : E → F) :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, (m : ℕ∞) ≤ n → Continuous fun x ↦ iteratedFDeriv 𝕜 m f x) ∧
      (∀ m : ℕ, (m : ℕ∞) < n → Differentiable 𝕜 fun x ↦ iteratedFDeriv 𝕜 m
        f x) :=
  contDiff_iff_continuous_differentiable
-----------------------------------------------------------
example {𝕂 : Type*} [RCLike 𝕂] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕂 F] {f : E → F} {x : E} {n : ℕ∞}
  (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) : HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.hasStrictFDerivAt hn
--**This code has the bug. I'll update it once I fix them.**
-----------------------------------------------------------
section LocalInverse
-----------------------------------------------------------
variable [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
-----------------------------------------------------------
noncomputable example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) : F → E :=
  HasStrictFDerivAt.localInverse f f' a hf
-----------------------------------------------------------
example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
  ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  hf.eventually_left_inverse
-----------------------------------------------------------
example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
  ∀ᶠ x in 𝓝 (f a), f (hf.localInverse f f' a x) = x :=
  hf.eventually_right_inverse
-----------------------------------------------------------
example {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
  (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
  HasStrictFDerivAt (HasStrictFDerivAt.localInverse f f' a hf) (f'.symm : F →L[𝕜] E) (f a) :=
  HasStrictFDerivAt.to_localInverse hf
-----------------------------------------------------------
end LocalInverse
-----------------------------------------------------------