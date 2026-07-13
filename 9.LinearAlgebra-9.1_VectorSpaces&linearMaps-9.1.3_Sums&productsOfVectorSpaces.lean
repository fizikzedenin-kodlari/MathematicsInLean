import Mathlib.Tactic
--9.Linear Algebra
--9.1 Vector spaces and linear maps
--9.1.3 Sums and products of vector spaces
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable  {W : Type*} [AddCommGroup W] [Module K W]
-----------------------------------------------------------
section binary_product
-----------------------------------------------------------
variable {W : Type*} [AddCommGroup W] [Module K W]
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {T : Type*} [AddCommGroup T] [Module K T]
-----------------------------------------------------------
-- First projection map
example : V × W →ₗ[K] V := LinearMap.fst K V W
-----------------------------------------------------------
-- Second projection map
example : V × W →ₗ[K] W := LinearMap.snd K V W
-----------------------------------------------------------
-- Universal property of the product
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : U →ₗ[K]  V × W := LinearMap.prod φ ψ
-----------------------------------------------------------
-- The product map does the expected thing, first component
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.fst K V W ∘ₗ LinearMap.prod φ ψ = φ := rfl
-----------------------------------------------------------
-- The product map does the expected thing, second component
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.snd K V W ∘ₗ LinearMap.prod φ ψ = ψ := rfl
-----------------------------------------------------------
-- We can also combine maps in parallel
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) : (V × W) →ₗ[K] (U × T) := φ.prodMap ψ
-----------------------------------------------------------
-- This is simply done by combining the projections with the universal property
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) :
  φ.prodMap ψ = (φ ∘ₗ .fst K V W).prod (ψ ∘ₗ .snd K V W) := rfl
-----------------------------------------------------------
-- First inclusion map
example : V →ₗ[K] V × W := LinearMap.inl K V W
-----------------------------------------------------------
-- Second inclusion map
example : W →ₗ[K] V × W := LinearMap.inr K V W
-----------------------------------------------------------
-- Universal property of the sum (aka coproduct)
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : V × W →ₗ[K] U := φ.coprod ψ
-----------------------------------------------------------
-- The coproduct map does the expected thing, first component
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inl K V W = φ :=
  LinearMap.coprod_inl φ ψ
-----------------------------------------------------------
-- The coproduct map does the expected thing, second component
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inr K V W = ψ :=
  LinearMap.coprod_inr φ ψ
-----------------------------------------------------------
-- The coproduct map is defined in the expected way
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) (v : V) (w : W) :
  φ.coprod ψ (v, w) = φ v + ψ w :=
  rfl
-----------------------------------------------------------
end binary_product
-----------------------------------------------------------
section families
-----------------------------------------------------------
open DirectSum
-----------------------------------------------------------
variable {ι : Type*} [DecidableEq ι]
         (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
-----------------------------------------------------------
-- The universal property of the direct sum assembles maps from the summands to build
-- a map from the direct sum
example (φ : Π i, (V i →ₗ[K] W)) : (⨁ i, V i) →ₗ[K] W :=
DirectSum.toModule K ι W φ
-----------------------------------------------------------
-- The universal property of the direct product assembles maps into the factors
-- to build a map into the direct product
example (φ : Π i, (W →ₗ[K] V i)) : W →ₗ[K] (Π i, V i) :=
  LinearMap.pi φ
-----------------------------------------------------------
-- The projection maps from the product
example (i : ι) : (Π j, V j) →ₗ[K] V i := LinearMap.proj i
-----------------------------------------------------------
-- The inclusion maps into the sum
example (i : ι) : V i →ₗ[K] (⨁i, V i) := DirectSum.lof K ι V i
-----------------------------------------------------------
-- The inclusion maps into the product
example (i : ι) : V i →ₗ[K] (Π i, V i) := LinearMap.single K V i
-----------------------------------------------------------
-- In case `ι` is a finite type, there is an isomorphism between the sum and product.
example [Fintype ι] : (⨁ i, V i) ≃ₗ[K] (Π i, V i) :=
  linearEquivFunOnFintype K ι V
-----------------------------------------------------------
end families
-----------------------------------------------------------
