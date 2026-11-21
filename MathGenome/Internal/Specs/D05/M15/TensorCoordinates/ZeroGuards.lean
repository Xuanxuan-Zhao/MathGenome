import MathGenome.Internal.Specs.D05.M15.TensorCoordinates.TraceDeterminant

/-!
Independent statements for K05.15.tensor_coordinates, paper.tex:2761.
`IsUnit` in the endomorphism ring means existence of a two-sided linear inverse.
The arbitrary-map assertions have no dimension restriction. Only the converse
uses nonzero domain spaces. The finite-dimensional invertibility criterion
states positivity of both factor dimensions explicitly.
-/
namespace Specs.D05.M15.TensorCoordinates.ZeroGuards

open scoped TensorProduct

/-- Tensoring injective maps preserves injectivity, including zero domains. -/
def injective_tensor : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    Function.Injective S → Function.Injective T →
      Function.Injective (TensorProduct.map S T)

/-- Both domains must be nonzero for this converse; codomains are arbitrary. -/
def injective_factors : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [Nontrivial V] [Nontrivial W] (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    Function.Injective (TensorProduct.map S T) →
      Function.Injective S ∧ Function.Injective T

/-- The two arbitrary-dimensional assertions combined under the converse's guards. -/
def injective_iff : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [Nontrivial V] [Nontrivial W] (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    Function.Injective (TensorProduct.map S T) ↔
      Function.Injective S ∧ Function.Injective T

/-- The paper's invertibility equivalence, with both dimensions positive. -/
def invertible_factors : Prop :=
  ∀ {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Module.End K V) (T : Module.End K W),
    0 < Module.finrank K V → 0 < Module.finrank K W →
      (IsUnit (TensorProduct.map S T) ↔ IsUnit S ∧ IsUnit T)

/-- With either dimension zero, every tensor endomorphism is invertible. -/
def zero_dimension_invertible : Prop :=
  ∀ {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Module.End K V) (T : Module.End K W),
    (Module.finrank K V = 0 ∨ Module.finrank K W = 0) →
      (∀ z : V ⊗[K] W, z = 0) ∧ IsUnit (TensorProduct.map S T)

/-- A zero domain factor makes every tensor map injective, in any dimension. -/
def zero_factor_injective : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    (Subsingleton V ∨ Subsingleton W) → Function.Injective (TensorProduct.map S T)

/-- Explicit failure of both unguarded converses when the left domain is zero.
The other factor is the nonzero one-dimensional scalar space. -/
def zero_left_counterexample : Prop :=
  ∀ {K : Type*} [Field K],
    ∃ (S : Module.End K (Fin 0 → K)) (T : Module.End K K),
      IsUnit (TensorProduct.map S T) ∧
      Function.Injective (TensorProduct.map S T) ∧ ¬IsUnit T ∧ ¬Function.Injective T

/-- The same failure when the right domain is zero. -/
def zero_right_counterexample : Prop :=
  ∀ {K : Type*} [Field K],
    ∃ (S : Module.End K K) (T : Module.End K (Fin 0 → K)),
      IsUnit (TensorProduct.map S T) ∧
      Function.Injective (TensorProduct.map S T) ∧ ¬IsUnit S ∧ ¬Function.Injective S

end Specs.D05.M15.TensorCoordinates.ZeroGuards
