import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! Independent statements of P206 W28 (paper.tex, least squares and the normal
 equations). Both spaces are arbitrary finite-dimensional real or complex
 inner-product spaces. No positive dimension, rank, or injectivity is imposed
 for the characterization or existence. The inverse is the total ring inverse;
 its actual two-sided inverse identities are asserted under injectivity. -/
noncomputable section

namespace Specs.NumAnalysis206.NormalEquations

universe u v w

def minimizer_iff_normal_equation : Prop :=
  ∀ {K : Type u} {E : Type v} {F : Type w} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E]
    [NormedAddCommGroup F] [InnerProductSpace K F]
    [FiniteDimensional K E] [FiniteDimensional K F] (A : E →ₗ[K] F) (b : F) (x : E),
    (∀ y : E, ‖A x - b‖ ≤ ‖A y - b‖) ↔
      LinearMap.adjoint A (A x - b) = 0

def exists_minimizer : Prop :=
  ∀ {K : Type u} {E : Type v} {F : Type w} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E]
    [NormedAddCommGroup F] [InnerProductSpace K F]
    [FiniteDimensional K E] [FiniteDimensional K F] (A : E →ₗ[K] F) (b : F),
    ∃ x : E, ∀ y : E, ‖A x - b‖ ≤ ‖A y - b‖

def gram_isUnit_of_injective : Prop :=
  ∀ {K : Type u} {E : Type v} {F : Type w} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E]
    [NormedAddCommGroup F] [InnerProductSpace K F]
    [FiniteDimensional K E] [FiniteDimensional K F] (A : E →ₗ[K] F),
    Function.Injective A → IsUnit ((LinearMap.adjoint A).comp A)

def gram_inverse_identities : Prop :=
  ∀ {K : Type u} {E : Type v} {F : Type w} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E]
    [NormedAddCommGroup F] [InnerProductSpace K F]
    [FiniteDimensional K E] [FiniteDimensional K F] (A : E →ₗ[K] F),
    Function.Injective A →
      (Ring.inverse ((LinearMap.adjoint A).comp A)).comp
        ((LinearMap.adjoint A).comp A) = LinearMap.id ∧
      ((LinearMap.adjoint A).comp A).comp
        (Ring.inverse ((LinearMap.adjoint A).comp A)) = LinearMap.id

def minimizer_iff_inverse_formula : Prop :=
  ∀ {K : Type u} {E : Type v} {F : Type w} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E]
    [NormedAddCommGroup F] [InnerProductSpace K F]
    [FiniteDimensional K E] [FiniteDimensional K F] (A : E →ₗ[K] F),
    Function.Injective A → ∀ (b : F) (x : E),
      (∀ y : E, ‖A x - b‖ ≤ ‖A y - b‖) ↔
        x = Ring.inverse ((LinearMap.adjoint A).comp A) (LinearMap.adjoint A b)

def exists_unique_injective_minimizer : Prop :=
  ∀ {K : Type u} {E : Type v} {F : Type w} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E]
    [NormedAddCommGroup F] [InnerProductSpace K F]
    [FiniteDimensional K E] [FiniteDimensional K F] (A : E →ₗ[K] F),
    Function.Injective A → ∀ b : F,
      ∃! x : E, ∀ y : E, ‖A x - b‖ ≤ ‖A y - b‖

end Specs.NumAnalysis206.NormalEquations
