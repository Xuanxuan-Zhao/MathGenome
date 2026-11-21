import MathGenome.Internal.Specs.D05.M14.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Independent statements for K05.14.positive_spectrum (paper.tex:2400–2414).
The zero-quadratic corollary is allocated to its own downstream goal.
All predicates use the shared first-slot-linear inner product and the original
self-adjointness requirement. Eigenvalues range over the scalar field, and their
reality is a conclusion. No nontriviality hypothesis is imposed on the spaces. -/

namespace Specs.D05.M14.PositiveSpectrum

universe u v w

/-- Self-adjoint eigenvalues are real, so inequalities on their real parts express
exactly the inequalities in the source, for both real and complex scalars. -/
def eigenvalues_real : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.selfAdjoint T → ∀ μ : F, Module.End.HasEigenvalue T μ →
      (RCLike.re μ : F) = μ

def semidefinite_iff_eigenvalues : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.selfAdjoint T →
      (_root_.D05.positiveSemidefinite T ↔
        ∀ μ : F, Module.End.HasEigenvalue T μ → 0 ≤ RCLike.re μ)

def definite_iff_eigenvalues : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.selfAdjoint T →
      (_root_.D05.positiveDefinite T ↔
        ∀ μ : F, Module.End.HasEigenvalue T μ → 0 < RCLike.re μ)

/-- Rectangular maps have positive Gram operators. -/
def adjoint_comp_positive : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (R : V →ₗ[F] W),
    _root_.D05.positiveSemidefinite ((LinearMap.adjoint R).comp R)

def adjoint_comp_quadratic : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (R : V →ₗ[F] W) (v : V),
    _root_.D05.firstInner (F := F) (((LinearMap.adjoint R).comp R) v) v =
      (‖R v‖ ^ 2 : ℝ)

/-- The factor can always be chosen on the same space. No prescribed arbitrary
codomain is required to have sufficient dimension. -/
def semidefinite_iff_factorization : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.positiveSemidefinite T ↔
      ∃ R : V →ₗ[F] V, T = (LinearMap.adjoint R).comp R

/-- `IsUnit` in the endomorphism ring is ordinary linear invertibility. -/
def definite_iff_invertible : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.positiveSemidefinite T →
      (_root_.D05.positiveDefinite T ↔ IsUnit T)

end Specs.D05.M14.PositiveSpectrum
