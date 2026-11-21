import MathGenome.Internal.Specs.D05.M13.AdjointKernel
import MathGenome.Internal.Specs.D05.M14.LeastSquares
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
Independent statements for K05.14.normal_equations, paper.tex:2518–2526.
The spaces are finite dimensional over R or C, represented uniformly by RCLike,
with no positive-dimension assumption. The adjoint is the shared canonical
LinearMap.adjoint, whose first-slot-linear convention bridge is upstream.
A residual minimizer is a global minimum over all vectors of the domain.

The expression Ring.inverse A is Mathlib's total ring inverse. Its two-sided
inverse identities are asserted below only after deriving IsUnit A from
injectivity of T. The invertibility equivalence also states the singular case.
No inverse or minimizer certificate is an assumption.
-/

noncomputable section

namespace Specs.D05.M14.NormalEquations

/-- A vector minimizes the residual norm exactly when its residual is killed by the adjoint. -/
def minimizer_iff_normal_equation : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W) (v : V),
    (∀ u : V, ‖T v - w‖ ≤ ‖T u - w‖) ↔
      LinearMap.adjoint T (T v - w) = 0

/-- The Gram endomorphism is invertible exactly in the injective case; otherwise it is singular. -/
def gram_isUnit_iff_injective : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    IsUnit ((LinearMap.adjoint T).comp T) ↔ Function.Injective T

/-- Under injectivity the inverse in the formula is an actual two-sided linear inverse. -/
def gram_inverse_identities : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    Function.Injective T →
      (Ring.inverse ((LinearMap.adjoint T).comp T)).comp
          ((LinearMap.adjoint T).comp T) = LinearMap.id ∧
      ((LinearMap.adjoint T).comp T).comp
          (Ring.inverse ((LinearMap.adjoint T).comp T)) = LinearMap.id

/-- For injective T the displayed inverse formula characterizes all minimizers, in both directions. -/
def minimizer_iff_inverse_formula : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    Function.Injective T → ∀ (w : W) (v : V),
      (∀ u : V, ‖T v - w‖ ≤ ‖T u - w‖) ↔
        v = Ring.inverse ((LinearMap.adjoint T).comp T) (LinearMap.adjoint T w)

/-- For every right-hand side an injective T has exactly one residual minimizer. -/
def exists_unique_injective_minimizer : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    Function.Injective T → ∀ w : W,
      ∃! v : V, ∀ u : V, ‖T v - w‖ ≤ ‖T u - w‖

end Specs.D05.M14.NormalEquations
