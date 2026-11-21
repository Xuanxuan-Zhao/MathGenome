import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent specification of the quantitative existence stage of
`d04:04:inverse-function`. Ambient extensions represent functions on the open
set U, as in the shared derivative interface. A linear equivalence packages
invertibility of Df(a); its inverse is continuous by finite dimension.
All norms are the shared Euclidean and operator norms. No dimension is excluded.
-/
noncomputable section
open Set
namespace Specs.D04.C04.QuantitativeInverseBall
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

/-- Existence and uniqueness in the closed ball, interior membership, the
lower bound and injectivity on the whole closed ball, and the inverse estimate
for every pair of admissible target values and their solutions. -/
def quantitative_inverse_ballType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → E n) (a : E n)
    (A : E n ≃ₗ[ℝ] E n) (ρ q : ℝ),
    IsOpen U → CrOn 1 U f → a ∈ U →
    A.toContinuousLinearEquiv.toContinuousLinearMap = totalDerivative f a →
    0 < ρ → Metric.closedBall a ρ ⊆ U → 0 ≤ q → q < 1 →
    (∀ x ∈ Metric.closedBall a ρ,
      ‖ContinuousLinearMap.id ℝ (E n) -
        A.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (totalDerivative f x)‖ ≤ q) →
    (∀ x ∈ Metric.closedBall a ρ, ∀ z ∈ Metric.closedBall a ρ,
      (1 - q) * ‖x - z‖ ≤ ‖A.symm (f x - f z)‖) ∧
    InjOn f (Metric.closedBall a ρ) ∧
    (∀ y : E n, ‖A.symm (y - f a)‖ < (1 - q) * ρ →
      ∃! x : E n, x ∈ Metric.closedBall a ρ ∧ f x = y) ∧
    (∀ y : E n, ‖A.symm (y - f a)‖ < (1 - q) * ρ →
      ∀ x ∈ Metric.closedBall a ρ, f x = y → x ∈ Metric.ball a ρ) ∧
    (∀ y z : E n,
      ‖A.symm (y - f a)‖ < (1 - q) * ρ →
      ‖A.symm (z - f a)‖ < (1 - q) * ρ →
      ∀ x_y ∈ Metric.closedBall a ρ, ∀ x_z ∈ Metric.closedBall a ρ,
        f x_y = y → f x_z = z →
        ‖x_y - x_z‖ ≤ ‖A.symm (y - z)‖ / (1 - q))

end Specs.D04.C04.QuantitativeInverseBall
