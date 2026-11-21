import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Independent statement of `d04:04:inverse-function`. Ambient functions
represent maps on the displayed open sets. The shared recursive `CrOn` and
`SmoothOn` are used, so finite regularity is not replaced by smoothness.
Linear equivalences express invertibility; in finite dimension all are
continuous. No positive-dimension hypothesis is imposed. -/
noncomputable section
open Set
open scoped NNReal
namespace Specs.D04.C04.InverseFunction
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

/-- The common geometric, differential, uniqueness, and Lipschitz conclusions.
The last equivalence gives uniqueness for every solution with values in X,
and therefore also for any competing local inverse taking values in X. -/
def InverseNeighborhood {n : ℕ} (U : Set (E n)) (f : E n → E n) (a : E n)
    (X Y : Set (E n)) (g : E n → E n) : Prop :=
  IsOpen X ∧ IsOpen Y ∧ a ∈ X ∧ f a ∈ Y ∧ X ⊆ U ∧
  BijOn f X Y ∧ MapsTo g Y X ∧ LeftInvOn g f X ∧ RightInvOn g f Y ∧
  (∀ x ∈ X, ∃ B : E n ≃L[ℝ] E n,
    B.toContinuousLinearMap = totalDerivative f x) ∧
  (∀ y ∈ Y, ∃ B : E n ≃L[ℝ] E n,
    B.toContinuousLinearMap = totalDerivative f (g y) ∧
    HasTotalDerivative Y g B.symm.toContinuousLinearMap y ∧
    totalDerivative g y = B.symm.toContinuousLinearMap) ∧
  (∃ K : ℝ≥0, LipschitzOnWith K g Y) ∧
  (∀ y ∈ Y, ∀ x ∈ X, f x = y ↔ x = g y)

def inverse_function_finiteType : Prop :=
  ∀ {n : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → E n) (a : E n)
    (A : E n ≃ₗ[ℝ] E n),
    1 ≤ r → IsOpen U → CrOn r U f → a ∈ U →
    A.toContinuousLinearEquiv.toContinuousLinearMap = totalDerivative f a →
    ∃ X Y g, InverseNeighborhood U f a X Y g ∧ CrOn r Y g

def inverse_function_smoothType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → E n) (a : E n)
    (A : E n ≃ₗ[ℝ] E n),
    IsOpen U → SmoothOn U f → a ∈ U →
    A.toContinuousLinearEquiv.toContinuousLinearMap = totalDerivative f a →
    ∃ X Y g, InverseNeighborhood U f a X Y g ∧ SmoothOn Y g

/-- Full ball conclusion, including the lower bound on the entire ball,
existence and uniqueness for every admissible target, interior membership,
and the anisotropic inverse estimate for every pair of solutions. -/
def inverse_function_quantitativeType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → E n) (a : E n)
    (A : E n ≃ₗ[ℝ] E n) (ρ q : ℝ),
    IsOpen U → CrOn 1 U f → a ∈ U →
    A.toContinuousLinearEquiv.toContinuousLinearMap = totalDerivative f a →
    0 < ρ → Metric.closedBall a ρ ⊆ U → q < 1 →
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

end Specs.D04.C04.InverseFunction
