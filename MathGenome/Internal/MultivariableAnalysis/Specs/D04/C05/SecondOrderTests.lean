import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ExtremaInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.Symmetry

/-! Independent pointwise second-order tests (d04:05:second-order).
The shared recursive differentiability predicate requires existence of first
derivatives near a and differentiability of the derivative at a; it does not
require continuous second derivatives nearby. The Hessian quadratic form is
the diagonal of the shared second differential. -/
noncomputable section
open Set
namespace Specs.D04.C05.SecondOrderTests
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
open Specs.D04.C03.Symmetry.Model
open Specs.D04.C05.ExtremaInterfaces.Model

def secondOrder_minimumType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TimesDifferentiableAt 2 U f a → LocalMinimumOn U f a →
    totalDerivative f a = 0 ∧ ∀ v, 0 ≤ differentialDiagonal (higherDifferential 2 f a) v

def secondOrder_maximumType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TimesDifferentiableAt 2 U f a → LocalMaximumOn U f a →
    totalDerivative f a = 0 ∧ ∀ v, differentialDiagonal (higherDifferential 2 f a) v ≤ 0

/-- The estimate is valid also in dimension zero, where every increment is zero. -/
def secondOrder_positiveType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TimesDifferentiableAt 2 U f a → totalDerivative f a = 0 →
    (∀ v, v ≠ 0 → 0 < differentialDiagonal (higherDifferential 2 f a) v) →
    StrictLocalMinimumOn U f a ∧
    ∃ c > 0, ∃ ρ > 0, ∀ h, ‖h‖ < ρ →
      a + h ∈ U ∧ f a + c * ‖h‖ ^ 2 ≤ f (a + h)

def secondOrder_negativeType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TimesDifferentiableAt 2 U f a → totalDerivative f a = 0 →
    (∀ v, v ≠ 0 → differentialDiagonal (higherDifferential 2 f a) v < 0) →
    StrictLocalMaximumOn U f a ∧
    ∃ c > 0, ∃ ρ > 0, ∀ h, ‖h‖ < ρ →
      a + h ∈ U ∧ f (a + h) ≤ f a - c * ‖h‖ ^ 2

/-- No stationarity assumption is imposed in the saddle criterion. -/
def secondOrder_indefiniteType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TimesDifferentiableAt 2 U f a →
    (∃ u, 0 < differentialDiagonal (higherDifferential 2 f a) u) →
    (∃ v, differentialDiagonal (higherDifferential 2 f a) v < 0) → SaddlePoint U f a

def secondOrder_dimension_zeroType : Prop :=
  ∀ (U : Set (E 0)) (f : E 0 → ℝ) (a : E 0), a ∈ U →
    StrictLocalMinimumOn U f a ∧ StrictLocalMaximumOn U f a ∧
    ∀ (c : ℝ) (h : E 0), f (a+h) = f a + c * ‖h‖ ^ 2

/-- The literal one-coordinate polynomials, with their common zero Hessian. -/
def zeroHessian_examplesType : Prop :=
  let f : E 1 → ℝ := fun x => (x 0)^4
  let g : E 1 → ℝ := fun x => -(x 0)^4
  let k : E 1 → ℝ := fun x => (x 0)^3
  TimesDifferentiableAt 2 univ f 0 ∧ TimesDifferentiableAt 2 univ g 0 ∧
  TimesDifferentiableAt 2 univ k 0 ∧
  hessian f 0 = 0 ∧ hessian g 0 = 0 ∧ hessian k 0 = 0 ∧
  StrictLocalMinimumOn univ f 0 ∧ StrictLocalMaximumOn univ g 0 ∧ SaddlePoint univ k 0

/-- The common nonzero positive semidefinite Hessian is displayed entrywise.
The third example has a local minimum which is not strict. -/
def semidefiniteHessian_examplesType : Prop :=
  let f : E 2 → ℝ := fun x => (x 0)^2 + (x 1)^4
  let g : E 2 → ℝ := fun x => (x 0)^2 - (x 1)^4
  let k : E 2 → ℝ := fun x => (x 0)^2
  TimesDifferentiableAt 2 univ f 0 ∧ TimesDifferentiableAt 2 univ g 0 ∧
  TimesDifferentiableAt 2 univ k 0 ∧
  hessian f 0 = !![2, 0; 0, 0] ∧ hessian g 0 = !![2, 0; 0, 0] ∧
  hessian k 0 = !![2, 0; 0, 0] ∧
  hessian k 0 ≠ 0 ∧
  (∀ v, 0 ≤ differentialDiagonal (higherDifferential 2 k 0) v) ∧
  (∃ v, v ≠ 0 ∧ differentialDiagonal (higherDifferential 2 k 0) v = 0) ∧
  StrictLocalMinimumOn univ f 0 ∧ SaddlePoint univ g 0 ∧
  LocalMinimumOn univ k 0 ∧ ¬ StrictLocalMinimumOn univ k 0

end Specs.D04.C05.SecondOrderTests
