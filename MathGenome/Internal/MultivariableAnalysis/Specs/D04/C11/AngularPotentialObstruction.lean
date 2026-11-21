import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.LocalAndStarShapedPotentials
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.ClosedAndExactForms
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.OrientedEuclideanDictionary
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.CircleMultiplicity
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Independent statements for d04:11:angular-obstruction and d04:13:angular.
The field, circle, derivative, Riemann integral and form types are the shared
ones. A rotation parameter permits every removed ray. A branch is assumed only
continuous and to satisfy the polar representation, not to be differentiable. -/
noncomputable section
open Set
namespace Specs.D04.C11.AngularPotentialObstruction
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model
open Specs.D04.C09.CircleMultiplicity.Model
open Specs.D04.C11.PotentialPathIndependencePeriods.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C13.ClosedAndExactForms.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
namespace Model

/-- The work form (-y dx + x dy)/(x²+y²). -/
def angularForm : FormField 2 1 := alpha angularField

/-- Remove the ray of angle α+π, including the origin. -/
def angularSlit (α : ℝ) : Set (E 2) :=
  {x | Complex.exp (-(α : ℂ) * Complex.I) * complexCoordinates.symm x ∈ Complex.slitPlane}

/-- A single-valued angle with values between α-π and α+π on this slit. -/
def slitAngle (α : ℝ) (x : E 2) : ℝ :=
  α + Complex.arg (Complex.exp (-(α : ℂ) * Complex.I) * complexCoordinates.symm x)

/-- The polar identity uses exp(iθ)=cos θ+i sin θ. No derivative is assumed. -/
def IsAngleBranch (U : Set (E 2)) (a : E 2 → ℝ) : Prop :=
  ContinuousOn a U ∧ ∀ x ∈ U,
    (‖complexCoordinates.symm x‖ : ℂ) * Complex.exp ((a x : ℂ) * Complex.I) =
      complexCoordinates.symm x
end Model
open Model

abbrev angularFormType := FormField 2 1
def angularFormValue : angularFormType := angularForm
abbrev angularSlitType := ℝ → Set (E 2)
def angularSlitValue : angularSlitType := angularSlit
abbrev slitAngleType := ℝ → E 2 → ℝ
def slitAngleValue : slitAngleType := slitAngle
abbrev IsAngleBranchType := Set (E 2) → (E 2 → ℝ) → Prop
def IsAngleBranchValue : IsAngleBranchType := IsAngleBranch

def angularForm_applyType : Prop := ∀ (x : E 2) (v : Fin 1 → E 2),
  angularForm x v = (-x 1 * v 0 0 + x 0 * v 0 1) / ((x 0)^2 + (x 1)^2)
def angularField_smoothType : Prop := ∀ r : ℕ, CrOn r puncturedPlane angularField
def angularField_symmetricType : Prop := ∀ x ∈ puncturedPlane, (jacobian angularField x).IsSymm
def angularForm_closedType : Prop := IsClosedForm puncturedPlane angularForm
def angularField_local_potentialType : Prop := ∀ x ∈ puncturedPlane,
  ∃ r > 0, Metric.ball x r ⊆ puncturedPlane ∧ HasPotential (Metric.ball x r) angularField

def angularForm_locally_exactType : Prop := ∀ x ∈ puncturedPlane,
  ∃ r > 0, Metric.ball x r ⊆ puncturedPlane ∧ IsExactForm (Metric.ball x r) angularForm

def angular_circle_integralType : Prop :=
  ∀ d : PiecewiseC1Data (circlePath 1), ∃ h : WorkIntegrable d angularField,
    workLineIntegral d angularField h = 2 * Real.pi
def angularForm_circle_integralType : Prop :=
  ∀ d : PiecewiseC1Data (circlePath 1), ∃ h : OneFormIntegrable d angularForm,
    oneFormIntegral d angularForm h = 2 * Real.pi
def angularField_no_global_potentialType : Prop := ¬ HasPotential puncturedPlane angularField
def angularForm_not_exactType : Prop := ¬ IsExactForm puncturedPlane angularForm

def angularSlit_rayType : Prop := ∀ (α : ℝ) (x : E 2),
  x ∉ angularSlit α ↔ ∃ r : ℝ, 0 ≤ r ∧
    complexCoordinates.symm x = -(r : ℂ) * Complex.exp ((α : ℂ) * Complex.I)
def angularSlit_openType : Prop := ∀ α, IsOpen (angularSlit α)
def angularSlit_subsetType : Prop := ∀ α, angularSlit α ⊆ puncturedPlane
def slitAngle_branchType : Prop := ∀ α, IsAngleBranch (angularSlit α) (slitAngle α)
def slitAngle_potentialType : Prop := ∀ α,
  IsPotential (angularSlit α) angularField (slitAngle α)
def continuous_angle_branch_potentialType : Prop := ∀ (α : ℝ) (a : E 2 → ℝ),
  IsAngleBranch (angularSlit α) a → IsPotential (angularSlit α) angularField a

end Specs.D04.C11.AngularPotentialObstruction
