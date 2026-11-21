import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.GradientIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Independent statements for paper.tex, d04:09:circle. All path lengths and
line integrals use the shared polygonal-supremum and proper Riemann definitions. -/
noncomputable section
open Set
open scoped ENNReal
namespace Specs.D04.C09.CircleMultiplicity
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model
namespace Model

def circle (m : ℤ) (t : ℝ) : E 2 :=
  WithLp.toLp 2 ![Real.cos ((m : ℝ) * t), Real.sin ((m : ℝ) * t)]

def circleVelocity (m : ℤ) (t : ℝ) : E 2 :=
  WithLp.toLp 2 ![-(m : ℝ) * Real.sin ((m : ℝ) * t),
    (m : ℝ) * Real.cos ((m : ℝ) * t)]

def circlePath (m : ℤ) : IntervalPath 2 0 (2 * Real.pi) where
  ordered := by positivity
  toFun := circle m
  continuousOn := by
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

def puncturedPlane : Set (E 2) := {x | x ≠ 0}

def angularField (x : E 2) : E 2 :=
  WithLp.toLp 2 ![-x 1 / ((x 0)^2 + (x 1)^2), x 0 / ((x 0)^2 + (x 1)^2)]
end Model
open Model

abbrev circleType := ℤ → ℝ → E 2
def circleValue : circleType := circle
abbrev circleVelocityType := ℤ → ℝ → E 2
def circleVelocityValue : circleVelocityType := circleVelocity
abbrev circlePathType := ℤ → IntervalPath 2 0 (2 * Real.pi)
def circlePathValue : circlePathType := circlePath
abbrev puncturedPlaneType := Set (E 2)
def puncturedPlaneValue : puncturedPlaneType := puncturedPlane
abbrev angularFieldType := E 2 → E 2
def angularFieldValue : angularFieldType := angularField

def circle_derivativeType : Prop := ∀ (m : ℤ) (t : ℝ),
  HasDerivAt (circle m) (circleVelocity m t) t

def circle_speedType : Prop := ∀ (m : ℤ) (t : ℝ), ‖circleVelocity m t‖ = |(m : ℝ)|

def circle_traceType : Prop := ∀ m : ℤ, m ≠ 0 →
  trace (circlePath m) = {x : E 2 | ‖x‖ = 1}

def circle_closedType : Prop := ∀ m : ℤ, circle m 0 = circle m (2 * Real.pi)

def circle_piecewiseC1Type : Prop := ∀ m : ℤ, PiecewiseC1 (circlePath m)

def circle_lengthType : Prop := ∀ m : ℤ,
  length (circle m) 0 (2 * Real.pi) = ENNReal.ofReal (2 * Real.pi * |(m : ℝ)|)

def circle_scalar_integralType : Prop := ∀ (m : ℤ) (d : PiecewiseC1Data (circlePath m)),
  ∃ h : ScalarIntegrable d (fun _ => 1),
    scalarLineIntegral d (fun _ => 1) h = 2 * Real.pi * |(m : ℝ)|

def angularField_circleType : Prop := ∀ (m : ℤ) (t : ℝ),
  circle m t ∈ puncturedPlane ∧
  inner ℝ (angularField (circle m t)) (circleVelocity m t) = (m : ℝ)

def circle_work_integralType : Prop := ∀ (m : ℤ) (d : PiecewiseC1Data (circlePath m)),
  ∃ h : WorkIntegrable d angularField,
    workLineIntegral d angularField h = 2 * Real.pi * (m : ℝ)

def angularField_C1Type : Prop := CrOn 1 puncturedPlane angularField

def angularField_cross_partialsType : Prop := ∀ x ∈ puncturedPlane,
  scalarPartialDerivative (fun y => angularField y 1) x 0 =
    scalarPartialDerivative (fun y => angularField y 0) x 1

def angularField_no_potentialType : Prop := ¬ ∃ f : E 2 → ℝ,
  CrOn 1 puncturedPlane f ∧ ∀ x ∈ puncturedPlane, scalarGradient f x = angularField x

/-- Concrete equal-trace witnesses for both unsigned and signed multiplicity. -/
def trace_does_not_determineType : Prop :=
  ∃ (d₁ : PiecewiseC1Data (circlePath 1))
    (d₂ : PiecewiseC1Data (circlePath 2)) (dneg : PiecewiseC1Data (circlePath (-1))),
  ∃ (h₁ : ScalarIntegrable d₁ (fun _ => 1)) (h₂ : ScalarIntegrable d₂ (fun _ => 1)),
  ∃ (w₁ : WorkIntegrable d₁ angularField) (wneg : WorkIntegrable dneg angularField),
    trace (circlePath 1) = trace (circlePath 2) ∧
    trace (circlePath 1) = trace (circlePath (-1)) ∧
    scalarLineIntegral d₁ (fun _ => 1) h₁ ≠ scalarLineIntegral d₂ (fun _ => 1) h₂ ∧
    workLineIntegral d₁ angularField w₁ ≠ workLineIntegral dneg angularField wneg


end Specs.D04.C09.CircleMultiplicity
