import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfPolarReduction
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.PlanarHopf

/-! The explicit normal form of paper.tex, Chapter 16, “A check on the normalization”.
The complex plane has its usual real norm. Time and both parameters are real.
The stability assertion uses the shared maximal flow and includes forward existence.
-/
noncomputable section
namespace Specs.D13Unified.Ch16.HopfPolarExample
open Set Filter Complex
open scoped ComplexConjugate
open CubicHomologicalElimination HopfReturnExpansion
open _root_.D13Unified
open Ch01.AutonomousParameters Ch14.OrbitalDefinitions

/-- The original polynomial family, including the family without a cubic term. -/
def family (κ ω : ℝ) (x : ℝ × ℂ) : ℂ :=
  ((x.1 : ℂ) + I * ω) * x.2 + κ * x.2 * (‖x.2‖ ^ 2 : ℝ)

def field (μ ω : ℝ) (z : ℂ) : ℂ := family (-1) ω (μ, z)

def circle (μ : ℝ) : Set ℂ := Metric.sphere 0 (Real.sqrt μ)
def cycle (μ ω t : ℝ) : ℂ := polarPoint (Real.sqrt μ) (ω * t)

/-- The actual finite homological procedure, applied to the displayed polynomial
coefficients in the original complex coordinate. -/
def computedCoefficient (κ μ ω : ℝ) : ℂ :=
  retainedCoefficient μ ω zeroQuadratic (resonantCubic κ)

def Normalization : Prop :=
  (∀ κ ω μ z, family κ ω (μ, z) =
    eigenvalue μ ω * z + (resonantCubic κ).eval z) ∧
  (∀ μ ω, quadraticChange μ ω zeroQuadratic = zeroQuadratic) ∧
  (∀ κ μ ω, computedCoefficient κ μ ω = (κ : ℂ) ∧
    cubicChange μ ω (cubicAfterQuadratic zeroQuadratic (resonantCubic κ)
      (quadraticChange μ ω zeroQuadratic)) = resonantCubic 0)

/-- Equality of the physical velocity with the polar differential, with r>0.
Both implications are included, so these equations lose no polar solutions. -/
def PolarEquations : Prop :=
  ∀ μ ω r θ v w : ℝ, 0 < r →
    ((v : ℂ) * direction θ + (r : ℂ) * direction θ * (w * I) =
        field μ ω (polarPoint r θ) ↔
      v = μ * r - r ^ 3 ∧ w = ω)

/-- Actual derivatives of a differentiable polar curve. -/
def PolarSolutions : Prop :=
  ∀ μ ω (r θ : ℝ → ℝ) t v w,
    HasDerivAt r v t → HasDerivAt θ w t → 0 < r t →
    (HasDerivAt (fun s => polarPoint (r s) (θ s))
      (field μ ω (polarPoint (r t) (θ t))) t ↔
      v = μ * r t - (r t) ^ 3 ∧ w = ω)

def PeriodicCircle : Prop :=
  ∀ μ ω : ℝ, 0 < μ → 0 < ω →
    PlanarHopf.LeastPeriodOrbit (field μ ω) (circle μ) (2 * Real.pi / ω) ∧
    (∀ t, HasDerivAt (cycle μ ω) (field μ ω (cycle μ ω t)) t) ∧
    range (cycle μ ω) = circle μ

/-- Forward orbital asymptotic stability for every positive μ and ω, on the
whole original state domain ℂ. No small-parameter restriction is added. -/
def StableCircle : Prop :=
  ∀ μ ω : ℝ, 0 < μ → 0 < ω →
    ∃ A : AutonomousODE ℂ, A.domain = univ ∧
      (∀ z, autonomousEvalValue A z = field μ ω z) ∧
      orbitalAsymptoticallyStableValue A (circle μ)

/-- The amplitude relation and the failure of cubic nondegeneracy in the
linear family. This asserts no classification of the degenerate system. -/
def AmplitudeAndDegeneracy : Prop :=
  (∀ μ > 0, (Real.sqrt μ) ^ 2 = μ ∧ 0 < Real.sqrt μ) ∧
  (∀ μ ω, (computedCoefficient (-1) μ ω).re = -1 ∧
    (computedCoefficient 0 μ ω).re = 0 ∧ ¬ (computedCoefficient 0 μ ω).re ≠ 0)

end Specs.D13Unified.Ch16.HopfPolarExample
