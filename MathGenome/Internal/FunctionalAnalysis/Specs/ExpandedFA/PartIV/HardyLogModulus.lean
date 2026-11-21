import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyDisk
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The logarithmic part of `fa2:p4:hardy-factorization`, paper.tex:18858–18878.
The boundary measure is the probability Haar measure of the canonical Hardy
model.  The zero convention for `Real.log` is never used as a substitute for
the assertion that a nonzero Hardy function has nonzero boundary values a.e.
The pointwise logarithmic inequality is restricted to nonzeros; its exponential
form includes every point of the disk, including zeros of the function. -/

noncomputable section
open MeasureTheory
open scoped Real

namespace ExpandedFA.PartIV.HardyLogModulus
open HardyDiskSpec

abbrev BoundaryCircle := HardyDiskSpec.Circle

abbrev circleMeasure : Measure BoundaryCircle := AddCircle.haarAddCircle

def circlePoint (t : BoundaryCircle) : ℂ := fourier (T := 2 * π) 1 t

def boundaryLog (f : H2) (t : BoundaryCircle) : ℝ := Real.log ‖boundary f t‖

def poissonLog (h : BoundaryCircle → ℝ) (z : ℂ) : ℝ :=
  ∫ t, ((1 - ‖z‖ ^ 2) / ‖circlePoint t - z‖ ^ 2) * h t ∂circleMeasure

def logarithmicIntegral (h : BoundaryCircle → ℝ) (z : ℂ) : ℂ :=
  ∫ t, ((circlePoint t + z) / (circlePoint t - z)) * (h t : ℂ) ∂circleMeasure

/-- The actual integral formula, defined without an integrability certificate. -/
def exponentialFactor (h : BoundaryCircle → ℝ) (c z : ℂ) : ℂ :=
  c * Complex.exp (logarithmicIntegral h z)

namespace Spec

def BoundaryLogIntegrable : Prop := ∀ f : H2, f ≠ 0 →
  Integrable (boundaryLog f) circleMeasure ∧
    ∀ᵐ t ∂circleMeasure, boundary f t ≠ 0

def LogMajorization : Prop := ∀ f : H2, f ≠ 0 → ∀ z ∈ disk,
  eval f z ≠ 0 → Real.log ‖eval f z‖ ≤ poissonLog (boundaryLog f) z

def ExponentialMajorization : Prop := ∀ f : H2, f ≠ 0 → ∀ z ∈ disk,
  ‖eval f z‖ ≤ Real.exp (poissonLog (boundaryLog f) z)

/-- This goal constructs the exponential factor. Cyclicity and inner–outer
uniqueness are separately allocated to `app_hardy_inner_outer`. -/
def FactorConstruction : Prop := ∀ f : H2, f ≠ 0 → ∀ c : ℂ, ‖c‖ = 1 →
  DifferentiableOn ℂ (exponentialFactor (boundaryLog f) c) disk ∧
    (∀ z ∈ disk, exponentialFactor (boundaryLog f) c z ≠ 0) ∧
    ∃ o : H2,
      Set.EqOn (eval o) (exponentialFactor (boundaryLog f) c) disk ∧
      (∀ᵐ t ∂circleMeasure, ‖boundary o t‖ = ‖boundary f t‖) ∧
      ∀ z ∈ disk, ‖eval f z / exponentialFactor (boundaryLog f) c z‖ ≤ 1

-- Independently useful parts of the construction, also stated without
-- presupposing any of the three analytic boundary conclusions above.
def IntegralHolomorphic : Prop := ∀ h : BoundaryCircle → ℝ, Integrable h circleMeasure →
  DifferentiableOn ℂ (logarithmicIntegral h) disk

def ExponentialHolomorphic : Prop := ∀ h : BoundaryCircle → ℝ, Integrable h circleMeasure →
  ∀ c : ℂ, DifferentiableOn ℂ (exponentialFactor h c) disk

def ExponentialNonzero : Prop := ∀ (h : BoundaryCircle → ℝ) (c : ℂ), c ≠ 0 →
  ∀ z : ℂ, exponentialFactor h c z ≠ 0

def ExponentialNorm : Prop := ∀ h : BoundaryCircle → ℝ, Integrable h circleMeasure →
  ∀ c : ℂ, ‖c‖ = 1 → ∀ z ∈ disk,
    ‖exponentialFactor h c z‖ = Real.exp (poissonLog h z)

/-- A useful integrability estimate requiring no nonzero hypothesis. The full
boundary logarithm theorem additionally controls the negative part. -/
def PositiveLogIntegrable : Prop := ∀ f : H2,
  Integrable (fun t => max (boundaryLog f t) 0) circleMeasure

/-- The positive logarithms actually converge in L² along radial approach. -/
def PositiveLogRadialConvergence : Prop := ∀ f : H2,
  ∃ (g : ℝ → Lp ℝ 2 circleMeasure) (b : Lp ℝ 2 circleMeasure),
    ((b : BoundaryCircle → ℝ) =ᵐ[circleMeasure] fun t => max (boundaryLog f t) 0) ∧
    (∀ r : ℝ, 0 ≤ r → r < 1 →
      (g r : BoundaryCircle → ℝ) =ᵐ[circleMeasure] fun t =>
        max (Real.log ‖eval f ((r : ℂ) * circlePoint t)‖) 0) ∧
    Filter.Tendsto g (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds b)

/-- General exponential construction for arbitrary square-integrable boundary
data. It has no analyticity assumption on those data, and assumes their logarithm
is integrable. Applying it to a Hardy boundary requires proving that premise. -/
def BoundaryExponentialRealization : Prop := ∀ g : BoundaryL2,
  Integrable (fun t => Real.log ‖g t‖) circleMeasure →
  (∀ᵐ t ∂circleMeasure, g t ≠ 0) →
  ∀ c : ℂ, ‖c‖ = 1 → ∃ o : H2,
    Set.EqOn (eval o) (exponentialFactor (fun t => Real.log ‖g t‖) c) disk ∧
    ∀ᵐ t ∂circleMeasure, ‖boundary o t‖ = ‖g t‖

end Spec
end ExpandedFA.PartIV.HardyLogModulus
