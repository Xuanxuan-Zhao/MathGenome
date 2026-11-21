import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.PowerSeries

/-!
K03.13.radius, paper.tex:1358–1365. These statements use exactly the
upstream coefficient-root limsup and its extended nonnegative reciprocal.
Strict interior/exterior inequalities deliberately leave the boundary open.
Convergence and divergence concern the ordinary inclusive partial sums;
absolute convergence is the ordinary convergence of the magnitude series.
The center is included regardless of whether the radius is zero. Uniqueness
compares against every extended nonnegative radius with the same dichotomy.
Real centers and both real and complex coefficients have their original scope.
-/
namespace Specs.SingleVariableAnalysis.Ch13.Radius

open Specs.SingleVariableAnalysis.Ch13.PowerSeries
open scoped ENNReal

def realCenterHasSum : Prop := ∀ (a : ℕ → ℝ) (c : ℝ),
  RealPowerSeriesHasSumValue a c c (a 0) ∧
  RealPowerSeriesAbsolutelyConvergesValue a c c

def complexCenterHasSum : Prop := ∀ (a : ℕ → ℂ) (c : ℝ),
  ComplexPowerSeriesHasSumValue a c (c : ℂ) (a 0) ∧
  ComplexPowerSeriesAbsolutelyConvergesValue a c (c : ℂ)

def realRadiusAbsolute : Prop := ∀ (a : ℕ → ℝ) (c x : ℝ),
  ENNReal.ofReal |x-c| < realPowerSeriesRadiusValue a →
  RealPowerSeriesAbsolutelyConvergesValue a c x

def complexRadiusAbsolute : Prop := ∀ (a : ℕ → ℂ) (c : ℝ) (z : ℂ),
  ENNReal.ofReal ‖z-(c : ℂ)‖ < complexPowerSeriesRadiusValue a →
  ComplexPowerSeriesAbsolutelyConvergesValue a c z

def realRadiusDiverges : Prop := ∀ (a : ℕ → ℝ) (c x : ℝ),
  realPowerSeriesRadiusValue a < ENNReal.ofReal |x-c| →
  ¬ RealPowerSeriesConvergesValue a c x

def complexRadiusDiverges : Prop := ∀ (a : ℕ → ℂ) (c : ℝ) (z : ℂ),
  complexPowerSeriesRadiusValue a < ENNReal.ofReal ‖z-(c : ℂ)‖ →
  ¬ ComplexPowerSeriesConvergesValue a c z

def realRadiusUnique : Prop := ∀ (a : ℕ → ℝ) (c : ℝ) (r : ℝ≥0∞),
  (∀ x : ℝ, ENNReal.ofReal |x-c| < r →
    RealPowerSeriesAbsolutelyConvergesValue a c x) →
  (∀ x : ℝ, r < ENNReal.ofReal |x-c| →
    ¬ RealPowerSeriesConvergesValue a c x) →
  r = realPowerSeriesRadiusValue a

def complexRadiusUnique : Prop := ∀ (a : ℕ → ℂ) (c : ℝ) (r : ℝ≥0∞),
  (∀ z : ℂ, ENNReal.ofReal ‖z-(c : ℂ)‖ < r →
    ComplexPowerSeriesAbsolutelyConvergesValue a c z) →
  (∀ z : ℂ, r < ENNReal.ofReal ‖z-(c : ℂ)‖ →
    ¬ ComplexPowerSeriesConvergesValue a c z) →
  r = complexPowerSeriesRadiusValue a

def realRadiusEndpoints : Prop := ∀ (a : ℕ → ℝ) (c : ℝ),
  (realPowerSeriesRadiusValue a = 0 → ∀ x : ℝ, x ≠ c →
    ¬ RealPowerSeriesConvergesValue a c x) ∧
  (realPowerSeriesRadiusValue a = ⊤ → ∀ x : ℝ,
    RealPowerSeriesAbsolutelyConvergesValue a c x)

def complexRadiusEndpoints : Prop := ∀ (a : ℕ → ℂ) (c : ℝ),
  (complexPowerSeriesRadiusValue a = 0 → ∀ z : ℂ, z ≠ (c : ℂ) →
    ¬ ComplexPowerSeriesConvergesValue a c z) ∧
  (complexPowerSeriesRadiusValue a = ⊤ → ∀ z : ℂ,
    ComplexPowerSeriesAbsolutelyConvergesValue a c z)

end Specs.SingleVariableAnalysis.Ch13.Radius
