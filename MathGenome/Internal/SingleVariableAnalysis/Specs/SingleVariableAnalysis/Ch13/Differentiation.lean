import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.CompactUniform
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic

/-!
K03.13.termwise, paper.tex:1387–1397, differentiation portion.
The sum is specified by its ordinary ordered partial sums on the open real
convergence interval. Any function representing those values has derivatives
of every finite order there, with the ordinary sums of the formal derivative
terms as values. Values outside that interval are immaterial. Existence of
such a representative is included separately. Complex targets use real
increments throughout. Equality of extended radii has no positivity or
finiteness hypothesis, so includes zero and infinity. The integration portion
of this source entry belongs to the separate integration goal.
-/
namespace Specs.SingleVariableAnalysis.Ch13.Differentiation
open PowerSeries CompactUniform
open Specs.SingleVariableAnalysis.Ch11.PartialSums
open scoped ENNReal

def realSumExists : Prop := ∀ (a : ℕ → ℝ) (c : ℝ),
  ∃ f : ℝ → ℝ, ∀ x : ℝ,
    ENNReal.ofReal |x-c| < realPowerSeriesRadiusValue a →
    RealPowerSeriesHasSumValue a c x (f x)

def complexSumExists : Prop := ∀ (a : ℕ → ℂ) (c : ℝ),
  ∃ f : ℝ → ℂ, ∀ x : ℝ,
    ENNReal.ofReal |x-c| < complexPowerSeriesRadiusValue a →
    ComplexPowerSeriesHasSumValue a c (x : ℂ) (f x)

def realAllDerivatives : Prop := ∀ (a : ℕ → ℝ) (c : ℝ) (f : ℝ → ℝ),
  (∀ x : ℝ, ENNReal.ofReal |x-c| < realPowerSeriesRadiusValue a →
    RealPowerSeriesHasSumValue a c x (f x)) →
  ∀ (k : ℕ) (x : ℝ), ENNReal.ofReal |x-c| < realPowerSeriesRadiusValue a →
    realSeriesHasSumValue (realFormalDerivativeTermValue a c k x)
      (iteratedDeriv k f x) ∧
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k+1) f x) x

def complexAllDerivatives : Prop := ∀ (a : ℕ → ℂ) (c : ℝ) (f : ℝ → ℂ),
  (∀ x : ℝ, ENNReal.ofReal |x-c| < complexPowerSeriesRadiusValue a →
    ComplexPowerSeriesHasSumValue a c (x : ℂ) (f x)) →
  ∀ (k : ℕ) (x : ℝ), ENNReal.ofReal |x-c| < complexPowerSeriesRadiusValue a →
    complexSeriesHasSumValue (complexFormalDerivativeTermValue a c k (x : ℂ))
      (iteratedDeriv k f x) ∧
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k+1) f x) x

def realDerivativeRadius : Prop := ∀ a : ℕ → ℝ,
  realPowerSeriesRadiusValue (fun n => (n+1 : ℝ) * a (n+1)) =
    realPowerSeriesRadiusValue a

def complexDerivativeRadius : Prop := ∀ a : ℕ → ℂ,
  complexPowerSeriesRadiusValue (fun n => (n+1 : ℂ) * a (n+1)) =
    complexPowerSeriesRadiusValue a

end Specs.SingleVariableAnalysis.Ch13.Differentiation
