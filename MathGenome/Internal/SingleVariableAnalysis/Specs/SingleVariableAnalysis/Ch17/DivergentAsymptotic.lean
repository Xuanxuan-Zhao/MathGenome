import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaRecurrence
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Absolute
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Ratio
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.PowerSeries
import Mathlib.Analysis.Asymptotics.Defs

/-! K03.17.divergent_asymptotic, paper.tex:4384–4402.
The parameter approaches zero from the right. The measure-integral value
formulas below are accompanied by independent improper Darboux-limit
statements, including absolute convergence. No total integral is used to
assert convergence. The radius is the shared Chapter 13 reciprocal-root-limsup radius
for coefficients (-1)^n n!, and ordinary series divergence
is stated separately. The expansion through degree m has little-o(x^m)
remainder for every m, including m = 0.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic
open Set MeasureTheory Filter
open scoped Topology BigOperators

abbrev kernelType := ℝ → ℝ → ℝ
def kernelValue : kernelType := fun x t => Real.exp (-t) / (1 + x * t)
abbrev functionType := ℝ → ℝ
def functionValue : functionType := fun x => ∫ t in Ioi (0 : ℝ), kernelValue x t
abbrev coefficientType := ℕ → ℝ
def coefficientValue : coefficientType := fun n => (-1 : ℝ)^n * (n.factorial : ℝ)
abbrev truncationType := ℕ → ℝ → ℝ
def truncationValue : truncationType := fun N x =>
  ∑ k ∈ Finset.range N, coefficientValue k * x^k
abbrev remainderType := ℕ → ℝ → ℝ
def remainderValue : remainderType := fun N x =>
  (-x)^N * ∫ t in Ioi (0 : ℝ), t^N * Real.exp (-t) / (1 + x*t)

def hasIntegral : Prop := ∀ x : ℝ, 0 < x →
  Ch10.SeveralEndpoints.hasIntegralValue .real (kernelValue x)
    (0 : WithBot ℝ) ⊤ (functionValue x)

def absoluteConvergence : Prop := ∀ x : ℝ, 0 < x →
  Ch10.Absolute.absoluteValue .real (kernelValue x) (0 : WithBot ℝ) ⊤

/-- Both endpoint limits are independent, with split at 1. -/
def independentLimits : Prop := ∀ x : ℝ, 0 < x →
  Ch10.OneEndpoint.leftHasIntegralValue .real (kernelValue x) (0 : WithBot ℝ) 1
    (show ℝ from ∫ t in (0 : ℝ)..1, kernelValue x t) ∧
  Ch10.OneEndpoint.rightHasIntegralValue .real (kernelValue x) 1 ⊤
    (show ℝ from ∫ t in Ioi (1 : ℝ), kernelValue x t)

def remainderHasIntegral : Prop := ∀ (N : ℕ) (x : ℝ), 0 < x →
  Ch10.SeveralEndpoints.hasIntegralValue .real
    (fun t : ℝ => t^N * Real.exp (-t) / (1+x*t)) (0 : WithBot ℝ) ⊤
    (show ℝ from ∫ t in Ioi (0 : ℝ), t^N * Real.exp (-t) / (1+x*t))

def expansion : Prop := ∀ (N : ℕ) (x : ℝ), 1 ≤ N → 0 < x →
  functionValue x = truncationValue N x + remainderValue N x

def remainderBound : Prop := ∀ (N : ℕ) (x : ℝ), 1 ≤ N → 0 < x →
  |remainderValue N x| ≤ (N.factorial : ℝ) * x^N

def radiusZero : Prop :=
  Ch13.PowerSeries.realPowerSeriesRadiusValue coefficientValue = 0

def seriesDiverges : Prop := ∀ x : ℝ, x ≠ 0 →
  Ch11.PartialSums.realSeriesDivergesValue (fun n => coefficientValue n * x^n)

def termsNotTendstoZero : Prop := ∀ x : ℝ, x ≠ 0 →
  ¬ Tendsto (fun n => coefficientValue n * x^n) atTop (𝓝 0)

def allOrders : Prop := ∀ m : ℕ,
  Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
    (fun x => functionValue x - truncationValue (m+1) x) (fun x => x^m)

end Specs.SingleVariableAnalysis.Ch17.DivergentAsymptotic
