import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.SinCos
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.LogArctanSeries
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Binomial

/-!
K03.13.standard_series, paper.tex:1514–1536, including the binomial
expansion referred to at 1452–1477. All sums below mean convergence of
ordinary inclusive partial sums, including the conditional endpoints.

The first three identities name both the shared series constructions and
the canonical real functions. The logarithm uses its inverse-exponential
construction, the arctangent its fixed principal branch. The log index n
denotes source index n+1. Binomial coefficients are the shared finite
falling products divided by factorials. Real powers occur only at positive
bases; terminating cases use algebraic natural powers at every real base.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch13.StandardSeries
open Ch11.PartialSums Ch11.Absolute
open Ch07.ExpConstruction Ch07.SinCos Ch07.LogConstruction
open Ch07.TrigInverses Ch07.PiPeriod Ch07.RealPowers
open Ch13.LogArctanSeries Ch13.PowerSeries Ch13.BinomialInterior

def expIdentity : Prop := ∀ x : ℝ,
  realSeriesHasSumValue (fun n => x^n / (n.factorial : ℝ)) (realSeriesExpValue x) ∧
  realSeriesHasSumValue (fun n => x^n / (n.factorial : ℝ)) (Real.exp x)

def sinIdentity : Prop := ∀ x : ℝ,
  realSeriesHasSumValue
    (fun n => (-1 : ℝ)^n * x^(2*n+1) / ((2*n+1).factorial : ℝ)) (realSeriesSinValue x) ∧
  realSeriesHasSumValue
    (fun n => (-1 : ℝ)^n * x^(2*n+1) / ((2*n+1).factorial : ℝ)) (Real.sin x)

def cosIdentity : Prop := ∀ x : ℝ,
  realSeriesHasSumValue
    (fun n => (-1 : ℝ)^n * x^(2*n) / ((2*n).factorial : ℝ)) (realSeriesCosValue x) ∧
  realSeriesHasSumValue
    (fun n => (-1 : ℝ)^n * x^(2*n) / ((2*n).factorial : ℝ)) (Real.cos x)

def factorialAbsolute : Prop := ∀ x : ℝ,
  realAbsolutelyConvergesValue (fun n => x^n / (n.factorial : ℝ)) ∧
  realAbsolutelyConvergesValue
    (fun n => (-1 : ℝ)^n * x^(2*n+1) / ((2*n+1).factorial : ℝ)) ∧
  realAbsolutelyConvergesValue
    (fun n => (-1 : ℝ)^n * x^(2*n) / ((2*n).factorial : ℝ))

def logIdentity : Prop := ∀ x : ℝ, -1 < x → x ≤ 1 →
  realSeriesHasSumValue (logSeriesTermValue x) (seriesLogValue (1+x))

def arctanIdentity : Prop := ∀ x : ℝ, -1 ≤ x → x ≤ 1 →
  realSeriesHasSumValue (arctanSeriesTermValue x) (principalArctanValue x)

def logDomain : Prop := ∀ x : ℝ,
  realSeriesConvergesValue (logSeriesTermValue x) ↔ -1 < x ∧ x ≤ 1

def arctanDomain : Prop := ∀ x : ℝ,
  realSeriesConvergesValue (arctanSeriesTermValue x) ↔ -1 ≤ x ∧ x ≤ 1

def logEndpoint : Prop :=
  realSeriesHasSumValue (logSeriesTermValue 1) (seriesLogValue 2)

def arctanEndpoints : Prop :=
  realSeriesHasSumValue (arctanSeriesTermValue 1) (analyticPiValue/4) ∧
  realSeriesHasSumValue (arctanSeriesTermValue (-1)) (-(analyticPiValue/4))

def logNegativeEndpoint : Prop :=
  Ch01.SequenceLimit.divergesToNegInfinityValue
    (realPartialSumValue (logSeriesTermValue (-1))) ∧
  ¬ realSeriesConvergesValue (logSeriesTermValue (-1))

def exteriorDivergence : Prop := ∀ x : ℝ, 1 < |x| →
  ¬ realSeriesConvergesValue (logSeriesTermValue x) ∧
  ¬ realSeriesConvergesValue (arctanSeriesTermValue x)

def binomialInterior : Prop := ∀ (α x : ℝ), |x| < 1 →
  RealPowerSeriesHasSumValue (binomialCoefficientValue α) 0 x (realPowerValue (1+x) α)

def binomialRadius : Prop := ∀ α : ℝ, (∀ m : ℕ, α ≠ (m : ℝ)) →
  realPowerSeriesRadiusValue (binomialCoefficientValue α) = 1

def binomialOneConverges : Prop := ∀ α : ℝ, (∀ m : ℕ, α ≠ (m : ℝ)) →
  (RealPowerSeriesConvergesValue (binomialCoefficientValue α) 0 1 ↔ -1 < α)

def binomialOneSum : Prop := ∀ α : ℝ, -1 < α →
  RealPowerSeriesHasSumValue (binomialCoefficientValue α) 0 1 (realPowerValue 2 α)

def binomialNegOneConverges : Prop := ∀ α : ℝ, (∀ m : ℕ, α ≠ (m : ℝ)) →
  (RealPowerSeriesConvergesValue (binomialCoefficientValue α) 0 (-1) ↔ 0 < α)

def binomialNegOneSum : Prop := ∀ α : ℝ, 0 < α →
  RealPowerSeriesHasSumValue (binomialCoefficientValue α) 0 (-1) 0

def binomialEndpointsAbsolute : Prop := ∀ α : ℝ, 0 < α →
  RealPowerSeriesAbsolutelyConvergesValue (binomialCoefficientValue α) 0 1 ∧
  RealPowerSeriesAbsolutelyConvergesValue (binomialCoefficientValue α) 0 (-1)

def binomialOneConditional : Prop := ∀ α : ℝ, -1 < α → α < 0 →
  RealPowerSeriesConvergesValue (binomialCoefficientValue α) 0 1 ∧
  ¬ RealPowerSeriesAbsolutelyConvergesValue (binomialCoefficientValue α) 0 1

def binomialNaturalAllArguments : Prop := ∀ (m : ℕ) (x : ℝ),
  (∀ n : ℕ, m < n → binomialCoefficientValue (m : ℝ) n = 0) ∧
  RealPowerSeriesAbsolutelyConvergesValue (binomialCoefficientValue (m : ℝ)) 0 x ∧
  RealPowerSeriesHasSumValue (binomialCoefficientValue (m : ℝ)) 0 x ((1+x)^m)

def binomialNaturalEndpoints : Prop := ∀ m : ℕ,
  RealPowerSeriesHasSumValue (binomialCoefficientValue (m : ℝ)) 0 1 ((2 : ℝ)^m) ∧
  RealPowerSeriesHasSumValue (binomialCoefficientValue (m : ℝ)) 0 (-1)
    (if m = 0 then 1 else 0)

end Specs.SingleVariableAnalysis.Ch13.StandardSeries
