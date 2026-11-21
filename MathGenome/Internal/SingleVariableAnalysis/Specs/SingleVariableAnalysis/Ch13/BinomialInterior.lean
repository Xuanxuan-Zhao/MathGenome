import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.PowerSeries
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers

/-! K03.13.binomial, interior/termination/radius portion, paper.tex:1452–1470.
The coefficient is the finite falling product divided by n!, including the empty
product at n=0. The interior identity uses the source exp/log real power and
ordinary inclusive partial sums. For natural exponents the conclusion uses
natural powers at every real base, including zero and negative bases.
Endpoint convergence is a separate allocated obligation.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch13.BinomialInterior
open scoped BigOperators ENNReal

def binomialCoefficientType : Type := ℝ → ℕ → ℝ

def binomialCoefficientValue : binomialCoefficientType := fun α n =>
  (∏ j ∈ Finset.range n, (α - (j : ℝ))) / (n.factorial : ℝ)

def coefficientZero : Prop := ∀ α : ℝ, binomialCoefficientValue α 0 = 1

def coefficientRecurrence : Prop := ∀ (α : ℝ) (n : ℕ),
  (n + 1 : ℝ) * binomialCoefficientValue α (n + 1) =
    (α - n) * binomialCoefficientValue α n

def interior : Prop := ∀ (α x : ℝ), |x| < 1 →
  PowerSeries.RealPowerSeriesHasSumValue (binomialCoefficientValue α) 0 x
    (Ch07.RealPowers.realPowerValue (1 + x) α)

def naturalCoefficient : Prop := ∀ (m n : ℕ),
  binomialCoefficientValue (m : ℝ) n = (m.choose n : ℝ)

def termination : Prop := ∀ (m n : ℕ), m < n →
  binomialCoefficientValue (m : ℝ) n = 0

def naturalIdentity : Prop := ∀ (m : ℕ) (x : ℝ),
  ∑ n ∈ Finset.range (m + 1), binomialCoefficientValue (m : ℝ) n * x^n =
    (1 + x)^m

def nonnaturalRadius : Prop := ∀ α : ℝ, (∀ m : ℕ, α ≠ (m : ℝ)) →
  PowerSeries.realPowerSeriesRadiusValue (binomialCoefficientValue α) = 1

end Specs.SingleVariableAnalysis.Ch13.BinomialInterior
