import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.SmoothFlat
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Analyticity

/-! K03.06.smooth_not_analytic, paper.tex:2883–2886.
The function is the existing zero extension of exp(-1/x²). Taylor coefficients
use real iterated derivatives and factorial normalization, including order zero.
Series values mean limits of the inclusive ordered partial sums. Nonanalyticity
excludes every local power series representation, not just the Taylor series.
The finite Peano assertions include order zero and use a two-sided neighborhood.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch06.SmoothNotAnalytic
open Filter
open scoped Topology BigOperators

abbrev taylorCoefficientType := ℕ → ℝ

def taylorCoefficientValue : taylorCoefficientType := fun n =>
  iteratedDeriv n FlatDecay.flatExponentialValue 0 / (n.factorial : ℝ)

def coefficientsZero : Prop := ∀ n : ℕ, taylorCoefficientValue n = 0

def partialSumsZero : Prop := ∀ (x : ℝ) (N : ℕ),
  Ch13.PowerSeries.realPowerSeriesPartialSumValue taylorCoefficientValue 0 x N = 0

def seriesHasSumZero : Prop := ∀ x : ℝ,
  Ch13.PowerSeries.RealPowerSeriesHasSumValue taylorCoefficientValue 0 x 0

def seriesDiffers : Prop := ∀ x : ℝ, x ≠ 0 →
  ¬ Ch13.PowerSeries.RealPowerSeriesHasSumValue taylorCoefficientValue 0 x
    (FlatDecay.flatExponentialValue x)

def noTaylorNeighborhood : Prop := ∀ r : ℝ, 0 < r → ∃ x : ℝ,
  0 < |x| ∧ |x| < r ∧
    ¬ Ch13.PowerSeries.RealPowerSeriesHasSumValue taylorCoefficientValue 0 x
      (FlatDecay.flatExponentialValue x)

def noPowerSeriesNeighborhood : Prop := ¬ ∃ (a : ℕ → ℝ) (r : ℝ),
  0 < r ∧ ∀ x : ℝ, |x| < r →
    Ch13.PowerSeries.RealPowerSeriesHasSumValue a 0 x (FlatDecay.flatExponentialValue x)

def notAnalyticAt : Prop := ¬ AnalyticAt ℝ FlatDecay.flatExponentialValue 0

def finitePeano : Prop := ∀ n : ℕ,
  Ch02.BigO.scalarLittleOValue (𝓝 (0 : ℝ))
    (fun h => FlatDecay.flatExponentialValue h -
      ∑ k ∈ Finset.range (n + 1), taylorCoefficientValue k * h ^ k)
    (fun h => h ^ n)

def smoothNotAnalytic : Prop :=
  Ch04.Higher.smoothOnValue FlatDecay.flatExponentialValue Set.univ ∧
    ¬ AnalyticAt ℝ FlatDecay.flatExponentialValue 0

end Specs.SingleVariableAnalysis.Ch06.SmoothNotAnalytic
