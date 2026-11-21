import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
Independent specification of the geometric-series part of K03.11.geometric_p
(paper.tex:1011–1020). Terms begin at zero and the partial sum through N
includes q^N, including the constant term q^0 = 1 when q = 0.
The upstream sum predicates are ordinary finite scalar limits of ordered
partial sums. Divergence means absence of every finite scalar sum.
No real exponents, logarithms, or exponentials occur in these statements.
The harmonic and p-series assertions in the same source entry are allocated
separately to Necessary and PSeries.
-/

namespace Specs.SingleVariableAnalysis.Ch11.Geometric

open PartialSums

/-- Convergence with the specified value, for every real ratio in the unit ball. -/
def realGeometricSeriesHasSum : Prop :=
  ∀ q : ℝ, |q| < 1 → realSeriesHasSumValue (fun n => q ^ n) (1 / (1 - q))

/-- Every ratio on or outside the boundary gives no finite real sum. -/
def realGeometricSeriesDiverges : Prop :=
  ∀ q : ℝ, 1 ≤ |q| → realSeriesDivergesValue (fun n => q ^ n)

def realGeometricSeriesConvergesIff : Prop :=
  ∀ q : ℝ, realSeriesConvergesValue (fun n => q ^ n) ↔ |q| < 1

/-- Complex ratios are constrained by the canonical modulus. -/
def complexGeometricSeriesHasSum : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 → complexSeriesHasSumValue (fun n => q ^ n) (1 / (1 - q))

def complexGeometricSeriesDiverges : Prop :=
  ∀ q : ℂ, 1 ≤ ‖q‖ → complexSeriesDivergesValue (fun n => q ^ n)

def complexGeometricSeriesConvergesIff : Prop :=
  ∀ q : ℂ, complexSeriesConvergesValue (fun n => q ^ n) ↔ ‖q‖ < 1

end Specs.SingleVariableAnalysis.Ch11.Geometric
