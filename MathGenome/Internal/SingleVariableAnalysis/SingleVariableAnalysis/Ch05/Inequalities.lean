import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Inequalities
import Mathlib.Analysis.MeanInequalities

/-!
# Exponential, logarithmic and weighted arithmetic–geometric inequalities

K03.05.inequalities, paper.tex:962–978. The declarations retain the shared
series/inverse/power constructions. Their upstream canonical bridges allow
reuse of Mathlib's real inequalities, including the strict and equality cases.

Provenance: `Analysis/Complex/Exponential.lean` proves the strict exponential
bound from the series and reciprocal identity; `SpecialFunctions/Log/Basic.lean`
obtains the strict logarithmic bound by substitution. `Analysis/MeanInequalities.lean`
proves finite weighted AM–GM and its equality criterion by Jensen for the
(strictly) convex exponential applied to logarithms, discarding zero weights.
This is equivalent to the manuscript's Jensen proof using the concave logarithm.
-/

namespace SingleVariableAnalysis
open scoped BigOperators

/-- The exponential lies above its tangent at zero, for every real argument. -/
theorem expSeries_one_add_le :
    Specs.SingleVariableAnalysis.Ch05.Inequalities.exponentialLowerBound := by
  intro x
  change 1 + x ≤ realSeriesExp x
  have he : realSeriesExp x = Real.exp x := expSeries_eq_realExp x
  rw [he, add_comm]
  exact Real.add_one_le_exp x

/-- Equality in the exponential supporting-line inequality. -/
theorem expSeries_eq_one_add_iff :
    Specs.SingleVariableAnalysis.Ch05.Inequalities.exponentialEquality := by
  intro x
  change realSeriesExp x = 1 + x ↔ x = 0
  have he : realSeriesExp x = Real.exp x := expSeries_eq_realExp x
  rw [he]
  constructor
  · intro h
    by_contra hx
    have hlt := Real.add_one_lt_exp hx
    linarith
  · rintro rfl
    simp

/-- The positive-domain logarithmic bound. -/
theorem seriesLog_le_sub_one :
    Specs.SingleVariableAnalysis.Ch05.Inequalities.logarithmUpperBound := by
  intro x hx
  change seriesLog x ≤ x - 1
  rw [seriesLog_eq_realLog x hx]
  exact Real.log_le_sub_one_of_pos hx

/-- Equality in the positive-domain logarithmic bound. -/
theorem seriesLog_eq_sub_one_iff :
    Specs.SingleVariableAnalysis.Ch05.Inequalities.logarithmEquality := by
  intro x hx
  change seriesLog x = x - 1 ↔ x = 1
  rw [seriesLog_eq_realLog x hx]
  constructor
  · intro h
    by_contra hx1
    exact (ne_of_lt (Real.log_lt_sub_one_of_pos hx hx1)) h
  · rintro rfl
    simp

/-- Finite weighted AM–GM, using the shared real-power construction. -/
theorem weighted_geometric_le_arithmetic :
    Specs.SingleVariableAnalysis.Ch05.Inequalities.weightedArithmeticGeometric := by
  intro ι s w a hw hs ha
  change (∏ j ∈ s, realPower (a j) (w j)) ≤ ∑ j ∈ s, w j * a j
  have hprod : (∏ j ∈ s, realPower (a j) (w j)) = ∏ j ∈ s, (a j) ^ (w j) :=
    Finset.prod_congr rfl (fun j hj => realPower_eq_rpow (a j) (ha j hj) (w j))
  rw [hprod]
  exact Real.geom_mean_le_arith_mean_weighted s w a hw hs (fun j hj => (ha j hj).le)

/-- Equality in finite weighted AM–GM, allowing arbitrary zero-weight inputs. -/
theorem weighted_geometric_eq_arithmetic_iff :
    Specs.SingleVariableAnalysis.Ch05.Inequalities.weightedArithmeticGeometricEquality := by
  intro ι s w a hw hs ha
  change (∏ j ∈ s, realPower (a j) (w j)) = ∑ j ∈ s, w j * a j ↔ _
  have hprod : (∏ j ∈ s, realPower (a j) (w j)) = ∏ j ∈ s, (a j) ^ (w j) :=
    Finset.prod_congr rfl (fun j hj => realPower_eq_rpow (a j) (ha j hj) (w j))
  rw [hprod]
  have heq := Real.geom_mean_eq_arith_mean_weighted_iff_of_nonneg s w a hw hs
    (fun j hj => (ha j hj).le)
  constructor
  · intro h j hj hjpos k hk hkpos
    exact heq.mp h j hj hjpos.ne' k hk hkpos.ne'
  · intro h
    apply heq.mpr
    intro j hj hjne k hk hkne
    exact h j hj (lt_of_le_of_ne (hw j hj) hjne.symm)
      k hk (lt_of_le_of_ne (hw k hk) hkne.symm)

end SingleVariableAnalysis
