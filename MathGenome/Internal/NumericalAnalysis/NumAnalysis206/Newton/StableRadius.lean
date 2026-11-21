import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.StableRadius
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Exact real-algebraic stable radius formula from Proposition W78. -/
namespace NumAnalysis206.Newton.StableRadius

theorem denominator_positive (η L : ℝ) :
    0 < 1 + Real.sqrt (1 - 2 * η * L) := by
  have h := Real.sqrt_nonneg (1 - 2 * η * L)
  linarith

theorem radius_identity (η L : ℝ) (hL : 0 < L)
    (_hlower : 0 ≤ 2 * η * L) (hupper : 2 * η * L ≤ 1) :
    (1 - Real.sqrt (1 - 2 * η * L)) / L =
      2 * η / (1 + Real.sqrt (1 - 2 * η * L)) := by
  have hsquare : Real.sqrt (1 - 2 * η * L) ^ 2 = 1 - 2 * η * L :=
    Real.sq_sqrt (by linarith)
  have hden := ne_of_gt (denominator_positive η L)
  apply (div_eq_div_iff (ne_of_gt hL) hden).2
  nlinarith [hsquare]

theorem radius_at_zero (η : ℝ) :
    2 * η / (1 + Real.sqrt (1 - 2 * η * (0 : ℝ))) = η := by
  simp only [mul_zero, sub_zero, Real.sqrt_one]
  norm_num

theorem radius_continuous (η : ℝ) :
    Continuous (fun L : ℝ =>
      2 * η / (1 + Real.sqrt (1 - 2 * η * L))) := by
  apply Continuous.div continuous_const
    (continuous_const.add (Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_const.mul continuous_id))))
  intro L
  exact ne_of_gt (denominator_positive η L)

end NumAnalysis206.Newton.StableRadius
