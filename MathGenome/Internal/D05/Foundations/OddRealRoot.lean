import MathGenome.Internal.Specs.D05.Foundations.OddRealRoot
import MathGenome.Internal.D05.Foundations.FormalPolynomials
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
The odd-degree root theorem, using leading-term domination and the real IVT.
No real or complex splitting theorem is used. Mathlib's polynomial asymptotics
are proved by comparing each lower power with the leading power.
-/

namespace D05.Foundations.OddRealRoot

open Filter Polynomial

/-- With positive leading coefficient, an odd-degree polynomial tends to opposite
infinities at the two ends of the real line. -/
theorem limits_of_positive_leadingCoeff (p : Polynomial ℝ)
    (hpos : 0 < p.natDegree) (hodd : Odd p.natDegree)
    (hlc : 0 < p.leadingCoeff) :
    Tendsto p.eval atTop atTop ∧ Tendsto p.eval atBot atBot := by
  have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp hpos
  refine ⟨p.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc.le, ?_⟩
  -- Reflection changes the sign of the leading coefficient in odd degree.
  have hreflect : (p.comp (-X)).leadingCoeff = -p.leadingCoeff := by
    rw [comp_neg_X_leadingCoeff_eq, hodd.neg_one_pow, neg_one_mul]
  have hneg : Tendsto (fun x : ℝ => p.eval (-x)) atTop atBot := by
    simpa only [eval_comp, eval_neg, eval_X] using
      (p.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos
        (by simpa only [degree_comp_neg_X] using hdeg)
        (by rw [hreflect]; exact neg_nonpos.mpr hlc.le)
  simpa only [Function.comp_def, neg_neg] using hneg.comp tendsto_neg_atBot_atTop

/-- The IVT applied between the two tails gives a zero when the leading
coefficient is positive. -/
theorem root_of_positive_leadingCoeff (p : Polynomial ℝ)
    (hpos : 0 < p.natDegree) (hodd : Odd p.natDegree)
    (hlc : 0 < p.leadingCoeff) : ∃ x : ℝ, p.eval x = 0 := by
  obtain ⟨hTop, hBot⟩ := limits_of_positive_leadingCoeff p hpos hodd hlc
  exact p.continuous.surjective hTop hBot 0

/-- Every real polynomial of positive odd degree has a real root. -/
theorem existsRealRoot : D05.Specs.OddRealRoot.existsRealRoot := by
  intro p hpos hodd
  have hlc : p.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hpos)
  rcases lt_or_gt_of_ne hlc with hneg | hposlc
  · obtain ⟨x, hx⟩ := root_of_positive_leadingCoeff (-p)
      (by simpa only [natDegree_neg] using hpos)
      (by simpa only [natDegree_neg] using hodd)
      (by simpa only [leadingCoeff_neg] using neg_pos.mpr hneg)
    exact ⟨x, neg_eq_zero.mp (by simpa only [eval_neg] using hx)⟩
  · exact root_of_positive_leadingCoeff p hpos hodd hposlc

end D05.Foundations.OddRealRoot
