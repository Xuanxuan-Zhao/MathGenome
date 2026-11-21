import MathGenome.Internal.Specs.D07.Appendix.RealOddExtensions
import Mathlib.Analysis.Polynomial.Order
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Order.Ring.Abs

/-!
The real odd-degree lemma from the algebraic FTA appendix.
The sign lemmas used below follow from real polynomial asymptotics and the
intermediate value theorem; they use no complex root-existence result.
The extension argument uses the tower law through `minpoly.degree_dvd`.
-/

universe u

namespace D07.Appendix.RealOddExtensions

open Polynomial

/-- If there were no roots, the signs to the left and right of all roots
would hold at the same point. In odd degree those signs are opposite. -/
private theorem odd_polynomial_has_root_of_leadingCoeff_nonneg
    (f : Polynomial ℝ) (hodd : Odd f.natDegree) (hlc : 0 ≤ f.leadingCoeff) :
    ∃ x : ℝ, f.eval x = 0 := by
  by_contra h
  have hroot : ∀ x : ℝ, ¬ f.IsRoot x := by simpa only [not_exists, IsRoot.def] using h
  have hpos : 0 < f.eval 0 :=
    zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (fun x hx => (hroot x hx).elim) hlc
  have hneg := zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
    (x := (0 : ℝ)) (fun x hx => (hroot x hx).elim) hlc
  rw [Int.negOnePow_odd _ (by simpa using hodd)] at hneg
  norm_num at hneg
  exact (not_lt_of_ge hpos.le) hneg

theorem odd_polynomial_has_real_zero :
    Specs.D07.Appendix.RealOddExtensions.OddPolynomialHasRealZero := by
  intro f hodd
  rcases le_total 0 f.leadingCoeff with hlc | hlc
  · exact odd_polynomial_has_root_of_leadingCoeff_nonneg f hodd hlc
  · obtain ⟨x, hx⟩ := odd_polynomial_has_root_of_leadingCoeff_nonneg (-f)
      (by simpa using hodd) (by simpa using hlc)
    exact ⟨x, by simpa using hx⟩

theorem odd_extension_surjective :
    Specs.D07.Appendix.RealOddExtensions.OddExtensionSurjective.{u} := by
  intro E _ _ _ hodd a
  have ha : IsIntegral ℝ a := IsIntegral.of_finite ℝ a
  have hdegree : Odd (minpoly ℝ a).natDegree :=
    hodd.of_dvd_nat (minpoly.degree_dvd ha)
  obtain ⟨r, hr⟩ := odd_polynomial_has_real_zero (minpoly ℝ a) hdegree
  have hlinear : (minpoly ℝ a).degree = 1 :=
    degree_eq_one_of_irreducible_of_root (minpoly.irreducible ha) hr
  exact (minpoly.degree_eq_one_iff.mp hlinear)

end D07.Appendix.RealOddExtensions
