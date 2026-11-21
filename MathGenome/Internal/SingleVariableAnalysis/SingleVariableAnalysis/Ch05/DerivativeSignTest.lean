import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.DerivativeSignTest
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith

/-!
The first derivative sign test and its stationary-point counterexample.
On either short closed segment ending at the center, continuity at the center
and punctured differentiability give precisely the hypotheses of Lagrange.
The sign of the intermediate derivative gives a strict inequality. Negating
the function proves the minimum test without differentiating at the center.
-/

namespace SingleVariableAnalysis

open Set
open scoped Topology

theorem first_derivative_strict_maximum (f : ℝ → ℝ) (a r : ℝ)
    (hr : 0 < r) (hf : ContinuousAt f a)
    (hd : ∀ x : ℝ, 0 < |x - a| → |x - a| < r → DifferentiableAt ℝ f x)
    (hl : ∀ x ∈ Ioo (a - r) a, 0 < deriv f x)
    (hu : ∀ x ∈ Ioo a (a + r), deriv f x < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x - a| → |x - a| < δ → f x < f a := by
  refine ⟨r, hr, ?_⟩
  intro x hxa hxr
  have hxne : x ≠ a := sub_ne_zero.mp (abs_pos.mp hxa)
  have hbounds := abs_lt.mp hxr
  rcases lt_or_gt_of_ne hxne with hx | hx
  · have hc : ContinuousOn f (Icc x a) := by
      intro y hy
      by_cases hya : y = a
      · subst y
        exact hf.continuousWithinAt
      · have hya' : y < a := lt_of_le_of_ne hy.2 hya
        exact (hd y (abs_pos.mpr (sub_ne_zero.mpr hya))
          (by rw [abs_of_neg (sub_neg.mpr hya')]; linarith [hy.1])).continuousAt.continuousWithinAt
    have hdiff : ∀ y ∈ Ioo x a, DifferentiableAt ℝ f y := by
      intro y hy
      apply hd y (abs_pos.mpr (sub_ne_zero.mpr hy.2.ne))
      rw [abs_of_neg (sub_neg.mpr hy.2)]
      linarith [hy.1]
    obtain ⟨c, hc, heq⟩ := lagrange_deriv f x a hx hc hdiff
    have hp : 0 < deriv f c := hl c ⟨by linarith [hc.1], hc.2⟩
    have hpos := mul_pos hp (sub_pos.mpr hx)
    linarith
  · have hc : ContinuousOn f (Icc a x) := by
      intro y hy
      by_cases hya : y = a
      · subst y
        exact hf.continuousWithinAt
      · have hay : a < y := lt_of_le_of_ne hy.1 (Ne.symm hya)
        exact (hd y (abs_pos.mpr (sub_ne_zero.mpr hya))
          (by rw [abs_of_pos (sub_pos.mpr hay)]; linarith [hy.2])).continuousAt.continuousWithinAt
    have hdiff : ∀ y ∈ Ioo a x, DifferentiableAt ℝ f y := by
      intro y hy
      apply hd y (abs_pos.mpr (sub_ne_zero.mpr hy.1.ne'))
      rw [abs_of_pos (sub_pos.mpr hy.1)]
      linarith [hy.2]
    obtain ⟨c, hc, heq⟩ := lagrange_deriv f a x hx hc hdiff
    have hn : deriv f c < 0 := hu c ⟨hc.1, by linarith [hc.2]⟩
    have hneg := mul_neg_of_neg_of_pos hn (sub_pos.mpr hx)
    linarith

theorem first_derivative_strict_minimum (f : ℝ → ℝ) (a r : ℝ)
    (hr : 0 < r) (hf : ContinuousAt f a)
    (hd : ∀ x : ℝ, 0 < |x - a| → |x - a| < r → DifferentiableAt ℝ f x)
    (hl : ∀ x ∈ Ioo (a - r) a, deriv f x < 0)
    (hu : ∀ x ∈ Ioo a (a + r), 0 < deriv f x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x - a| → |x - a| < δ → f a < f x := by
  obtain ⟨δ, hδ, hmax⟩ := first_derivative_strict_maximum (fun x => -f x) a r hr
    hf.neg (fun x hx hxr => (hd x hx hxr).neg)
    (by intro x hx; simpa using neg_pos.mpr (hl x hx))
    (by intro x hx; simpa using neg_neg_of_pos (hu x hx))
  exact ⟨δ, hδ, fun x hx hxr => neg_lt_neg_iff.mp (hmax x hx hxr)⟩

theorem cubic_stationary_no_extremum :
    HasDerivAt (fun x : ℝ => x ^ 3) 0 0 ∧
      deriv (fun x : ℝ => x ^ 3) 0 = 0 ∧
      ¬ IsLocalMax (fun x : ℝ => x ^ 3) 0 ∧
      ¬ IsLocalMin (fun x : ℝ => x ^ 3) 0 := by
  have hder : HasDerivAt (fun x : ℝ => x ^ 3) 0 0 := by
    simpa using hasDerivAt_pow 3 (0 : ℝ)
  refine ⟨hder, hder.deriv, ?_, ?_⟩
  · intro hmax
    obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp hmax
    have h := hh (y := δ / 2) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < δ / 2)]
      linarith)
    have hp : 0 < (δ / 2) ^ 3 := pow_pos (by positivity) _
    norm_num at h
    linarith
  · intro hmin
    obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp hmin
    have h := hh (y := -(δ / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity : 0 < δ / 2)]
      linarith)
    have hp : 0 < (δ / 2) ^ 3 := pow_pos (by positivity) _
    norm_num at h
    linarith

end SingleVariableAnalysis
