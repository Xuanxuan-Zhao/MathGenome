import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.SecondTest
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.DerivativeSignTest
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative

/-!
The second derivative test under pointwise differentiability of the first
derivative. Its positive difference quotients give the first derivative's
opposite signs on the two sides. No continuity of the second derivative is
used. The zero-second-derivative examples are checked by polynomial calculus.
-/

namespace SingleVariableAnalysis

open Set

theorem second_derivative_strict_minimum (f : ℝ → ℝ) (a r : ℝ)
    (hr : 0 < r)
    (hf : ∀ x : ℝ, |x - a| < r → DifferentiableAt ℝ f x)
    (hdf : DifferentiableAt ℝ (deriv f) a) (hzero : deriv f a = 0)
    (hpos : 0 < deriv (deriv f) a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x - a| → |x - a| < δ → f a < f x := by
  have heps := (realDerivative_epsilon_iff (deriv f) (deriv (deriv f) a) a).mp
    ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr hdf.hasDerivAt)
  obtain ⟨s, hs, hquot⟩ := heps _ hpos
  have hq : ∀ x : ℝ, 0 < |x - a| → |x - a| < s →
      0 < deriv f x / (x - a) := by
    intro x hx hxs
    have h := hquot (x - a) hx hxs
    rw [add_sub_cancel, hzero, sub_zero] at h
    linarith [(abs_lt.mp h).1]
  apply first_derivative_strict_minimum f a (min r s) (lt_min hr hs)
    (hf a (by simpa using hr)).continuousAt
    (fun x _ hx => hf x (lt_of_lt_of_le hx (min_le_left r s)))
  · intro x hx
    have hxa : 0 < |x - a| := abs_pos.mpr (sub_ne_zero.mpr hx.2.ne)
    have hxs : |x - a| < s := by
      rw [abs_of_neg (sub_neg.mpr hx.2)]
      linarith [min_le_right r s, hx.1]
    have h := hq x hxa hxs
    exact (div_pos_iff.mp h).resolve_left (fun h' => (not_lt_of_ge (le_of_lt hx.2))
      (sub_pos.mp h'.2)) |>.1
  · intro x hx
    have hxa : 0 < |x - a| := abs_pos.mpr (sub_ne_zero.mpr hx.1.ne')
    have hxs : |x - a| < s := by
      rw [abs_of_pos (sub_pos.mpr hx.1)]
      linarith [min_le_right r s, hx.2]
    exact (div_pos_iff.mp (hq x hxa hxs)).resolve_right
      (fun h' => (not_lt_of_ge (sub_nonneg.mpr hx.1.le)) h'.2) |>.1

theorem second_derivative_strict_maximum (f : ℝ → ℝ) (a r : ℝ)
    (hr : 0 < r)
    (hf : ∀ x : ℝ, |x - a| < r → DifferentiableAt ℝ f x)
    (hdf : DifferentiableAt ℝ (deriv f) a) (hzero : deriv f a = 0)
    (hneg : deriv (deriv f) a < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x - a| → |x - a| < δ → f x < f a := by
  have hdneg : deriv (fun x => -f x) = fun x => -deriv f x := by
    funext x
    exact deriv.neg
  have hdfneg : DifferentiableAt ℝ (deriv (fun x => -f x)) a := by
    rw [hdneg]
    exact hdf.neg
  have hsecond : deriv (deriv (fun x => -f x)) a = -deriv (deriv f) a := by
    rw [hdneg]
    exact deriv.neg
  obtain ⟨δ, hδ, hh⟩ := second_derivative_strict_minimum (fun x => -f x) a r hr
    (fun x hx => (hf x hx).neg) hdfneg
    (by rw [hdneg]; simp [hzero]) (by rw [hsecond]; exact neg_pos.mpr hneg)
  exact ⟨δ, hδ, fun x hx hxr => neg_lt_neg_iff.mp (hh x hx hxr)⟩

theorem quartic_zero_second_derivative_minimum :
    Specs.SingleVariableAnalysis.Ch05.SecondTest.quarticZeroSecondDerivativeMinimum := by
  have hfirst : HasDerivAt (fun x : ℝ => x ^ 4) 0 0 := by
    simpa using hasDerivAt_pow 4 (0 : ℝ)
  have hd : deriv (fun x : ℝ => x ^ 4) = fun x => 4 * x ^ 3 := by
    funext x
    simpa using (hasDerivAt_pow 4 x).deriv
  have hsecond : HasDerivAt (deriv (fun x : ℝ => x ^ 4)) 0 0 := by
    rw [hd]
    simpa using (hasDerivAt_pow 3 (0 : ℝ)).const_mul 4
  refine ⟨hfirst, hsecond, hfirst.deriv, hsecond.deriv, 1, by norm_num, ?_⟩
  intro x hx _
  simpa using (by decide : Even (4 : ℕ)).pow_pos (abs_pos.mp hx)

theorem negative_quartic_zero_second_derivative_maximum :
    Specs.SingleVariableAnalysis.Ch05.SecondTest.negativeQuarticZeroSecondDerivativeMaximum := by
  have hfirst : HasDerivAt (fun x : ℝ => -(x ^ 4)) 0 0 := by
    convert (hasDerivAt_pow 4 (0 : ℝ)).neg using 1 <;> norm_num
  have hd : deriv (fun x : ℝ => -(x ^ 4)) = fun x => -(4 * x ^ 3) := by
    funext x
    simpa using (hasDerivAt_pow 4 x).neg.deriv
  have hsecond : HasDerivAt (deriv (fun x : ℝ => -(x ^ 4))) 0 0 := by
    rw [hd]
    convert ((hasDerivAt_pow 3 (0 : ℝ)).const_mul 4).neg using 1 <;> norm_num
  refine ⟨hfirst, hsecond, hfirst.deriv, hsecond.deriv, 1, by norm_num, ?_⟩
  intro x hx _
  have hp : 0 < x ^ 4 := by
    exact (by decide : Even (4 : ℕ)).pow_pos (abs_pos.mp hx)
  simpa using neg_neg_of_pos hp

theorem cubic_zero_second_derivative_no_extremum :
    Specs.SingleVariableAnalysis.Ch05.SecondTest.cubicZeroSecondDerivativeNoExtremum := by
  have hd : deriv (fun x : ℝ => x ^ 3) = fun x => 3 * x ^ 2 := by
    funext x
    simpa using (hasDerivAt_pow 3 x).deriv
  have hsecond : HasDerivAt (deriv (fun x : ℝ => x ^ 3)) 0 0 := by
    rw [hd]
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_mul 3
  obtain ⟨hf, hd0, hmax, hmin⟩ := cubic_stationary_no_extremum
  exact ⟨hf, hsecond, hd0, hsecond.deriv, hmax, hmin⟩

end SingleVariableAnalysis
