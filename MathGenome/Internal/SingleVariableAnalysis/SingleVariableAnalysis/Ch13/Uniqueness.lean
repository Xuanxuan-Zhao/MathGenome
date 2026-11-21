import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Differentiation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
Coefficient recovery for locally represented real-variable power series.
Convergence at c+r/2 forces a positive radius. A representative on the full
convergence interval agrees locally with f by uniqueness of ordinary sums.
Termwise differentiation and locality of derivatives then apply to f. At the
center the formal derivative series has only its k-th term, k! a_k.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter
open scoped Topology BigOperators ENNReal

namespace PowerSeriesUniqueness

/-- Evaluate a formal derivative at its center, before any infinite summation. -/
theorem term_center {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : ℕ → F) (c : ℝ) (k n : ℕ) :
    PowerSeriesDifferentiation.term a c k c n =
      if n = k then (k.factorial : ℝ) • a k else 0 := by
  rcases lt_trichotomy n k with h | h | h
  · simp [PowerSeriesDifferentiation.term, Nat.descFactorial_of_lt h, ne_of_lt h]
  · subst n
    simp [PowerSeriesDifferentiation.term, Nat.descFactorial_self]
  · simp [PowerSeriesDifferentiation.term, Nat.ne_of_gt (Nat.sub_pos_of_lt h), ne_of_gt h]

theorem real_center_derivative_sum (a : ℕ → ℝ) (c : ℝ) (k : ℕ) :
    RealSeriesHasSum (realFormalDerivativeTerm a c k c) ((k.factorial : ℝ) * a k) := by
  apply PowerSeriesDifferentiation.real_hasSum_of_hasSum
  have he : realFormalDerivativeTerm a c k c =
      fun n => if n = k then (k.factorial : ℝ) * a k else 0 := by
    funext n
    rw [← PowerSeriesDifferentiation.real_term_eq]
    simpa only [smul_eq_mul] using term_center a c k n
  rw [he]
  exact hasSum_ite_eq k _

theorem complex_center_derivative_sum (a : ℕ → ℂ) (c : ℝ) (k : ℕ) :
    ComplexSeriesHasSum (complexFormalDerivativeTerm a c k (c : ℂ))
      ((k.factorial : ℂ) * a k) := by
  apply PowerSeriesDifferentiation.complex_hasSum_of_hasSum
  have he : complexFormalDerivativeTerm a c k (c : ℂ) =
      fun n => if n = k then (k.factorial : ℂ) * a k else 0 := by
    funext n
    rw [← PowerSeriesDifferentiation.complex_term_eq]
    simpa only [Complex.real_smul, Complex.ofReal_natCast] using term_center a c k n
  rw [he]
  exact hasSum_ite_eq k _

/-- Ordinary local convergence, without assuming an absolute or positive-radius
certificate, supplies a representative to which the upstream calculus applies. -/
theorem real_local_representative (a : ℕ → ℝ) (c : ℝ) (f : ℝ → ℝ)
    (hf : ∃ r : ℝ, 0 < r ∧ ∀ x, |x-c| < r → RealPowerSeriesHasSum a c x (f x)) :
    0 < realPowerSeriesRadius a ∧ ∃ g : ℝ → ℝ,
      (∀ x, ENNReal.ofReal |x-c| < realPowerSeriesRadius a →
        RealPowerSeriesHasSum a c x (g x)) ∧ f =ᶠ[𝓝 c] g := by
  obtain ⟨r, hr, hf⟩ := hf
  have hbound : ENNReal.ofReal (r/2) ≤ realPowerSeriesRadius a := by
    by_contra h
    have hdiv := real_powerSeries_radius_diverges a c (c+r/2)
      (by simpa [abs_of_pos hr, abs_of_pos (by linarith : 0 < r/2)] using lt_of_not_ge h)
    exact hdiv ⟨f (c+r/2), hf _ (by simpa [abs_of_pos (by linarith : 0 < r/2)] using (by linarith : r/2 < r))⟩
  have hpos : 0 < realPowerSeriesRadius a :=
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < r/2)).trans_le hbound
  obtain ⟨g, hg⟩ := real_powerSeries_sum_exists a c
  refine ⟨hpos, g, hg, ?_⟩
  filter_upwards [Metric.ball_mem_nhds c (by linarith : 0 < r/2)] with x hx
  have hx' : |x-c| < r/2 := by simpa [Metric.mem_ball, Real.dist_eq] using hx
  exact real_powerSeries_sum_unique a c x _ _ (hf x (by linarith))
    (hg x ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < r/2)).mpr hx' |>.trans_le hbound))

theorem complex_local_representative (a : ℕ → ℂ) (c : ℝ) (f : ℝ → ℂ)
    (hf : ∃ r : ℝ, 0 < r ∧ ∀ x, |x-c| < r → ComplexPowerSeriesHasSum a c (x : ℂ) (f x)) :
    0 < complexPowerSeriesRadius a ∧ ∃ g : ℝ → ℂ,
      (∀ x, ENNReal.ofReal |x-c| < complexPowerSeriesRadius a →
        ComplexPowerSeriesHasSum a c (x : ℂ) (g x)) ∧ f =ᶠ[𝓝 c] g := by
  obtain ⟨r, hr, hf⟩ := hf
  have hbound : ENNReal.ofReal (r/2) ≤ complexPowerSeriesRadius a := by
    by_contra h
    have hdiv := complex_powerSeries_radius_diverges a c ((c+r/2 : ℝ) : ℂ)
      (by simpa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, abs_of_pos (by linarith : 0 < r/2)] using lt_of_not_ge h)
    exact hdiv ⟨f (c+r/2), hf _ (by simpa [abs_of_pos (by linarith : 0 < r/2)] using (by linarith : r/2 < r))⟩
  have hpos : 0 < complexPowerSeriesRadius a :=
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < r/2)).trans_le hbound
  obtain ⟨g, hg⟩ := complex_powerSeries_sum_exists a c
  refine ⟨hpos, g, hg, ?_⟩
  filter_upwards [Metric.ball_mem_nhds c (by linarith : 0 < r/2)] with x hx
  have hx' : |x-c| < r/2 := by simpa [Metric.mem_ball, Real.dist_eq] using hx
  exact complex_powerSeries_sum_unique a c (x : ℂ) _ _ (hf x (by linarith))
    (hg x ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < r/2)).mpr hx' |>.trans_le hbound))

end PowerSeriesUniqueness
open PowerSeriesUniqueness

theorem real_powerSeries_coefficient_formula :
    Specs.SingleVariableAnalysis.Ch13.Uniqueness.realCoefficientFormula := by
  intro a c f hf k
  obtain ⟨hpos, g, hg, hfg⟩ := real_local_representative a c f hf
  have hx : ENNReal.ofReal |c-c| < realPowerSeriesRadius a := by simpa using hpos
  obtain ⟨hval, hder⟩ := real_powerSeries_all_derivatives a c g hg k c hx
  constructor
  · rw [(hfg.iteratedDeriv k).eq_of_nhds]
    exact real_series_sum_unique _ _ _ hval (real_center_derivative_sum a c k)
  · rw [(hfg.iteratedDeriv (k+1)).eq_of_nhds]
    exact hder.congr_of_eventuallyEq (hfg.iteratedDeriv k)

theorem complex_powerSeries_coefficient_formula :
    Specs.SingleVariableAnalysis.Ch13.Uniqueness.complexCoefficientFormula := by
  intro a c f hf k
  obtain ⟨hpos, g, hg, hfg⟩ := complex_local_representative a c f hf
  have hx : ENNReal.ofReal |c-c| < complexPowerSeriesRadius a := by simpa using hpos
  obtain ⟨hval, hder⟩ := complex_powerSeries_all_derivatives a c g hg k c hx
  constructor
  · rw [(hfg.iteratedDeriv k).eq_of_nhds]
    exact complex_series_sum_unique _ _ _ hval (complex_center_derivative_sum a c k)
  · rw [(hfg.iteratedDeriv (k+1)).eq_of_nhds]
    exact hder.congr_of_eventuallyEq (hfg.iteratedDeriv k)

theorem real_powerSeries_coefficients_unique :
    Specs.SingleVariableAnalysis.Ch13.Uniqueness.realCoefficientUnique := by
  intro a b c f ha hb
  funext k
  have h := (real_powerSeries_coefficient_formula a c f ha k).1.symm.trans
    (real_powerSeries_coefficient_formula b c f hb k).1
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)) h

theorem complex_powerSeries_coefficients_unique :
    Specs.SingleVariableAnalysis.Ch13.Uniqueness.complexCoefficientUnique := by
  intro a b c f ha hb
  funext k
  have h := (complex_powerSeries_coefficient_formula a c f ha k).1.symm.trans
    (complex_powerSeries_coefficient_formula b c f hb k).1
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)) h

end SingleVariableAnalysis
