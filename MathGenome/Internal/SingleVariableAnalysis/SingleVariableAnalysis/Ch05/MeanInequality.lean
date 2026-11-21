import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.MeanInequality
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Lagrange

/-!
# The scalar mean inequality

K03.05.mean_inequality, paper.tex:835–844. For the real target use Lagrange.
For the complex target set v = f y - f x and project onto the fixed real
functional z ↦ Re(conj(v) * z). This is the manuscript's projection scaled
by ‖v‖. Its endpoint difference is ‖v‖² and its derivative is bounded by
‖v‖ M. Cancel ‖v‖ when positive; the zero increment case is immediate.
All differentiation is over ℝ, with no endpoint derivative hypotheses.
-/

namespace SingleVariableAnalysis

open Set

theorem real_mean_inequality (f : ℝ → ℝ) (x y M : ℝ)
    (hxy : x < y) (_hM : 0 ≤ M) (hf : ContinuousOn f (Icc x y))
    (hd : ∀ t ∈ Ioo x y, DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Ioo x y, |deriv f t| ≤ M) :
    |f y - f x| ≤ M * (y - x) := by
  obtain ⟨c, hc, heq⟩ := lagrange_deriv f x y hxy hf hd
  rw [heq, abs_mul, abs_of_pos (sub_pos.mpr hxy)]
  exact mul_le_mul_of_nonneg_right (hb c hc) (sub_nonneg.mpr hxy.le)

theorem complex_mean_inequality (f : ℝ → ℂ) (x y M : ℝ)
    (hxy : x < y) (hM : 0 ≤ M) (hf : ContinuousOn f (Icc x y))
    (hd : ∀ t ∈ Ioo x y, DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Ioo x y, ‖deriv f t‖ ≤ M) :
    ‖f y - f x‖ ≤ M * (y - x) := by
  let v : ℂ := f y - f x
  by_cases hv : v = 0
  · change ‖v‖ ≤ M * (y - x)
    rw [hv, norm_zero]
    exact mul_nonneg hM (sub_nonneg.mpr hxy.le)
  let F : ℝ → ℝ := fun t => (star v * f t).re
  have hF : ContinuousOn F (Icc x y) :=
    Complex.continuous_re.comp_continuousOn (hf.const_mul (star v))
  have hF' (t : ℝ) (ht : t ∈ Ioo x y) :
      HasDerivAt F (star v * deriv f t).re t :=
    ((complex_hasDerivAt_iff_components _ _ _).mp
      ((hd t ht).hasDerivAt.const_mul (star v))).1
  obtain ⟨c, hc, heq⟩ := lagrange_deriv F x y hxy hF
    (fun t ht => (hF' t ht).differentiableAt)
  have hend : F y - F x = ‖v‖ ^ 2 := by
    change (star v * f y).re - (star v * f x).re = ‖v‖ ^ 2
    rw [← Complex.sub_re, ← mul_sub]
    change (star v * v).re = ‖v‖ ^ 2
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.mul_re]
  have hbound : deriv F c ≤ ‖v‖ * M := by
    rw [(hF' c hc).deriv]
    calc
      (star v * deriv f c).re ≤ ‖star v * deriv f c‖ := Complex.re_le_norm _
      _ = ‖v‖ * ‖deriv f c‖ := by rw [norm_mul, norm_star]
      _ ≤ ‖v‖ * M := mul_le_mul_of_nonneg_left (hb c hc) (norm_nonneg _)
  have hsq : ‖v‖ ^ 2 ≤ (‖v‖ * M) * (y - x) := by
    rw [← hend, heq]
    exact mul_le_mul_of_nonneg_right hbound (sub_nonneg.mpr hxy.le)
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  change ‖v‖ ≤ M * (y - x)
  exact le_of_mul_le_mul_left (by simpa only [pow_two, mul_assoc] using hsq) hpos

theorem real_mean_inequality_within (f f' : ℝ → ℝ) (x y M : ℝ)
    (hxy : x < y) (hM : 0 ≤ M) (hf : RelativeContinuous f (Icc x y))
    (hd : ∀ t ∈ Ioo x y, HasRealIncrementDerivativeWithin f (f' t) (Icc x y) t)
    (hb : ∀ t ∈ Ioo x y, |f' t| ≤ M) :
    |f y - f x| ≤ M * (y - x) := by
  have hder (t : ℝ) (ht : t ∈ Ioo x y) : HasDerivAt f (f' t) t :=
    (withinDerivative_interior_iff f (f' t) (Icc x y) t
      (by simpa only [interior_Icc] using ht)).mp (hd t ht)
  exact real_mean_inequality f x y M hxy hM
    (relativeContinuous_continuousOn f (Icc x y) hf)
    (fun t ht => (hder t ht).differentiableAt)
    (fun t ht => (hder t ht).deriv.symm ▸ hb t ht)

theorem complex_mean_inequality_within (f f' : ℝ → ℂ) (x y M : ℝ)
    (hxy : x < y) (hM : 0 ≤ M) (hf : RelativeContinuous f (Icc x y))
    (hd : ∀ t ∈ Ioo x y, HasRealIncrementDerivativeWithin f (f' t) (Icc x y) t)
    (hb : ∀ t ∈ Ioo x y, ‖f' t‖ ≤ M) :
    ‖f y - f x‖ ≤ M * (y - x) := by
  have hder (t : ℝ) (ht : t ∈ Ioo x y) : HasDerivAt f (f' t) t :=
    (withinDerivative_interior_iff f (f' t) (Icc x y) t
      (by simpa only [interior_Icc] using ht)).mp (hd t ht)
  exact complex_mean_inequality f x y M hxy hM
    (relativeContinuous_continuousOn f (Icc x y) hf)
    (fun t ht => (hder t ht).differentiableAt)
    (fun t ht => (hder t ht).deriv.symm ▸ hb t ht)

end SingleVariableAnalysis
