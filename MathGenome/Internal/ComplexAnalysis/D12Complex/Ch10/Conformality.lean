import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.Conformality
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.RealComplexDifferential
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalHolomorphicInverse
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.Exponential

/-!
Angles and orientation (paper.tex:2324–2329). The pointwise geometry needs
only the complex derivative at that point. The neighborhood assertion uses
weak holomorphy and the already proved noncritical inverse theorem.
-/

noncomputable section
namespace D12Complex.Conformality

theorem conformal_differential :
    Specs.D12Complex.Ch10.Conformality.conformal_differential_type := by
  intro f c a hd hc
  obtain ⟨hl, hm⟩ := realDifferential_det f c a hd
  refine ⟨(hasComplexDerivativeAt_iff_real f c a).mp hd,
    realDifferential_apply f c a hd, realDifferential_matrix f c a hd,
    hl, hm, ?_⟩
  rw [hm]
  exact pow_pos (norm_pos_iff.mpr hc) 2

theorem multiplication_rotation_dilation :
    Specs.D12Complex.Ch10.Conformality.multiplication_rotation_dilation_type := by
  intro c hc
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hnC : (‖c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  refine ⟨norm_pos_iff.mpr hc, ?_, ?_, ?_, fun h => norm_mul c h⟩
  · simp [hn]
  · apply (div_eq_iff hnC).mpr
    simpa [mul_comm] using (Complex.norm_mul_exp_arg_mul_I c).symm
  · intro h
    field_simp

theorem multiplication_oriented_angles :
    Specs.D12Complex.Ch10.Conformality.multiplication_oriented_angles_type := by
  intro c v w hc hv hw
  have hr : (c * w) / (c * v) = w / v := mul_div_mul_left w v hc
  exact ⟨mul_ne_zero hc hv, mul_ne_zero hc hw, hr, congrArg Complex.arg hr⟩

theorem conformal_tangent_angles :
    Specs.D12Complex.Ch10.Conformality.conformal_tangent_angles_type := by
  intro f c a hd hc v w hv hw
  simp only [realDifferential_apply f c a hd]
  exact multiplication_oriented_angles c v w hc hv hw

theorem local_conformal_equivalence :
    Specs.D12Complex.Ch10.Conformality.local_conformal_equivalence_type := by
  intro Ω f a hf ha hc
  obtain ⟨U, V, h, haU, hfaV, hU, hp, hn, _⟩ :=
    LocalHolomorphicInverse.local_holomorphic_inverse Ω f a hf ha hc
  have hconf : ConformalOn U f := ⟨hp.1, hn⟩
  exact ⟨⟨U, haU, hconf⟩, U, V, h, haU, hfaV, hU, hp, hconf⟩

theorem exponential_counterexample :
    Specs.D12Complex.Ch10.Conformality.exponential_counterexample_type := by
  have hp : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hperiod : Function.Periodic E ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    intro z
    apply (Exponential.E_eq_E_iff _ _).mpr
    exact ⟨1, by simp⟩
  refine ⟨⟨Exponential.holomorphicOn_E, ?_⟩, hperiod, hp, ?_, ?_⟩
  · intro z _
    rw [Exponential.deriv_E]
    exact Exponential.E_ne_zero z
  · intro z
    exact ⟨by simpa only [ne_eq, add_eq_left] using hp, hperiod z⟩
  · intro hinj
    have heq := hinj (hperiod 0)
    exact hp (by simpa only [zero_add] using heq)

end D12Complex.Conformality
