import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.HardyAveragingContinuous
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.HardyAveragingRealBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

noncomputable section
open MeasureTheory Set
open scoped unitInterval Topology

namespace ExpandedFA.PartV.HardyAveragingContinuous

open Spec

/-- Hardy averaging on complex C([0,1]), with the supremum norm. -/
def hardy : Spec.OperatorType := Spec.operatorValue

lemma dilation_integrable (f : Space) : Integrable (dilation f) :=
  (dilation f).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma hardy_apply (f : Space) (x : I) : hardy f x = ∫ r : I, f (r * x) := by
  change (∫ r : I, dilation f r) x = _
  exact ContinuousMap.integral_apply (dilation_integrable f) x

@[simp] lemma hardy_zero (f : Space) : hardy f 0 = f 0 := by
  rw [hardy_apply]
  simp

lemma extension_apply (f : Space) (x : I) : extension f (x : ℝ) = f x :=
  ContinuousMap.IccExtendCM_of_mem x.property

/-- The scalar integral on the interval is the same as the C([0,1])-valued
Bochner integral evaluated at x. -/
lemma hardy_apply_interval (f : Space) (x : I) :
    hardy f x = ∫ r in (0 : ℝ)..1, extension f (r * (x : ℝ)) := by
  rw [hardy_apply]
  have heq : (fun r : I => f (r * x)) =
      (fun r : I => extension f ((r : ℝ) * (x : ℝ))) := by
    funext r
    exact (extension_apply f (r * x)).symm
  rw [heq]
  rw [integral_subtype measurableSet_Icc (fun r : ℝ => extension f (r * (x : ℝ)))]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

lemma hardy_apply_pos (f : Space) (x : I) (hx : 0 < (x : ℝ)) :
    hardy f x = (x : ℂ)⁻¹ * ∫ t in (0 : ℝ)..(x : ℝ), extension f t := by
  rw [hardy_apply_interval, intervalIntegral.integral_comp_mul_right _ hx.ne']
  simp [Complex.real_smul]

theorem operator_formula : Spec.OperatorFormula := ⟨hardy_zero, hardy_apply_pos⟩

@[simp] lemma hardy_const (c : ℂ) : hardy (ContinuousMap.const I c) = ContinuousMap.const I c := by
  ext x
  rw [hardy_apply]
  simp

lemma hardy_norm_le : ‖hardy‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have h : ∀ r : I, ‖dilation f r‖ ≤ ‖f‖ := by
    intro r
    exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun x =>
      ContinuousMap.norm_coe_le_norm f (r * x)
  simpa [hardy, operatorValue, Spec.average] using
    norm_integral_le_of_norm_le_const (μ := volume) (Filter.Eventually.of_forall h)

theorem norm_one : Spec.NormOne := by
  change ‖hardy‖ = 1
  apply le_antisymm hardy_norm_le
  have h := hardy.le_opNorm (ContinuousMap.const I (1 : ℂ))
  rw [hardy_const] at h
  simpa using h

/-- A vanishing Hardy average has a vanishing primitive, including at zero. -/
lemma primitive_eq_zero_of_hardy_eq_zero (f : Space) (hf : hardy f = 0) (x : I) :
    ∫ t in (0 : ℝ)..(x : ℝ), extension f t = 0 := by
  by_cases hx : (x : ℝ) = 0
  · simp [hx]
  · have hp := congrArg (fun g : Space => g x) hf
    rw [hardy_apply_pos f x (lt_of_le_of_ne x.property.1 (Ne.symm hx))] at hp
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    exact (mul_eq_zero.mp hp).resolve_left (inv_ne_zero hxc)

lemma hardy_ker_eq_zero (f : Space) (hf : hardy f = 0) : f = 0 := by
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, ∫ s in (0 : ℝ)..t, extension f s = 0 := by
    intro t ht
    exact primitive_eq_zero_of_hardy_eq_zero f hf ⟨t, ht⟩
  ext x
  have hd := intervalIntegral.integral_hasDerivAt_right
    ((extension f).continuous.intervalIntegrable 0 (x : ℝ))
    (extension f).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    (extension f).continuous.continuousAt
  have hz : HasDerivWithinAt (fun t : ℝ => ∫ s in (0 : ℝ)..t, extension f s)
      0 (Icc 0 1) (x : ℝ) :=
    (hasDerivWithinAt_const (x : ℝ) (Icc (0 : ℝ) 1) (0 : ℂ)).congr
      (fun t ht => hp t ht) (hp x x.property)
  have hu := uniqueDiffOn_Icc zero_lt_one (x : ℝ) x.property
  have heq := (hd.hasDerivWithinAt.derivWithin hu).symm.trans (hz.derivWithin hu)
  simpa only [extension_apply, ContinuousMap.zero_apply] using heq

theorem no_zero_eigenvalue : Spec.NoZeroEigenvalue := by
  change Function.Injective hardy
  intro f g h
  have hz : hardy (f - g) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (hardy_ker_eq_zero _ hz)

/-- The positive-real-part powers are genuine continuous functions at zero. -/
def continuousPower (b : ℂ) (hb : 0 < b.re) : Space :=
  ⟨fun x => (x : ℂ) ^ b,
    (Complex.continuous_ofReal_cpow_const hb).comp continuous_subtype_val⟩

lemma continuousPower_ne_zero (b : ℂ) (hb : 0 < b.re) : continuousPower b hb ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : Space => f 1) h
  simp [continuousPower] at h1

lemma hardy_continuousPower (b : ℂ) (hb : 0 < b.re) :
    hardy (continuousPower b hb) = (b + 1)⁻¹ • continuousPower b hb := by
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hb1 : b + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  ext x
  by_cases hx : (x : ℝ) = 0
  · have hx0 : x = 0 := Subtype.ext hx
    subst x
    simp [continuousPower, Complex.zero_cpow hb0]
  · have hxp : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx)
    rw [hardy_apply_pos _ x hxp]
    have hext : (∫ t in (0 : ℝ)..(x : ℝ), extension (continuousPower b hb) t) =
        ∫ t in (0 : ℝ)..(x : ℝ), (t : ℂ) ^ b := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hxp.le] at ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans x.property.2⟩
      exact extension_apply (continuousPower b hb) ⟨t, htI⟩
    rw [hext, integral_cpow (Or.inl (by linarith : -1 < b.re))]
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    simp only [Complex.ofReal_zero]
    rw [Complex.zero_cpow hb1, sub_zero, Complex.cpow_add _ _ hxc, Complex.cpow_one]
    simp only [ContinuousMap.smul_apply, continuousPower, ContinuousMap.coe_mk, smul_eq_mul]
    field_simp

/-- Every reciprocal parameter with real part greater than one is an eigenvalue. -/
lemma eigenvalue_of_inverse_re_gt_one (z : ℂ) (hz : 1 < (z⁻¹).re) :
    ∃ f : Space, f ≠ 0 ∧ hardy f = z • f := by
  have hpos : 0 < (z⁻¹ - 1).re := by simpa using sub_pos.mpr hz
  refine ⟨continuousPower (z⁻¹ - 1) hpos, continuousPower_ne_zero _ _, ?_⟩
  simpa using hardy_continuousPower (z⁻¹ - 1) hpos

/-- The elementary disk/inverse-parameter correspondence, with zero excluded. -/
lemma inverse_re_gt_one_iff (z : ℂ) (hz : z ≠ 0) :
    1 < (z⁻¹).re ↔ ‖z - (1 / 2 : ℂ)‖ < (1 / 2 : ℝ) := by
  have hsq : ‖z - (1 / 2 : ℂ)‖ ^ 2 = Complex.normSq z - z.re + 1 / 4 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    norm_num
    ring
  rw [Complex.inv_re, lt_div_iff₀ (Complex.normSq_pos.mpr hz), one_mul]
  constructor
  · intro h
    exact (sq_lt_sq₀ (norm_nonneg _) (by norm_num : 0 ≤ (1 / 2 : ℝ))).mp (by nlinarith)
  · intro h
    have := (sq_lt_sq₀ (norm_nonneg _) (by norm_num : 0 ≤ (1 / 2 : ℝ))).mpr h
    nlinarith

lemma inverse_re_lt_one_iff (z : ℂ) (hz : z ≠ 0) :
    (z⁻¹).re < 1 ↔ (1 / 2 : ℝ) < ‖z - (1 / 2 : ℂ)‖ := by
  have hsq : ‖z - (1 / 2 : ℂ)‖ ^ 2 = Complex.normSq z - z.re + 1 / 4 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    norm_num
    ring
  rw [Complex.inv_re, div_lt_iff₀ (Complex.normSq_pos.mpr hz), one_mul]
  constructor
  · intro h
    exact (sq_lt_sq₀ (by norm_num : 0 ≤ (1 / 2 : ℝ)) (norm_nonneg _)).mp (by nlinarith)
  · intro h
    have := (sq_lt_sq₀ (by norm_num : 0 ≤ (1 / 2 : ℝ)) (norm_nonneg _)).mpr h
    nlinarith

lemma open_disk_eigenvalues (z : ℂ) (hz : ‖z - (1 / 2 : ℂ)‖ < (1 / 2 : ℝ)) :
    ∃ f : Space, f ≠ 0 ∧ hardy f = z • f := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  exact eigenvalue_of_inverse_re_gt_one z ((inverse_re_gt_one_iff z hz0).mpr hz)

/-- Already the real interval (1/2,1) of power eigenvalues rules out compactness. -/
theorem noncompact : Spec.Noncompact := by
  change ¬ IsCompactOperator hardy
  intro hc
  have hcompact : Compactness.IsCompactLinearMap hardy.toLinearMap :=
    (Compactness.compact_iff_isCompactOperator _).mpr hc
  have hfin := Fredholm.compact_eigenvalues_finite_away_from_zero hardy hcompact
    (1 / 2) (by norm_num)
  have hm : MapsTo (fun r : ℝ => (r : ℂ)) (Ioo (1 / 2 : ℝ) 1)
      {z : ℂ | (∃ f : Space, f ≠ 0 ∧ hardy f = z • f) ∧ (1 / 2 : ℝ) ≤ ‖z‖} := by
    intro r hr
    have hrpos : 0 < r := by linarith [hr.1]
    refine ⟨eigenvalue_of_inverse_re_gt_one (r : ℂ) ?_, ?_⟩
    · simpa only [← Complex.ofReal_inv, Complex.ofReal_re] using (one_lt_inv₀ hrpos).mpr hr.2
    · simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos] using hr.1.le
  exact (Ioo_infinite (by norm_num : (1 / 2 : ℝ) < 1))
    (hfin.of_injOn hm (by intro r _ s _ h; exact Complex.ofReal_injective h))

lemma eigenvalue_mem_spectrum (z : ℂ) (f : Space) (hf : f ≠ 0)
    (he : hardy f = z • f) : z ∈ spectrum ℂ hardy := by
  change z ∈ Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue
    ℂ (Space →L[ℂ] Space) hardy
  rw [BanachAlgebra.operator_spectrum_iff_no_bounded_inverse]
  rintro ⟨S, hleft, _⟩
  have h := hleft f
  rw [he, sub_self, map_zero] at h
  exact hf h.symm

lemma closed_disk_subset_spectrum :
    {z : ℂ | ‖z - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ)} ⊆ spectrum ℂ hardy := by
  have hball : Metric.ball (1 / 2 : ℂ) (1 / 2) ⊆ spectrum ℂ hardy := by
    intro z hz
    obtain ⟨f, hf, he⟩ := open_disk_eigenvalues z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    exact eigenvalue_mem_spectrum z f hf he
  have hclosed : IsClosed (spectrum ℂ hardy) := spectrum.isClosed (𝕜 := ℂ) hardy
  have hclosure : closure (Metric.ball (1 / 2 : ℂ) (1 / 2)) ⊆ spectrum ℂ hardy :=
    closure_minimal hball hclosed
  rw [closure_ball _ (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hclosure
  simpa only [Metric.closedBall, dist_eq_norm] using hclosure

/-- The remaining spectral inclusion follows from the source's explicit inverse.
This is an assembly lemma, not a replacement for proving that inverse. -/
theorem spectrum_disk_of_exterior_resolvent (hres : Spec.ExteriorResolvent) : Spec.SpectrumDisk := by
  change spectrum ℂ hardy = _
  apply Subset.antisymm _ closed_disk_subset_spectrum
  intro z hz
  by_contra hout
  have hnorm : (1 / 2 : ℝ) < ‖z - (1 / 2 : ℂ)‖ := lt_of_not_ge hout
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hnorm
  obtain ⟨R, hleft, hright, _⟩ := hres z hz0 ((inverse_re_lt_one_iff z hz0).mpr hnorm)
  change z ∈ Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue
    ℂ (Space →L[ℂ] Space) hardy at hz
  rw [BanachAlgebra.operator_spectrum_iff_no_bounded_inverse] at hz
  apply hz
  refine ⟨-R, ?_, ?_⟩
  · intro f
    change -R (z • f - hardy f) = f
    rw [← neg_sub (hardy f), map_neg, neg_neg]
    exact hleft f
  · intro f
    change z • -R f - hardy (-R f) = f
    rw [map_neg, smul_neg, sub_neg_eq_add, neg_add_eq_sub]
    exact hright f

/-- The primitive equation holds at every positive point, including one. -/
lemma primitive_of_eigenfunction (z : ℂ) (f : Space) (he : hardy f = z • f)
    (x : I) (hx : 0 < (x : ℝ)) :
    (∫ t in (0 : ℝ)..(x : ℝ), extension f t) = (x : ℂ) * z * f x := by
  have h := congrArg (fun g : Space => g x) he
  rw [hardy_apply_pos f x hx] at h
  change (x : ℂ)⁻¹ * _ = z * f x at h
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  calc
    _ = (x : ℂ) * ((x : ℂ)⁻¹ * ∫ t in (0 : ℝ)..(x : ℝ), extension f t) := by
      rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
    _ = _ := by rw [h]; ring

/-- Multiplying the primitive by the integrating factor makes it constant.
FTC applies globally to the constant extension, so no derivative of f is assumed. -/
lemma weighted_primitive_of_eigenfunction (z : ℂ) (hz : z ≠ 0)
    (f : Space) (he : hardy f = z • f) (x : I) (hx : 0 < (x : ℝ)) :
    (∫ t in (0 : ℝ)..(x : ℝ), extension f t) * (x : ℂ) ^ (-z⁻¹) = z * f 1 := by
  let P : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, extension f t
  let G : ℝ → ℂ := fun x => P x * (x : ℂ) ^ (-z⁻¹)
  have hder : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt G 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have hP := intervalIntegral.integral_hasDerivAt_right
      ((extension f).continuous.intervalIntegrable 0 t)
      (extension f).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      (extension f).continuous.continuousAt
    have hpow := hasDerivAt_ofReal_cpow_const ht0 (neg_ne_zero.mpr (inv_ne_zero hz))
    have hprim : P t = (t : ℂ) * z * extension f t := by
      have hext := extension_apply f ⟨t, ht.1.le, ht.2⟩
      change extension f t = _ at hext
      rw [hext]
      exact primitive_of_eigenfunction z f he ⟨t, ht.1.le, ht.2⟩ ht.1
    convert hP.mul hpow using 1
    change 0 = extension f t * (t : ℂ) ^ (-z⁻¹) + P t * _
    rw [hprim, Complex.cpow_sub _ _ htc, Complex.cpow_one]
    field_simp
    ring
  have hbound := (convex_Ioc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hder t ht).hasDerivWithinAt)
    (fun t ht => by simp : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(0 : ℂ)‖ ≤ (0 : ℝ))
    ⟨hx, x.property.2⟩ (show (1 : ℝ) ∈ Ioc (0 : ℝ) 1 by norm_num)
  have heq : G (x : ℝ) = G 1 := by
    have hzero : G 1 - G (x : ℝ) = 0 := norm_le_zero_iff.mp (by simpa using hbound)
    exact (sub_eq_zero.mp hzero).symm
  have hP1 : P 1 = z * f 1 := by
    simpa using primitive_of_eigenfunction z f he 1 (by norm_num)
  change P (x : ℝ) * (x : ℂ) ^ (-z⁻¹) = P 1 * (1 : ℂ) ^ (-z⁻¹) at heq
  simpa only [Complex.one_cpow, mul_one, hP1] using heq

/-- Every eigenfunction has the source's power formula away from zero. -/
lemma eigenfunction_power_pos (z : ℂ) (hz : z ≠ 0)
    (f : Space) (he : hardy f = z • f) (x : I) (hx : 0 < (x : ℝ)) :
    f x = f 1 * (x : ℂ) ^ (z⁻¹ - 1) := by
  have h := weighted_primitive_of_eigenfunction z hz f he x hx
  rw [primitive_of_eigenfunction z f he x hx, Complex.cpow_neg] at h
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hp0 : (x : ℂ) ^ z⁻¹ ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hx0)
  have h' := (mul_inv_eq_iff_eq_mul₀ hp0).mp h
  rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one, ← mul_div_assoc]
  apply (eq_div_iff hx0).mpr
  apply (mul_left_cancel₀ hz)
  calc
    z * (f x * (x : ℂ)) = (x : ℂ) * z * f x := by ring
    _ = z * f 1 * (x : ℂ) ^ z⁻¹ := h'
    _ = z * (f 1 * (x : ℂ) ^ z⁻¹) := by ring

/-- Positive points are dense in the unit interval. -/
lemma eq_of_eq_pos (f g : Space)
    (h : ∀ x : I, 0 < (x : ℝ) → f x = g x) : f = g := by
  have heq : EqOn (extension f) (extension g) (Ioc (0 : ℝ) 1) := by
    intro t ht
    have hf := extension_apply f ⟨t, ht.1.le, ht.2⟩
    have hg := extension_apply g ⟨t, ht.1.le, ht.2⟩
    change extension f t = _ at hf
    change extension g t = _ at hg
    rw [hf, hg]
    exact h _ ht.1
  have hcl := heq.closure (extension f).continuous (extension g).continuous
  rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)] at hcl
  ext x
  simpa only [extension_apply] using hcl x.property

lemma eigenfunction_one_ne_zero (z : ℂ) (hz : z ≠ 0)
    (f : Space) (hf : f ≠ 0) (he : hardy f = z • f) : f 1 ≠ 0 := by
  intro hzero
  apply hf
  apply eq_of_eq_pos
  intro x hx
  simpa [hzero] using eigenfunction_power_pos z hz f he x hx

lemma eigenfunction_zero (z : ℂ) (hz : z ≠ 1)
    (f : Space) (he : hardy f = z • f) : f 0 = 0 := by
  have h := congrArg (fun g : Space => g 0) he
  change hardy f 0 = z * f 0 at h
  rw [hardy_zero] at h
  exact (mul_eq_zero.mp (show (z - 1) * f 0 = 0 by rw [sub_mul, one_mul, ← h, sub_self])).resolve_left
    (sub_ne_zero.mpr hz)

/-- Continuity at zero forces strict positivity of the exponent's real part,
except for the constant eigenfunctions. -/
lemma eigenfunction_inverse_re (z : ℂ) (hz : z ≠ 0) (f : Space)
    (hf : f ≠ 0) (he : hardy f = z • f) : 1 < (z⁻¹).re ∨ z = 1 := by
  by_cases hz1 : z = 1
  · exact Or.inr hz1
  left
  by_contra hpos
  have hb : (z⁻¹ - 1).re ≤ 0 := by simpa using sub_nonpos.mpr (le_of_not_gt hpos)
  have hlim : Filter.Tendsto (fun t : ℝ => ‖extension f t‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Filter.Tendsto (fun t : ℝ => ‖extension f t‖) (𝓝[>] (0 : ℝ))
        (𝓝 ‖extension f (0 : ℝ)‖) :=
      (extension f).continuous.continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds
    have hext0 : extension f (0 : ℝ) = f 0 := extension_apply f 0
    simpa only [hext0, eigenfunction_zero z hz1 f he, norm_zero] using h
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ‖f 1‖ ≤ ‖extension f t‖ := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    have hext := extension_apply f ⟨t, ht.1.le, ht.2.le⟩
    change extension f t = _ at hext
    rw [hext, eigenfunction_power_pos z hz f he ⟨t, ht.1.le, ht.2.le⟩ ht.1, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
    exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      ht.1 ht.2.le hb)
  have hzero := ge_of_tendsto hlim hbound
  exact eigenfunction_one_ne_zero z hz f hf he (norm_le_zero_iff.mp hzero)

lemma fixed_function_constant (f : Space) (he : hardy f = f) :
    f = ContinuousMap.const I (f 1) := by
  apply eq_of_eq_pos
  intro x hx
  simpa using eigenfunction_power_pos 1 one_ne_zero f (by simpa using he) x hx

/-- Complete classification, including the value at the singular endpoint. -/
theorem power_eigenfunctions : Spec.PowerEigenfunctions := by
  intro z hz f hf
  change hardy f = z • f ↔ _
  constructor
  · intro he
    refine ⟨eigenfunction_inverse_re z hz f hf he,
      f 1, eigenfunction_one_ne_zero z hz f hf he, ?_⟩
    intro x
    by_cases hx : (x : ℝ) = 0
    · have hx0 : x = 0 := Subtype.ext hx
      subst x
      by_cases hz1 : z = 1
      · have hc := fixed_function_constant f (by simpa [hz1] using he)
        simpa [powerProfile, hz1] using congrArg (fun g : Space => g 0) hc
      · simp [powerProfile, hz1, eigenfunction_zero z hz1 f he]
    · simpa only [powerProfile, ite_eq_right hx] using
        eigenfunction_power_pos z hz f he x (lt_of_le_of_ne x.property.1 (Ne.symm hx))
  · rintro ⟨hcond, c, hc, hp⟩
    rcases hcond with hpos | rfl
    · have hb : 0 < (z⁻¹ - 1).re := by simpa using sub_pos.mpr hpos
      have hfc : f = c • continuousPower (z⁻¹ - 1) hb := by
        apply eq_of_eq_pos
        intro x hx
        simpa [powerProfile, hx.ne', continuousPower] using hp x
      rw [hfc, map_smul, hardy_continuousPower]
      simp only [sub_add_cancel, inv_inv, smul_smul, mul_comm c z]
    · have hfc : f = ContinuousMap.const I c := by
        ext x
        simpa [powerProfile] using hp x
      simpa only [one_smul, hfc] using hardy_const c

/-- The open disk and the constant eigenvalue are the entire point spectrum. -/
theorem eigenvalue_disk : Spec.EigenvalueDisk := by
  change {z : ℂ | ∃ f : Space, f ≠ 0 ∧ hardy f = z • f} = _
  ext z
  constructor
  · rintro ⟨f, hf, he⟩
    have hz : z ≠ 0 := by
      intro hzero
      have hk : hardy f = 0 := he.trans (by rw [hzero]; exact zero_smul ℂ f)
      exact hf (hardy_ker_eq_zero f hk)
    rcases eigenfunction_inverse_re z hz f hf he with hpos | hz1
    · exact Or.inl ((inverse_re_gt_one_iff z hz).mp hpos)
    · exact Or.inr hz1
  · rintro (hz | rfl)
    · exact open_disk_eigenvalues z hz
    · refine ⟨ContinuousMap.const I (1 : ℂ), ?_, ?_⟩
      · intro h
        have h0 := congrArg (fun f : Space => f 0) h
        simp at h0
      · simpa only [one_smul] using hardy_const (1 : ℂ)

/-- The singular weight is integrable precisely in the range needed outside
of the spectral disk. -/
lemma weight_integrable (a : ℂ) (ha : a.re < 1) :
    Integrable (fun r : I => (r : ℂ) ^ (-a)) := by
  have hi : IntervalIntegrable (fun r : ℝ => (r : ℂ) ^ (-a)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' (by simpa only [Complex.neg_re] using (neg_lt_neg ha))
  exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi)

lemma weight_integral (a : ℂ) (ha : a.re < 1) :
    (∫ r : I, (r : ℂ) ^ (-a)) = (1 - a)⁻¹ := by
  rw [integral_subtype measurableSet_Icc (fun r : ℝ => (r : ℂ) ^ (-a)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by simpa only [Complex.neg_re] using (neg_lt_neg ha)))]
  have hne : -a + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  simp only [Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero,
    Complex.zero_cpow hne, sub_zero, one_div]
  congr 1
  ring

lemma weight_norm_integral (a : ℂ) (ha : a.re < 1) :
    (∫ r : I, ‖(r : ℂ) ^ (-a)‖) = 1 / (1 - a.re) := by
  rw [integral_subtype measurableSet_Icc (fun r : ℝ => ‖(r : ℂ) ^ (-a)‖),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have heq : (∫ r in (0 : ℝ)..1, ‖(r : ℂ) ^ (-a)‖) =
      ∫ r in (0 : ℝ)..1, r ^ (-a.re) := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall fun r hr => by
      rw [uIoc_of_le zero_le_one] at hr
      simpa only [Complex.neg_re] using Complex.norm_cpow_eq_rpow_re_of_pos hr.1 (-a)
  rw [heq, integral_rpow (Or.inl (by linarith : -1 < -a.re))]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : -a.re + 1 ≠ 0), sub_zero]
  congr 1
  ring

/-- A Banach-space integral gives continuity at the endpoint as well as
boundedness of the weighted dilation average. -/
def weightedAverage (a : ℂ) (f : Space) : Space :=
  ∫ r : I, (r : ℂ) ^ (-a) • dilation f r

lemma weighted_dilation_integrable (a : ℂ) (ha : a.re < 1) (f : Space) :
    Integrable (fun r : I => (r : ℂ) ^ (-a) • dilation f r) := by
  exact (weight_integrable a ha).smul_bdd ‖f‖ (dilation f).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun r =>
      (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun x =>
        ContinuousMap.norm_coe_le_norm f (r * x))

lemma weightedAverage_apply (a : ℂ) (ha : a.re < 1) (f : Space) (x : I) :
    weightedAverage a f x = ∫ r : I, (r : ℂ) ^ (-a) * f (r * x) := by
  exact ContinuousMap.integral_apply (weighted_dilation_integrable a ha f) x

lemma weightedAverage_zero (a : ℂ) (ha : a.re < 1) (f : Space) :
    weightedAverage a f 0 = (1 - a)⁻¹ * f 0 := by
  rw [weightedAverage_apply a ha f 0]
  simp only [mul_zero]
  rw [integral_mul_const, weight_integral a ha]

lemma weightedAverage_bound (a : ℂ) (ha : a.re < 1) (f : Space) :
    ‖weightedAverage a f‖ ≤ ‖f‖ / (1 - a.re) := by
  calc
    ‖weightedAverage a f‖ ≤ ∫ r : I, ‖(r : ℂ) ^ (-a) • dilation f r‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ r : I, ‖(r : ℂ) ^ (-a)‖ * ‖f‖ := by
      apply integral_mono (weighted_dilation_integrable a ha f).norm
        ((weight_integrable a ha).norm.mul_const ‖f‖)
      intro r
      change ‖(r : ℂ) ^ (-a) • dilation f r‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        ((ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun x =>
          ContinuousMap.norm_coe_le_norm f (r * x)) (norm_nonneg _)
    _ = ‖f‖ / (1 - a.re) := by
      rw [integral_mul_const, weight_norm_integral a ha]
      ring

/-- Weighted averaging as a bounded operator. -/
def weightedOperator (a : ℂ) (ha : a.re < 1) : Space →L[ℂ] Space :=
  ({ toFun := weightedAverage a
     map_add' := by
       intro f g
       have h : (fun r : I => (r : ℂ) ^ (-a) • dilation (f + g) r) =
           (fun r : I => (r : ℂ) ^ (-a) • dilation f r +
             (r : ℂ) ^ (-a) • dilation g r) := by ext r x; simp [dilation, mul_add]
       exact (congrArg (fun g : I → Space => ∫ r, g r) h).trans
         (integral_add (weighted_dilation_integrable a ha f) (weighted_dilation_integrable a ha g))
     map_smul' := by
       intro c f
       have h : (fun r : I => (r : ℂ) ^ (-a) • dilation (c • f) r) =
           (fun r : I => c • ((r : ℂ) ^ (-a) • dilation f r)) := by
         ext r x; simp [dilation]; ring
       exact (congrArg (fun g : I → Space => ∫ r, g r) h).trans (integral_smul c _) } : Space →ₗ[ℂ] Space).mkContinuous
    (1 / (1 - a.re)) (by
      intro f
      change ‖weightedAverage a f‖ ≤ (1 / (1 - a.re)) * ‖f‖
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using weightedAverage_bound a ha f)

lemma weighted_integral_intervalIntegrable (a : ℂ) (ha : a.re < 1) (f : Space) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-a) * extension f t) volume 0 x :=
  (intervalIntegral.intervalIntegrable_cpow'
    (by simpa only [Complex.neg_re] using neg_lt_neg ha)).mul_continuousOn
    (extension f).continuous.continuousOn

lemma weightedAverage_apply_interval (a : ℂ) (ha : a.re < 1) (f : Space) (x : I) :
    weightedAverage a f x =
      ∫ r in (0 : ℝ)..1, (r : ℂ) ^ (-a) * extension f (r * (x : ℝ)) := by
  rw [weightedAverage_apply a ha f x]
  have heq : (fun r : I => (r : ℂ) ^ (-a) * f (r * x)) =
      (fun r : I => (r : ℂ) ^ (-a) * extension f ((r : ℝ) * (x : ℝ))) := by
    funext r
    rw [← extension_apply f (r * x)]
    rfl
  rw [heq, integral_subtype measurableSet_Icc
    (fun r : ℝ => (r : ℂ) ^ (-a) * extension f (r * (x : ℝ))),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

/-- The weighted dilation integral is exactly the source's improper integral. -/
lemma weightedAverage_apply_pos (a : ℂ) (ha : a.re < 1) (f : Space)
    (x : I) (hx : 0 < (x : ℝ)) :
    weightedAverage a f x = (x : ℂ) ^ (a - 1) *
      ∫ t in (0 : ℝ)..(x : ℝ), (t : ℂ) ^ (-a) * extension f t := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hp0 : (x : ℂ) ^ a ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hprod : (∫ r in (0 : ℝ)..1,
      ((r * (x : ℝ) : ℝ) : ℂ) ^ (-a) * extension f (r * (x : ℝ))) =
      (x : ℂ) ^ (-a) * weightedAverage a f x := by
    rw [weightedAverage_apply_interval a ha f x, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    dsimp only
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.1 hx.le]
    ring
  have hscale := intervalIntegral.integral_comp_mul_right
    (fun t : ℝ => (t : ℂ) ^ (-a) * extension f t) hx.ne' (a := 0) (b := 1)
  rw [hprod, Complex.cpow_neg] at hscale
  simp only [zero_mul, one_mul, Complex.real_smul, Complex.ofReal_inv] at hscale
  rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
  calc
    weightedAverage a f x = (x : ℂ) ^ a * ((x : ℂ) ^ a)⁻¹ * weightedAverage a f x := by
      rw [mul_inv_cancel₀ hp0, one_mul]
    _ = (x : ℂ) ^ a * ((x : ℂ)⁻¹ *
        ∫ t in (0 : ℝ)..(x : ℝ), (t : ℂ) ^ (-a) * extension f t) := by
      rw [mul_assoc, hscale]
    _ = _ := by ring

lemma mul_weightedAverage (a : ℂ) (ha : a.re < 1) (f : Space)
    (x : I) (hx : 0 < (x : ℝ)) :
    (x : ℂ) * weightedAverage a f x = (x : ℂ) ^ a *
      ∫ t in (0 : ℝ)..(x : ℝ), (t : ℂ) ^ (-a) * extension f t := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [weightedAverage_apply_pos a ha f x hx, Complex.cpow_sub _ _ hx0, Complex.cpow_one]
  field_simp

/-- The continuous primitive x H_a f has derivative f + a H_a f in (0,1). -/
lemma weightedPrimitive_hasDerivAt (a : ℂ) (ha : a.re < 1) (ha0 : a ≠ 0)
    (f : Space) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * extension (weightedAverage a f) s)
      (extension f t + a * extension (weightedAverage a f) t) t := by
  let w : ℝ → ℂ := fun s => (s : ℂ) ^ (-a) * extension f s
  have hw : ContinuousOn w (Ioi (0 : ℝ)) := by
    apply continuousOn_of_forall_continuousAt
    intro s hs
    exact (Complex.continuousAt_ofReal_cpow_const s (-a) (Or.inr hs.ne')).mul
      (extension f).continuous.continuousAt
  have hJ := intervalIntegral.integral_hasDerivAt_right
    (weighted_integral_intervalIntegrable a ha f t)
    (hw.stronglyMeasurableAtFilter isOpen_Ioi t ht.1)
    (hw.continuousAt (isOpen_Ioi.mem_nhds ht.1))
  have hU := (hasDerivAt_ofReal_cpow_const ht.1.ne' ha0).mul hJ
  have heq : (fun s : ℝ => (s : ℂ) * extension (weightedAverage a f) s) =ᶠ[𝓝 t]
      (fun s : ℝ => (s : ℂ) ^ a * ∫ r in (0 : ℝ)..s, w r) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hext := extension_apply (weightedAverage a f) ⟨s, hs.1.le, hs.2.le⟩
    change extension (weightedAverage a f) s = _ at hext
    rw [hext]
    exact mul_weightedAverage a ha f ⟨s, hs.1.le, hs.2.le⟩ hs.1
  have hH : extension (weightedAverage a f) t = (t : ℂ) ^ (a - 1) *
      ∫ r in (0 : ℝ)..t, w r := by
    have hext := extension_apply (weightedAverage a f) ⟨t, ht.1.le, ht.2.le⟩
    change extension (weightedAverage a f) t = _ at hext
    rw [hext]
    exact weightedAverage_apply_pos a ha f ⟨t, ht.1.le, ht.2.le⟩ ht.1
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
  have hp0 : (t : ℂ) ^ a ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl ht0)
  convert hU.congr_of_eventuallyEq heq using 1
  rw [hH, Complex.cpow_neg]
  field_simp
  ring

/-- The explicit inverse of Q - z I, in the exterior parameter range. -/
def exteriorInverse (z : ℂ) (ha : (z⁻¹).re < 1) : Space →L[ℂ] Space :=
  (-z⁻¹) • ContinuousLinearMap.id ℂ Space - z⁻¹ ^ 2 • weightedOperator z⁻¹ ha

lemma exteriorInverse_apply (z : ℂ) (ha : (z⁻¹).re < 1) (f : Space) (x : I) :
    exteriorInverse z ha f x = -z⁻¹ * f x - z⁻¹ ^ 2 * weightedAverage z⁻¹ f x := rfl

lemma exteriorInverse_extension (z : ℂ) (ha : (z⁻¹).re < 1) (f : Space)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    extension (exteriorInverse z ha f) t = -z⁻¹ * extension f t -
      z⁻¹ ^ 2 * extension (weightedAverage z⁻¹ f) t := by
  have hR := extension_apply (exteriorInverse z ha f) ⟨t, ht⟩
  have hf := extension_apply f ⟨t, ht⟩
  have hH := extension_apply (weightedAverage z⁻¹ f) ⟨t, ht⟩
  change extension (exteriorInverse z ha f) t = _ at hR
  change extension f t = _ at hf
  change extension (weightedAverage z⁻¹ f) t = _ at hH
  rw [hR, hf, hH]
  exact exteriorInverse_apply z ha f ⟨t, ht⟩

lemma exteriorInverse_bound (z : ℂ) (ha : (z⁻¹).re < 1) :
    ‖exteriorInverse z ha‖ ≤ ‖z⁻¹‖ + ‖z⁻¹‖ ^ 2 / (1 - (z⁻¹).re) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg _) (div_nonneg (sq_nonneg _) (sub_pos.mpr ha).le))
  intro f
  change ‖(-z⁻¹) • f - z⁻¹ ^ 2 • weightedAverage z⁻¹ f‖ ≤ _
  calc
    _ ≤ ‖(-z⁻¹) • f‖ + ‖z⁻¹ ^ 2 • weightedAverage z⁻¹ f‖ := norm_sub_le _ _
    _ = ‖z⁻¹‖ * ‖f‖ + ‖z⁻¹‖ ^ 2 * ‖weightedAverage z⁻¹ f‖ := by
      rw [norm_smul, norm_smul, norm_neg, norm_pow]
    _ ≤ ‖z⁻¹‖ * ‖f‖ + ‖z⁻¹‖ ^ 2 * (‖f‖ / (1 - (z⁻¹).re)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left (weightedAverage_bound z⁻¹ ha f)
        (sq_nonneg _)) _
    _ = _ := by ring

lemma exteriorInverse_primitive (z : ℂ) (hz : z ≠ 0) (ha : (z⁻¹).re < 1)
    (f : Space) (x : I) :
    (∫ t in (0 : ℝ)..(x : ℝ), extension (exteriorInverse z ha f) t) =
      -z⁻¹ * (x : ℂ) * weightedAverage z⁻¹ f x := by
  let G : ℝ → ℂ := fun t => -z⁻¹ * ((t : ℂ) * extension (weightedAverage z⁻¹ f) t)
  have hG : Continuous G := continuous_const.mul
    (Complex.continuous_ofReal.mul (extension (weightedAverage z⁻¹ f)).continuous)
  have hder : ∀ t ∈ Ioo (0 : ℝ) (x : ℝ),
      HasDerivAt G (extension (exteriorInverse z ha f) t) t := by
    intro t ht
    have ht1 : t < 1 := lt_of_lt_of_le ht.2 x.property.2
    have hd := (weightedPrimitive_hasDerivAt z⁻¹ ha (inv_ne_zero hz) f t ⟨ht.1, ht1⟩).const_mul (-z⁻¹)
    convert hd using 1
    rw [exteriorInverse_extension z ha f t ⟨ht.1.le, ht1.le⟩]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le x.property.1
    hG.continuousOn hder
    ((extension (exteriorInverse z ha f)).continuous.intervalIntegrable 0 (x : ℝ))
  simpa only [G, extension_apply, Complex.ofReal_zero, mul_zero, zero_mul,
    sub_zero, mul_assoc] using hi

lemma exteriorInverse_right (z : ℂ) (hz : z ≠ 0) (ha : (z⁻¹).re < 1) (f : Space) :
    hardy (exteriorInverse z ha f) - z • exteriorInverse z ha f = f := by
  apply eq_of_eq_pos
  intro x hx
  change hardy (exteriorInverse z ha f) x - z * exteriorInverse z ha f x = f x
  rw [hardy_apply_pos _ x hx, exteriorInverse_primitive z hz ha f x,
    exteriorInverse_apply z ha f x]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp
  ring

lemma exterior_eigenfunction_eq_zero (z : ℂ) (hz : z ≠ 0) (ha : (z⁻¹).re < 1)
    (f : Space) (he : hardy f = z • f) : f = 0 := by
  by_contra hf
  rcases eigenfunction_inverse_re z hz f hf he with hpos | rfl
  · linarith
  · norm_num at ha

lemma exteriorInverse_left (z : ℂ) (hz : z ≠ 0) (ha : (z⁻¹).re < 1) (f : Space) :
    exteriorInverse z ha (hardy f - z • f) = f := by
  apply sub_eq_zero.mp
  apply exterior_eigenfunction_eq_zero z hz ha
  have h := exteriorInverse_right z hz ha (hardy f - z • f)
  rw [map_sub]
  rw [smul_sub]
  apply sub_eq_iff_eq_add.mp at h
  rw [h]
  abel

lemma exteriorInverse_zero (z : ℂ) (hz : z ≠ 0) (ha : (z⁻¹).re < 1) (f : Space) :
    exteriorInverse z ha f 0 = (1 - z)⁻¹ * f 0 := by
  have hz1 : z ≠ 1 := by rintro rfl; norm_num at ha
  have h1a : 1 - z⁻¹ ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  rw [exteriorInverse_apply, weightedAverage_zero z⁻¹ ha f]
  field_simp
  ring

/-- The source's full two-sided exterior resolvent, with its formula and bound. -/
theorem exterior_resolvent : Spec.ExteriorResolvent := by
  intro z hz ha
  refine ⟨exteriorInverse z ha, exteriorInverse_left z hz ha,
    exteriorInverse_right z hz ha, exteriorInverse_zero z hz ha, ?_, exteriorInverse_bound z ha⟩
  intro f x hx
  refine ⟨weighted_integral_intervalIntegrable z⁻¹ ha f x, ?_⟩
  rw [exteriorInverse_apply, weightedAverage_apply_pos z⁻¹ ha f x hx]
  ring

theorem spectrum_disk : Spec.SpectrumDisk :=
  spectrum_disk_of_exterior_resolvent exterior_resolvent

/-! The original real space and its intrinsic real spectral conclusions. -/

/-- The pointwise real-to-complex inclusion preserves the supremum norm. -/
def realInclusion : RealSpace →ₗᵢ[ℝ] Space where
  toFun f := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  map_add' f g := by ext x; simp
  map_smul' r f := by ext x; simp [Complex.real_smul]
  norm_map' f := by
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      change ‖(f x : ℂ)‖ ≤ ‖f‖
      simpa only [Complex.norm_real] using ContinuousMap.norm_coe_le_norm f x
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro x
      change ‖f x‖ ≤ ‖(⟨fun x => (f x : ℂ),
        Complex.continuous_ofReal.comp f.continuous⟩ : Space)‖
      simpa only [ContinuousMap.coe_mk, Complex.norm_real] using
        ContinuousMap.norm_coe_le_norm
          (⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ : Space) x

@[simp] lemma realInclusion_apply (f : RealSpace) (x : I) :
    realInclusion f x = (f x : ℂ) := rfl

/-- Pointwise real part, as a bounded real-linear map. -/
def realPart : Space →L[ℝ] RealSpace :=
  ({ toFun := fun f => ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
     map_add' := by intros; ext x; simp
     map_smul' := by intros; ext x; simp [Complex.real_smul] } :
    Space →ₗ[ℝ] RealSpace).mkContinuous 1 (by
      intro f
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      change ‖(f x).re‖ ≤ ‖f‖
      simpa only [Real.norm_eq_abs] using
        (Complex.abs_re_le_norm (f x)).trans (ContinuousMap.norm_coe_le_norm f x))

@[simp] lemma realPart_apply (f : Space) (x : I) : realPart f x = (f x).re := rfl

/-- Pointwise imaginary part, as a bounded real-linear map. -/
def imagPart : Space →L[ℝ] RealSpace :=
  ({ toFun := fun f => ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
     map_add' := by intros; ext x; simp
     map_smul' := by intros; ext x; simp [Complex.real_smul] } :
    Space →ₗ[ℝ] RealSpace).mkContinuous 1 (by
      intro f
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      change ‖(f x).im‖ ≤ ‖f‖
      simpa only [Real.norm_eq_abs] using
        (Complex.abs_im_le_norm (f x)).trans (ContinuousMap.norm_coe_le_norm f x))

@[simp] lemma imagPart_apply (f : Space) (x : I) : imagPart f x = (f x).im := rfl

/-- The actual real continuous-function space is a real form of the complex one. -/
def realForm : HardyAveragingRealBridge.RealForm RealSpace Space where
  inclusion := realInclusion
  re := realPart
  im := imagPart
  re_inclusion f := by ext x; simp
  im_inclusion f := by ext x; simp
  re_I_inclusion f := by ext x; simp [Complex.mul_re]
  im_I_inclusion f := by ext x; simp [Complex.mul_im]
  reconstruct f := by
    ext x
    simp only [ContinuousMap.add_apply, realInclusion_apply, realPart_apply,
      ContinuousMap.smul_apply, imagPart_apply, smul_eq_mul]
    simpa only [mul_comm Complex.I] using (Complex.re_add_im (f x)).symm


lemma real_closed_disk_iff (t : ℝ) :
    (‖(t : ℂ) - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ)) ↔ t ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : ‖(t : ℂ) - (1 / 2 : ℂ)‖ = |t - 1 / 2| := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hn, abs_le]
  constructor
  · rintro ⟨h₀, h₁⟩
    constructor <;> linarith
  · rintro ⟨h₀, h₁⟩
    constructor <;> linarith

lemma real_eigenvalue_disk_iff (t : ℝ) :
    (‖(t : ℂ) - (1 / 2 : ℂ)‖ < (1 / 2 : ℝ) ∨ (t : ℂ) = 1) ↔
      t ∈ Set.Ioc (0 : ℝ) 1 := by
  have hn : ‖(t : ℂ) - (1 / 2 : ℂ)‖ = |t - 1 / 2| := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hn, abs_lt]
  constructor
  · rintro (⟨h₀, h₁⟩ | h₁)
    · constructor <;> linarith
    · have ht : t = 1 := by exact_mod_cast h₁
      simp [ht]
  · rintro ⟨h₀, h₁⟩
    by_cases ht : t = 1
    · exact Or.inr (by simp [ht])
    · left
      have htlt : t < 1 := lt_of_le_of_ne h₁ ht
      constructor <;> linarith

lemma real_formula_unique {Q U : Spec.RealSpace →L[ℝ] Spec.RealSpace}
    (hQ : Spec.RealOperatorFormula Q) (hU : Spec.RealOperatorFormula U) : U = Q := by
  ext f x
  by_cases hx : (x : ℝ) = 0
  · have hx0 : x = 0 := Subtype.ext hx
    subst x
    exact (hU.1 f).trans (hQ.1 f).symm
  · have hpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx)
    exact (hU.2 f x hpos).trans (hQ.2 f x hpos).symm

/-- Averaging on the original real continuous-function space. -/
def realHardy : RealSpace →L[ℝ] RealSpace :=
  realPart.comp ((hardy.restrictScalars ℝ).comp realInclusion.toContinuousLinearMap)

lemma realHardy_apply (f : RealSpace) (x : I) :
    realHardy f x = ∫ r : I, f (r * x) := by
  change (hardy (realInclusion f) x).re = _
  rw [hardy_apply]
  simp only [realInclusion_apply, integral_complex_ofReal, Complex.ofReal_re]

lemma realHardy_intertwines (f : RealSpace) :
    hardy (realInclusion f) = realInclusion (realHardy f) := by
  ext x
  rw [hardy_apply, realInclusion_apply, realHardy_apply]
  simp only [realInclusion_apply, integral_complex_ofReal]

@[simp] lemma realHardy_zero (f : RealSpace) : realHardy f 0 = f 0 := by
  rw [realHardy_apply]
  simp

lemma realHardy_apply_interval (f : RealSpace) (x : I) :
    realHardy f x = ∫ r in (0 : ℝ)..1,
      ContinuousMap.IccExtendCM f (r * (x : ℝ)) := by
  rw [realHardy_apply]
  have heq : (fun r : I => f (r * x)) =
      (fun r : I => ContinuousMap.IccExtendCM f ((r : ℝ) * (x : ℝ))) := by
    funext r
    exact (ContinuousMap.IccExtendCM_of_mem (r * x).property).symm
  rw [heq]
  rw [integral_subtype measurableSet_Icc
    (fun r : ℝ => ContinuousMap.IccExtendCM f (r * (x : ℝ)))]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

lemma realHardy_formula : Spec.RealOperatorFormula realHardy := by
  refine ⟨realHardy_zero, ?_⟩
  intro f x hx
  rw [realHardy_apply_interval, intervalIntegral.integral_comp_mul_right _ hx.ne']
  simp [smul_eq_mul]

@[simp] lemma realHardy_const (c : ℝ) :
    realHardy (ContinuousMap.const I c) = ContinuousMap.const I c := by
  ext x
  rw [realHardy_apply]
  simp

lemma realHardy_norm : ‖realHardy‖ = 1 := by
  apply le_antisymm
  · exact (HardyAveragingRealBridge.norm_bounds realForm realHardy hardy
      realHardy_intertwines).1.trans (show ‖hardy‖ ≤ 1 from hardy_norm_le)
  · have h := realHardy.le_opNorm (ContinuousMap.const I (1 : ℝ))
    rw [realHardy_const] at h
    simpa using h

lemma realHardy_spectrum : spectrum ℝ realHardy = Icc (0 : ℝ) 1 := by
  rw [HardyAveragingRealBridge.spectrum_transport realForm realHardy hardy
    realHardy_intertwines]
  have hs : spectrum ℂ hardy = {z : ℂ | ‖z - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ)} := spectrum_disk
  rw [hs]
  ext t
  exact real_closed_disk_iff t

lemma realHardy_eigenvalues :
    {t : ℝ | ∃ f : RealSpace, f ≠ 0 ∧ realHardy f = t • f} = Ioc (0 : ℝ) 1 := by
  ext t
  change (∃ f : RealSpace, f ≠ 0 ∧ realHardy f = t • f) ↔ t ∈ Ioc (0 : ℝ) 1
  rw [HardyAveragingRealBridge.eigenvalue_transport realForm realHardy hardy
    realHardy_intertwines t]
  have he : (∃ f : Space, f ≠ 0 ∧ hardy f = (t : ℂ) • f) ↔
      ‖(t : ℂ) - (1 / 2 : ℂ)‖ < (1 / 2 : ℝ) ∨ (t : ℂ) = 1 :=
    Set.ext_iff.mp eigenvalue_disk (t : ℂ)
  exact he.trans (real_eigenvalue_disk_iff t)

lemma realHardy_injective : Function.Injective realHardy := by
  intro f g h
  apply realInclusion.injective
  apply no_zero_eigenvalue
  change hardy (realInclusion f) = hardy (realInclusion g)
  rw [realHardy_intertwines, realHardy_intertwines, h]

lemma realHardy_noncompact : ¬ IsCompactOperator realHardy := by
  intro hc
  exact noncompact ((HardyAveragingRealBridge.compact_transport realForm realHardy hardy
    realHardy_intertwines).mp hc)

theorem real_hardy_theorem : Spec.RealHardyTheorem := by
  refine ⟨realHardy, realHardy_formula, realHardy_norm, realHardy_spectrum,
    realHardy_eigenvalues, realHardy_injective, realHardy_noncompact, ?_⟩
  intro U hU
  exact real_formula_unique realHardy_formula hU

end ExpandedFA.PartV.HardyAveragingContinuous
