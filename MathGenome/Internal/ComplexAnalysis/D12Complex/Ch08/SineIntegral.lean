import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.SineIntegral
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.PrincipalValues
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace D12Complex.SineIntegral

abbrev sineKernel := Definitions.sineKernel

theorem sineKernel_removable :
    Specs.D12Complex.Ch08.SineIntegral.sineKernel_removable_type := by
  intro c
  have hcont : Continuous (sineKernel c) :=
    continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))
  have hzero : sineKernel c 0 = c := by simp [sineKernel, Definitions.sineKernel]
  have heq (x : ℝ) (hx : x ≠ 0) : sineKernel c x = Real.sin (c*x) / x := by
    by_cases hc : c = 0
    · simp [hc, sineKernel, Definitions.sineKernel]
    · rw [sineKernel, Definitions.sineKernel, Real.sinc_of_ne_zero (mul_ne_zero hc hx)]
      field_simp
  refine ⟨hcont, hzero, heq, ?_⟩
  have ht : Tendsto (sineKernel c) (𝓝[≠] 0) (𝓝 (sineKernel c 0)) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [hzero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact heq x hx

theorem principal_value_exp_div :
    Specs.D12Complex.Ch08.SineIntegral.principal_value_exp_div_type := by
  classical
  intro c hc
  have hres : Residue.residue
      (fun z : ℂ => Complex.exp (Complex.I * (c : ℂ) * z) *
        ((1 : Polynomial ℂ).eval z / Polynomial.X.eval z)) 0 = 1 := by
    have hp : HolomorphicOn univ (fun z : ℂ => Complex.exp (Complex.I * (c : ℂ) * z)) :=
      ⟨isOpen_univ, by intro z _; fun_prop⟩
    have hq : HolomorphicOn univ (fun z : ℂ => z) :=
      ⟨isOpen_univ, by intro z _; fun_prop⟩
    simpa using ResidueComputation.residue_simple_quotient _ _ _ 0 univ
      (mem_univ _) hp hq rfl (by simp) (Eventually.of_forall (fun z => by simp [div_eq_mul_inv]))
  have h := PrincipalValues.principal_value_residues (1 : Polynomial ℂ) Polynomial.X
    isCoprime_one_left (by simp) (by intro a _; simp) c hc
  simp only [Polynomial.eval_one, Polynomial.eval_X, one_div] at hres
  simpa [PrincipalValues.HasPrincipalValue, PrincipalValues.Definitions.realPoles,
    Polynomial.roots_X, Finset.filter_singleton, hres, div_eq_mul_inv] using h

lemma im_exp_div (c x : ℝ) :
    (Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)).im =
      Real.sin (c*x) / x := by
  simp [Complex.div_ofReal_im, Complex.exp_im, Complex.mul_re, Complex.mul_im]

lemma sineKernel_even (c x : ℝ) : sineKernel c (-x) = sineKernel c x := by
  simp [sineKernel, Definitions.sineKernel, Real.sinc_neg]

lemma im_integral_exp_div (c a b : ℝ)
    (hi : IntervalIntegrable (fun x : ℝ =>
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)) volume a b) :
    (∫ x in a..b, Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)).im =
      ∫ x in a..b, sineKernel c x := by
  change Complex.imCLM (∫ x in a..b, Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)) = _
  rw [← Complex.imCLM.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx _
  change (Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)).im = sineKernel c x
  rw [im_exp_div]
  exact ((sineKernel_removable c).2.2.1 x hx).symm

lemma deletedSet_singleton (ε : ℝ) :
    PrincipalValues.deletedSet {0} (-1) 1 (fun _ => ε) =
      Icc (-1 : ℝ) 1 \ Ioo (-ε) ε := by
  ext x
  simp [PrincipalValues.deletedSet, PrincipalValues.Definitions.deletedSet, Finset.mem_singleton]

/-- Taking the imaginary part of the local deletion limit is an ordinary
integral, since the imaginary singularity has a continuous extension. -/
lemma im_middle_limit (c : ℝ) (M : ℂ)
    (hi : ∀ ε : ({0} : Finset ℝ) → ℝ, (∀ a, 0 < ε a) →
      IntegrableOn (fun x : ℝ => Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ))
        (PrincipalValues.deletedSet {0} (-1) 1 ε))
    (hm : Tendsto (PrincipalValues.deletedIntegral
      (fun x : ℝ => Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)) {0} (-1) 1)
      (PrincipalValues.deletionFilter {0}) (𝓝 M)) :
    M.im = ∫ x in (-1 : ℝ)..1, sineKernel c x := by
  have hcont := (sineKernel_removable c).1
  have hconst : Tendsto (fun ε : ℝ => fun _ : ({0} : Finset ℝ) => ε)
      (𝓝[>] (0 : ℝ)) (PrincipalValues.deletionFilter {0}) :=
    tendsto_pi.mpr (fun _ => tendsto_id)
  have him := (Complex.continuous_im.tendsto M).comp (hm.comp hconst)
  have hF := intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => hcont.intervalIntegrable a b) (0 : ℝ)
  have hsmall : Tendsto (fun ε : ℝ => ∫ x in (-ε)..ε, sineKernel c x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hz : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝 0) := by simpa using hz.neg
    have hp := ((hF.tendsto 0).comp hz).sub ((hF.tendsto 0).comp hneg)
    simpa only [Function.comp_apply, sub_self,
      intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable 0 _)
        (hcont.intervalIntegrable 0 _)] using hp
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (PrincipalValues.deletedIntegral
        (fun x : ℝ => Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ))
        {0} (-1) 1 (fun _ => ε)).im =
      (∫ x in (-1 : ℝ)..1, sineKernel c x) - ∫ x in (-ε)..ε, sineKernel c x := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with ε hε hε1
    change 0 < ε at hε
    change ε < 1 at hε1
    change (∫ x in PrincipalValues.deletedSet {0} (-1) 1 (fun _ => ε),
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)).im = _
    change Complex.imCLM (∫ x in PrincipalValues.deletedSet {0} (-1) 1 (fun _ => ε),
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)) = _
    rw [← Complex.imCLM.integral_comp_comm (hi (fun _ => ε) (fun _ => hε))]
    have hs : MeasurableSet (PrincipalValues.deletedSet {0} (-1) 1 (fun _ => ε)) := by
      rw [deletedSet_singleton]; exact measurableSet_Icc.diff measurableSet_Ioo
    have heq : (∫ x in PrincipalValues.deletedSet {0} (-1) 1 (fun _ => ε),
        Complex.imCLM (Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ))) =
        ∫ x in PrincipalValues.deletedSet {0} (-1) 1 (fun _ => ε), sineKernel c x := by
      apply setIntegral_congr_fun hs
      intro x hx
      rw [deletedSet_singleton] at hx
      have hx0 : x ≠ 0 := by intro hx0; apply hx.2; subst x; constructor <;> linarith
      change (Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)).im = sineKernel c x
      rw [im_exp_div]
      exact ((sineKernel_removable c).2.2.1 x hx0).symm
    rw [heq, deletedSet_singleton,
      setIntegral_sdiff measurableSet_Ioo hcont.integrableOn_Icc
        (show Ioo (-ε) ε ⊆ Icc (-1 : ℝ) 1 from fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩),
      integral_Icc_eq_integral_Ioc, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← intervalIntegral.integral_of_le (by linarith : -ε ≤ ε)]
  have ht := (tendsto_const_nhds (x := ∫ x in (-1 : ℝ)..1, sineKernel c x)).sub hsmall
  simp only [sub_zero] at ht
  exact tendsto_nhds_unique him (ht.congr' (EventuallyEq.symm hevent))

theorem sine_integral : Specs.D12Complex.Ch08.SineIntegral.sine_integral_type := by
  intro c hc
  have hcont := (sineKernel_removable c).1
  have hlimit : Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, sineKernel c x)
      atTop (𝓝 (Real.pi / 2)) := by
    obtain ⟨hleft, hright, hdeleted, Lminus, M, Lplus, hm, hmid, hp, hsum⟩ :=
      principal_value_exp_div c hc (-1) 1 (by norm_num)
        (by intro a ha; have ha0 : a = 0 := Finset.mem_singleton.mp ha; subst a; norm_num)
    have hM := im_middle_limit c M hdeleted hmid
    have hplus : Tendsto (fun b : ℝ => ∫ x in (1 : ℝ)..b, sineKernel c x) atTop (𝓝 Lplus.im) := by
      apply ((Complex.continuous_im.tendsto Lplus).comp hp).congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
      exact im_integral_exp_div c 1 b (hright b hb)
    have hminus : Tendsto (fun b : ℝ => ∫ x in (1 : ℝ)..b, sineKernel c x) atTop (𝓝 Lminus.im) := by
      apply (((Complex.continuous_im.tendsto Lminus).comp hm).comp tendsto_neg_atTop_atBot).congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
      change (∫ x in (-b)..(-1 : ℝ), Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)).im = _
      rw [im_integral_exp_div c (-b) (-1) (hleft (-b) (by linarith))]
      simpa only [neg_neg, sineKernel_even] using
        (intervalIntegral.integral_comp_neg (a := (1 : ℝ)) (b := b) (sineKernel c)).symm
    have heqtail : Lminus.im = Lplus.im := tendsto_nhds_unique hminus hplus
    have heven0 : (∫ x in (-1 : ℝ)..0, sineKernel c x) = ∫ x in (0 : ℝ)..1, sineKernel c x := by
      simpa only [neg_zero, sineKernel_even] using
        (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (sineKernel c)).symm
    have hdouble : (∫ x in (-1 : ℝ)..1, sineKernel c x) =
        2 * ∫ x in (0 : ℝ)..1, sineKernel c x := by
      have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1)
      change (∫ x in (-1 : ℝ)..0, sineKernel c x) + (∫ x in (0 : ℝ)..1, sineKernel c x) = _ at h
      rw [heven0] at h
      linarith
    have hsumIm : Lminus.im + M.im + Lplus.im = Real.pi := by
      simpa using congrArg Complex.im hsum
    have hvalue : (∫ x in (0 : ℝ)..1, sineKernel c x) + Lplus.im = Real.pi/2 := by
      rw [heqtail, hM, hdouble] at hsumIm
      linarith
    rw [← hvalue]
    apply ((tendsto_const_nhds (x := ∫ x in (0 : ℝ)..1, sineKernel c x)).add hplus).congr'
    exact Eventually.of_forall (fun b => intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 1) (hcont.intervalIntegrable 1 b))
  refine ⟨fun b => hcont.intervalIntegrable 0 b, hlimit, ?_⟩
  apply hlimit.congr'
  apply Eventually.of_forall
  intro b
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx _
  exact (sineKernel_removable c).2.2.1 x hx

lemma norm_exp_div (c x : ℝ) :
    ‖Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)‖ = |x|⁻¹ := by
  rw [norm_div, OscillatoryIntegrals.norm_exp_real_frequency, Complex.norm_real,
    Real.norm_eq_abs, one_div]

theorem exp_div_not_integrable_near_zero :
    Specs.D12Complex.Ch08.SineIntegral.exp_div_not_integrable_near_zero_type := by
  intro c _ ε hε hi
  have hj : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 (ε/2) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ ε/2)).mpr
    apply IntegrableOn.congr_fun ((hi.mono_set (show Ioc 0 (ε/2) ⊆ Ioo (-ε) ε from ?_)).norm) ?_ measurableSet_Ioc
    · intro x hx
      constructor <;> linarith [hx.1, hx.2]
    · intro x hx
      change ‖Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / (x : ℂ)‖ = x⁻¹
      rw [norm_exp_div, abs_of_pos hx.1]
  have hn := intervalIntegrable_inv_iff.mp hj
  rcases hn with hn | hn
  · linarith
  · exact hn (by rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ ε/2)]; exact ⟨le_rfl, by positivity⟩)

/-- A quarter-period shift transfers a hypothetical absolute sine tail to
an absolute cosine tail. Together they would dominate the harmonic kernel. -/
lemma not_integrable_abs_sine (c : ℝ) (hc : 0 < c) :
    ¬ IntegrableOn (fun x : ℝ => |Real.sin (c*x)| / x) (Ioi (0 : ℝ)) := by
  intro hi
  let t : ℝ := Real.pi / (2*c)
  have ht : 0 < t := by dsimp [t]; positivity
  have hs : IntegrableOn (fun x : ℝ => |Real.sin (c*(x+t))| / (x+t)) (Ioi t) := by
    have h := ((measurePreserving_add_right volume t).integrableOn_comp_preimage
      (Homeomorph.addRight t).measurableEmbedding).mpr hi
    exact h.mono_set (fun x hx => by change t < x at hx; change 0 < x+t; linarith)
  have hshift (x : ℝ) : Real.sin (c*(x+t)) = Real.cos (c*x) := by
    have he : c*(x+t) = c*x + Real.pi/2 := by dsimp [t]; field_simp
    rw [he, Real.sin_add_pi_div_two]
  have hcos : IntegrableOn (fun x : ℝ => |Real.cos (c*x)| / x) (Ioi t) := by
    apply (hs.const_mul 2).mono' (Measurable.aestronglyMeasurable (by fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := ht.trans hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) hx0.le), hshift]
    have hp : 0 < x+t := by linarith
    have hn := abs_nonneg (Real.cos (c*x))
    change |Real.cos (c*x)| / x ≤ 2 * (|Real.cos (c*x)| / (x+t))
    rw [← mul_div_assoc, div_le_div_iff₀ hx0 hp]
    change t < x at hx
    nlinarith
  have hsum := (hi.mono_set (fun x hx => ht.le.trans_lt hx)).add hcos
  apply (not_integrableOn_Ioi_inv (a := t))
  apply hsum.mono' (Measurable.aestronglyMeasurable (by fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := ht.trans hx
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
  change x⁻¹ ≤ |Real.sin (c*x)| / x + |Real.cos (c*x)| / x
  rw [← add_div, inv_eq_one_div]
  apply (div_le_div_iff_of_pos_right hx0).mpr
  have hsid := Real.sin_sq_add_cos_sq (c*x)
  have hs0 := abs_nonneg (Real.sin (c*x))
  have hc0 := abs_nonneg (Real.cos (c*x))
  have hs1 := Real.abs_sin_le_one (c*x)
  have hc1 := Real.abs_cos_le_one (c*x)
  nlinarith [sq_abs (Real.sin (c*x)), sq_abs (Real.cos (c*x))]

theorem absolute_sine_integral_diverges :
    Specs.D12Complex.Ch08.SineIntegral.absolute_sine_integral_diverges_type := by
  intro c hc
  have hcont := (sineKernel_removable c).1.abs
  have hn := not_integrable_abs_sine c hc
  refine ⟨?_, hn⟩
  have hmono : Monotone (fun b : ℝ => ∫ x in (0 : ℝ)..b, |sineKernel c x|) := by
    intro a b hab
    change (∫ x in (0 : ℝ)..a, |sineKernel c x|) ≤ ∫ x in (0 : ℝ)..b, |sineKernel c x|
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 a) (hcont.intervalIntegrable a b)]
    have hp := intervalIntegral.integral_nonneg (μ := volume) hab (fun x _ => abs_nonneg (sineKernel c x))
    linarith
  apply hmono.tendsto_atTop_atTop
  intro K
  by_contra! hbound
  have hint : IntegrableOn (fun x : ℝ => |sineKernel c x|) (Ioi (0 : ℝ)) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded K 0
      (fun b : ℝ => (hcont.intervalIntegrable 0 b).1) tendsto_id
    exact Eventually.of_forall (fun b => by simpa only [Real.norm_eq_abs, abs_abs] using (hbound b).le)
  apply hn
  apply hint.congr_fun ?_ measurableSet_Ioi
  intro x hx
  change |Definitions.sineKernel c x| = |Real.sin (c*x)| / x
  rw [(sineKernel_removable c).2.2.1 x hx.ne', abs_div, abs_of_pos (show 0 < x from hx)]

end D12Complex.SineIntegral
