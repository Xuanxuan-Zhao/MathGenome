import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.GreenWeakInverse
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.GreenKernel
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.RegularProblem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace D13Unified.Ch10.GreenWeakInverse
open GreenKernel
open RegularProblem hiding Problem interval
open private cast_derivative cast_continuous from MathGenome.Internal.ODEDynamics.D13Unified.Ch10.GreenKernel

abbrev representative := Specs.D13Unified.Ch10.GreenWeakInverse.representativeValue
abbrev operator := Specs.D13Unified.Ch10.GreenWeakInverse.operatorValue
abbrev IsWeakDirichletSolution := Specs.D13Unified.Ch10.GreenWeakInverse.weakSolutionValue

/-- A weighted L² representative is integrable both for dx and for w dx. -/
theorem weighted_l1 : Specs.D13Unified.Ch10.GreenWeakInverse.WeightedL1 := by
  intro P f hf
  have := weightedMeasure_finite P
  have hi : Integrable f (weightedMeasure P) := hf.integrable (by norm_num)
  have hm : AEMeasurable (fun x => ENNReal.ofReal (P.w x)) (baseMeasure P) :=
    P.w_continuous.aemeasurable measurableSet_Icc |>.ennreal_ofReal
  have hw := (integrable_withDensity_iff_integrable_smul₀' hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
  have hF : Integrable (fun x => f x * (P.w x : ℂ)) (baseMeasure P) := by
    apply hw.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp [ENNReal.toReal_ofReal (P.w_positive x hx).le, mul_comm]
  refine ⟨?_, hF⟩
  have hc : ContinuousOn (fun x => ((P.w x : ℂ))⁻¹) (interval P) :=
    (Complex.continuous_ofReal.comp_continuousOn P.w_continuous).inv₀
      (fun x hx => Complex.ofReal_ne_zero.mpr (P.w_positive x hx).ne')
  have hh := IntegrableOn.mul_continuousOn hF hc isCompact_Icc
  apply hh.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  field_simp [Complex.ofReal_ne_zero.mpr (P.w_positive x hx).ne']

theorem kernel_integrable : Specs.D13Unified.Ch10.GreenWeakInverse.KernelIntegrable := by
  intro P c f hf x hx
  have hF := (weighted_l1 P f hf).2
  have hk : ContinuousOn (fun t => (kernel P c x t : ℂ)) (interval P) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((kernel_continuity P c).comp (continuousOn_const.prodMk continuousOn_id)
        (fun t ht => ⟨hx, ht⟩))
  have hh := IntegrableOn.continuousOn_mul hk hF isCompact_Icc
  have hI : IntegrableOn (fun t => (kernel P c x t : ℂ) * f t * (P.w t : ℂ))
      (interval P) := by simpa only [mul_assoc] using hh
  exact ⟨hI.mono_set Ioc_subset_Icc_self,
    by simp [Ioc_eq_empty (not_lt.mpr P.a_lt_b.le)]⟩

theorem representative_independent :
    Specs.D13Unified.Ch10.GreenWeakInverse.RepresentativeIndependent := by
  intro P c f g hf hg he
  have hae := (quotient_equality P f g hf hg).mp he
  funext x
  unfold applyKernel
  rw [intervalIntegral.integral_of_le P.a_lt_b.le,
    intervalIntegral.integral_of_le P.a_lt_b.le]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hae] with t ht
  exact congrArg (fun z : ℂ => (kernel P c x t : ℂ) * z * (P.w t : ℂ)) ht

/-- Absolute continuity of a complex Bochner primitive. Mathlib's scalar
primitive theorem is real-valued; the two real coordinate integrals supply
the finite-dimensional bridge used here. -/
lemma complex_primitive_ac {f : ℝ → ℂ} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, f t) a b := by
  have hr : IntervalIntegrable (fun t => (f t).re) volume a b :=
    ⟨Complex.reCLM.integrable_comp hf.1, Complex.reCLM.integrable_comp hf.2⟩
  have hi : IntervalIntegrable (fun t => (f t).im) volume a b :=
    ⟨Complex.imCLM.integrable_comp hf.1, Complex.imCLM.integrable_comp hf.2⟩
  have hR := Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
    (hr.absolutelyContinuousOnInterval_intervalIntegral hc)
  have hI := Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
    (hi.absolutelyContinuousOnInterval_intervalIntegral hc)
  apply (hR.add (hI.const_smul Complex.I)).congr
  intro x hx
  have hfx := hf.mono_set (uIcc_subset_uIcc hc hx)
  change ((∫ t in c..x, (f t).re : ℝ) : ℂ) +
    Complex.I * ((∫ t in c..x, (f t).im : ℝ) : ℂ) = _
  have hre : (∫ t in c..x, (f t).re) = (∫ t in c..x, f t).re :=
    Complex.reCLM.intervalIntegral_comp_comm hfx
  have him : (∫ t in c..x, (f t).im) = (∫ t in c..x, f t).im :=
    Complex.imCLM.intervalIntegral_comp_comm hfx
  rw [hre, him]
  simpa only [mul_comm] using Complex.re_add_im (∫ t in c..x, f t)

/-- An absolutely continuous function with a continuous AE derivative is C¹,
including the one-sided endpoint derivatives. No differentiability of an
arbitrary L² representative is used. -/
lemma regularity_of_ac_ae {y g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hy : AbsolutelyContinuousOnInterval y a b) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ᵐ x, x ∈ Icc a b → HasDerivAt y (g x) x) :
    ∀ x ∈ Icc a b, HasDerivWithinAt y (g x) (Icc a b) x := by
  let z : ℝ → ℂ := fun x => ∫ t in a..x, g t
  have hgi : IntervalIntegrable g volume a b :=
    (show ContinuousOn g (uIcc a b) from (uIcc_of_le hab).symm ▸ hg).intervalIntegrable
  have hz : AbsolutelyContinuousOnInterval z a b := complex_primitive_ac hgi left_mem_uIcc
  have he : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (y - z) 0 x := by
    filter_upwards [hd, hgi.ae_hasDerivAt_integral] with x hx hdx hxx
    have hxx' : x ∈ Icc a b := (uIcc_of_le hab) ▸ hxx
    simpa [z] using (hx hxx').sub (hdx hxx a left_mem_uIcc)
  obtain ⟨C, hC⟩ := (hy.sub hz).const_of_ae_hasDerivAt_zero he
  have heq : EqOn y (fun x => z x + C) (Icc a b) := by
    intro x hx
    have h := hC x ((uIcc_of_le hab).symm ▸ hx)
    change y x - z x = C at h
    exact sub_eq_iff_eq_add'.mp h
  intro x hx
  have hzder : HasDerivWithinAt z (g x) (Icc a b) x :=
    hasDerivWithinAt_integral_on_interval ordConnected_Icc hg (left_mem_Icc.mpr hab) hx
  exact (hzder.add_const C).congr_of_mem heq hx

lemma split_integral (P : Problem) (c : ℝ)
    (f : ℝ → ℂ) (hf : MemLp f 2 (weightedMeasure P)) (x : ℝ) (hx : x ∈ interval P) :
    applyKernel P c f x =
      ((rightMode P c x : ℂ) * (∫ t in P.a..x, (leftMode P c t : ℂ) * f t * (P.w t : ℂ)) +
       (leftMode P c x : ℂ) * (∫ t in x..P.b, (rightMode P c t : ℂ) * f t * (P.w t : ℂ))) /
        (denominator P c : ℂ) := by
  have hk := kernel_integrable P c f hf x hx
  have ha := hk.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc hx))
  have hb := hk.mono_set (uIcc_subset_uIcc_right (Icc_subset_uIcc hx))
  change (∫ t in P.a..P.b, (kernel P c x t : ℂ) * f t * (P.w t : ℂ)) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals ha hb]
  have hleft : (∫ t in P.a..x, (kernel P c x t : ℂ) * f t * (P.w t : ℂ)) =
      ((rightMode P c x : ℂ) / (denominator P c : ℂ)) *
        (∫ t in P.a..x, (leftMode P c t : ℂ) * f t * (P.w t : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    simp only [kernel, min_eq_right ht.2, max_eq_left ht.2,
      Complex.ofReal_div, Complex.ofReal_mul]
    ring
  have hright : (∫ t in x..P.b, (kernel P c x t : ℂ) * f t * (P.w t : ℂ)) =
      ((leftMode P c x : ℂ) / (denominator P c : ℂ)) *
        (∫ t in x..P.b, (rightMode P c t : ℂ) * f t * (P.w t : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.2] at ht
    simp only [kernel, min_eq_left ht.1, max_eq_right ht.1,
      Complex.ofReal_div, Complex.ofReal_mul]
    ring
  rw [hleft, hright]
  ring

/-- The endpoints are a null set; within derivatives become ambient
derivatives at almost every point of the closed interval. -/
lemma ae_interior (a b : ℝ) : ∀ᵐ x ∂volume, x ∈ Icc a b → x ∈ Ioo a b := by
  have ha : ∀ᵐ x ∂volume, x ≠ a := by simp [ae_iff]
  have hb : ∀ᵐ x ∂volume, x ≠ b := by simp [ae_iff]
  filter_upwards [ha, hb] with x hxa hxb hx
  exact ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩

/-- The full weak inverse, with actual continuous representatives. -/
theorem inverse_weak : Specs.D13Unified.Ch10.GreenWeakInverse.InverseWeak := by
  intro P c hc hQ f hf
  let U : ℝ → ℂ := fun x => (leftMode P c x : ℂ)
  let V : ℝ → ℂ := fun x => (rightMode P c x : ℂ)
  let UF : ℝ → ℂ := fun x => (leftFlux P c x : ℂ)
  let VF : ℝ → ℂ := fun x => (rightFlux P c x : ℂ)
  let pp : ℝ → ℂ := fun x => (P.p x : ℂ)
  let qq : ℝ → ℂ := fun x => (Q P c x : ℂ)
  let F : ℝ → ℂ := fun x => f x * (P.w x : ℂ)
  let d : ℂ := (denominator P c : ℂ)
  let A : ℝ → ℂ := fun x => ∫ t in P.a..x, U t * F t
  let B : ℝ → ℂ := fun x => ∫ t in x..P.b, V t * F t
  let Y : ℝ → ℂ := fun x => (V x * A x + U x * B x) / d
  let Z : ℝ → ℂ := fun x => (VF x * A x + UF x * B x) / d
  have ha : P.a ∈ interval P := left_mem_Icc.mpr P.a_lt_b.le
  have hb : P.b ∈ interval P := right_mem_Icc.mpr P.a_lt_b.le
  have ud := uniqueDiffOn_Icc P.a_lt_b
  have hpc : ContinuousOn pp (interval P) := cast_continuous P.p_regular.continuousOn
  have hqc : ContinuousOn qq (interval P) := cast_continuous (continuousOn_Q P c)
  have hUc : ContinuousOn U (interval P) := cast_continuous (left_mode_c1 P c).continuousOn
  have hVc : ContinuousOn V (interval P) := cast_continuous (right_mode_c1 P c).continuousOn
  have hUFc : ContinuousOn UF (interval P) := cast_continuous (left_flux_c1 P c).continuousOn
  have hVFc : ContinuousOn VF (interval P) := cast_continuous (right_flux_c1 P c).continuousOn
  have hp0 : ∀ x ∈ interval P, pp x ≠ 0 := fun x hx =>
    Complex.ofReal_ne_zero.mpr (P.p_positive x hx).ne'
  have hd0 : d ≠ 0 := Complex.ofReal_ne_zero.mpr (positive_modes P c hc hQ).2.2.1.ne'
  have hUd : ∀ x ∈ interval P, HasDerivWithinAt U (UF x / pp x) (interval P) x := by
    intro x hx
    convert! cast_derivative (𝕂 := ℂ) (left_mode_derivative P c x hx) using 1
    change (leftFlux P c x : ℂ) / (P.p x : ℂ) = ((leftFlux P c x / P.p x : ℝ) : ℂ)
    exact (Complex.ofReal_div _ _).symm
  have hVd : ∀ x ∈ interval P, HasDerivWithinAt V (VF x / pp x) (interval P) x := by
    intro x hx
    convert! cast_derivative (𝕂 := ℂ) (right_mode_derivative P c x hx) using 1
    change (rightFlux P c x : ℂ) / (P.p x : ℂ) = ((rightFlux P c x / P.p x : ℝ) : ℂ)
    exact (Complex.ofReal_div _ _).symm
  have hUFd : ∀ x ∈ interval P, HasDerivWithinAt UF (qq x * U x) (interval P) x := by
    intro x hx
    convert! cast_derivative (𝕂 := ℂ) (left_flux_derivative P c x hx) using 1
    change (Q P c x : ℂ) * (leftMode P c x : ℂ) = ((Q P c x * leftMode P c x : ℝ) : ℂ)
    exact (Complex.ofReal_mul _ _).symm
  have hVFd : ∀ x ∈ interval P, HasDerivWithinAt VF (qq x * V x) (interval P) x := by
    intro x hx
    convert! cast_derivative (𝕂 := ℂ) (right_flux_derivative P c x hx) using 1
    change (Q P c x : ℂ) * (rightMode P c x : ℂ) = ((Q P c x * rightMode P c x : ℝ) : ℂ)
    exact (Complex.ofReal_mul _ _).symm
  have hFI : Integrable F (baseMeasure P) := (weighted_l1 P f hf).2
  have hAI : IntervalIntegrable (fun t => U t * F t) volume P.a P.b := by
    have h := IntegrableOn.continuousOn_mul hUc hFI isCompact_Icc
    exact ⟨h.mono_set Ioc_subset_Icc_self, by simp [Ioc_eq_empty (not_lt.mpr P.a_lt_b.le)]⟩
  have hBI : IntervalIntegrable (fun t => V t * F t) volume P.a P.b := by
    have h := IntegrableOn.continuousOn_mul hVc hFI isCompact_Icc
    exact ⟨h.mono_set Ioc_subset_Icc_self, by simp [Ioc_eq_empty (not_lt.mpr P.a_lt_b.le)]⟩
  have hAac : AbsolutelyContinuousOnInterval A P.a P.b :=
    complex_primitive_ac hAI left_mem_uIcc
  have hBac : AbsolutelyContinuousOnInterval B P.a P.b := by
    apply (complex_primitive_ac hBI right_mem_uIcc).neg.congr
    intro x hx
    exact (intervalIntegral.integral_symm P.b x).symm
  have hAc : ContinuousOn A (interval P) := by
    exact hAac.continuousOn.mono (fun _ hx => Icc_subset_uIcc hx)
  have hBc : ContinuousOn B (interval P) := by
    exact hBac.continuousOn.mono (fun _ hx => Icc_subset_uIcc hx)
  have hYc : ContinuousOn Y (interval P) := ((hVc.mul hAc).add (hUc.mul hBc)).div_const d
  have hZc : ContinuousOn Z (interval P) := ((hVFc.mul hAc).add (hUFc.mul hBc)).div_const d
  have hUac : AbsolutelyContinuousOnInterval U P.a P.b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le P.a_lt_b.le]
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (left_mode_c1 P c)
  have hVac : AbsolutelyContinuousOnInterval V P.a P.b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le P.a_lt_b.le]
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (right_mode_c1 P c)
  have hUFac : AbsolutelyContinuousOnInterval UF P.a P.b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le P.a_lt_b.le]
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (left_flux_c1 P c)
  have hVFac : AbsolutelyContinuousOnInterval VF P.a P.b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le P.a_lt_b.le]
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (right_flux_c1 P c)
  have hYac : AbsolutelyContinuousOnInterval Y P.a P.b := by
    simpa only [Y, Z, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      ((hVac.smul hAac).add (hUac.smul hBac)).const_smul d⁻¹
  have hZac : AbsolutelyContinuousOnInterval Z P.a P.b := by
    simpa only [Y, Z, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      ((hVFac.smul hAac).add (hUFac.smul hBac)).const_smul d⁻¹
  have hW : ∀ x ∈ interval P, UF x * V x - U x * VF x = d := by
    intro x hx
    have hw := wronskian_constant P c x hx
    have hreal : leftFlux P c x * rightMode P c x - leftMode P c x * rightFlux P c x =
        denominator P c := by
      rw [← hw]
      dsimp [wronskian]
      rw [← left_flux_eq P c x hx, ← right_flux_eq P c x hx]
      ring
    dsimp [UF, V, U, VF, d]
    simpa only [Complex.ofReal_sub, Complex.ofReal_mul] using congrArg (fun z : ℝ => (z : ℂ)) hreal
  have hAE : ∀ᵐ x ∂volume, x ∈ interval P →
      HasDerivAt A (U x * F x) x ∧ HasDerivAt B (-V x * F x) x ∧
      HasDerivAt U (UF x / pp x) x ∧ HasDerivAt V (VF x / pp x) x ∧
      HasDerivAt UF (qq x * U x) x ∧ HasDerivAt VF (qq x * V x) x := by
    filter_upwards [hAI.ae_hasDerivAt_integral, hBI.ae_hasDerivAt_integral,
      ae_interior P.a P.b] with x hAx hBx hxx hx
    have hxu : x ∈ uIcc P.a P.b := Icc_subset_uIcc hx
    have hnh : interval P ∈ 𝓝 x :=
      Icc_mem_nhds (hxx hx).1 (hxx hx).2
    have hBd : HasDerivAt B (-V x * F x) x := by
      convert (hBx hxu P.b right_mem_uIcc).neg using 1
      · exact funext fun z => intervalIntegral.integral_symm P.b z
      · simp only [neg_mul]
    exact ⟨hAx hxu P.a left_mem_uIcc, hBd,
      (hUd x hx).hasDerivAt hnh, (hVd x hx).hasDerivAt hnh,
      (hUFd x hx).hasDerivAt hnh, (hVFd x hx).hasDerivAt hnh⟩
  have hYdae : ∀ᵐ x ∂volume, x ∈ interval P → HasDerivAt Y (Z x / pp x) x := by
    filter_upwards [hAE] with x hh hx
    rcases hh hx with ⟨hA, hB, hU, hV, hUF, hVF⟩
    convert (((hV.mul hA).add (hU.mul hB)).div_const d) using 1
    dsimp [Z]
    ring
  have hZdae : ∀ᵐ x ∂volume, x ∈ interval P → HasDerivAt Z (qq x * Y x - F x) x := by
    filter_upwards [hAE] with x hh hx
    rcases hh hx with ⟨hA, hB, hU, hV, hUF, hVF⟩
    convert (((hVF.mul hA).add (hUF.mul hB)).div_const d) using 1
    dsimp [Y]
    field_simp [hd0]
    linear_combination (F x) * hW x hx
  have hYd : ∀ x ∈ interval P, HasDerivWithinAt Y (Z x / pp x) (interval P) x :=
    regularity_of_ac_ae P.a_lt_b.le hYac
    (hZc.div hpc hp0) hYdae
  have hYreg : ContDiffOn ℝ 1 Y (interval P) :=
    Ch07.LinearSystemExistence.regularity (hZc.div hpc hp0) hYd
  have hflux : EqOn (fun x => pp x * derivWithin Y (interval P) x) Z (interval P) := by
    intro x hx
    change pp x * derivWithin Y (interval P) x = Z x
    rw [(hYd x hx).derivWithin (ud x hx)]
    field_simp [hp0 x hx]
  have hYa : Y P.a = 0 := by simp [Y, A, U, (left_initial P c).1]
  have hYb : Y P.b = 0 := by simp [Y, B, V, (right_initial P c).1]
  have hYsol : IsWeakDirichletSolution P c f Y := by
    refine ⟨hYreg, ?_, hYa, hYb, ?_⟩
    · apply hZac.congr
      intro x hx
      have hxI : x ∈ interval P := by
        rw [uIcc_of_le P.a_lt_b.le] at hx
        exact hx
      exact (hflux hxI).symm
    · apply (ae_restrict_iff' measurableSet_Icc).mpr
      filter_upwards [hZdae, ae_interior P.a P.b] with x hd hxx hx
      have hn : interval P ∈ 𝓝 x := Icc_mem_nhds (hxx hx).1 (hxx hx).2
      have he : (fun t => pp t * derivWithin Y (interval P) t) =ᶠ[𝓝 x] Z :=
        mem_of_superset hn hflux
      convert (hd hx).congr_of_eventuallyEq he using 1
      · rfl
      · dsimp only [qq, F]
        ring
  have hsplit : EqOn (applyKernel P c f) Y (interval P) := by
    intro x hx
    convert split_integral P c f hf x hx using 1
    simp only [Y, A, B, U, V, F, d, mul_assoc]
  have hKsol : IsWeakDirichletSolution P c f (applyKernel P c f) := by
    refine ⟨hYreg.congr hsplit, ?_, ?_, ?_, ?_⟩
    · apply hYsol.2.1.congr
      intro x hx
      have hxI : x ∈ interval P := by
        rw [uIcc_of_le P.a_lt_b.le] at hx
        exact hx
      exact congrArg (fun z => (P.p x : ℂ) * z)
        (derivWithin_congr hsplit (hsplit hxI)).symm
    · rw [hsplit ha]; exact hYa
    · rw [hsplit hb]; exact hYb
    · apply (ae_restrict_iff' measurableSet_Icc).mpr
      have hyAE := (ae_restrict_iff' measurableSet_Icc).mp hYsol.2.2.2.2
      filter_upwards [hyAE, ae_interior P.a P.b] with x hyx hxx hx
      have hn : interval P ∈ 𝓝 x := Icc_mem_nhds (hxx hx).1 (hxx hx).2
      have he : (fun t => (P.p t : ℂ) * derivWithin (applyKernel P c f) (interval P) t)
          =ᶠ[𝓝 x] (fun t => (P.p t : ℂ) * derivWithin Y (interval P) t) := by
        apply mem_of_superset hn
        intro t ht
        exact congrArg (fun z => (P.p t : ℂ) * z) (derivWithin_congr hsplit (hsplit ht))
      rw [hsplit hx]
      exact (hyx hx).congr_of_eventuallyEq he
  refine ⟨hKsol, ?_⟩
  intro y hy
  let z : ℝ → ℂ := fun t => pp t * derivWithin y (interval P) t
  let LA : ℝ → ℂ := fun t => UF t * y t - U t * z t
  let LB : ℝ → ℂ := fun t => V t * z t - VF t * y t
  have hyac : AbsolutelyContinuousOnInterval y P.a P.b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le P.a_lt_b.le]
    exact hy.1
  have hzac : AbsolutelyContinuousOnInterval z P.a P.b := hy.2.1
  have hLAac : AbsolutelyContinuousOnInterval LA P.a P.b :=
    (hUFac.smul hyac).sub (hUac.smul hzac)
  have hLBac : AbsolutelyContinuousOnInterval LB P.a P.b :=
    (hVac.smul hzac).sub (hVFac.smul hyac)
  have hyd : ∀ t ∈ interval P, HasDerivWithinAt y (z t / pp t) (interval P) t := by
    intro t ht
    have hd := (hy.1.differentiableOn (by norm_num) t ht).hasDerivWithinAt
    convert hd using 1
    dsimp [z]
    field_simp [hp0 t ht]
  have hzd : ∀ᵐ t ∂volume, t ∈ interval P → HasDerivAt z (qq t * y t - F t) t := by
    have h := (ae_restrict_iff' measurableSet_Icc).mp hy.2.2.2.2
    filter_upwards [h] with t hh ht
    convert hh ht using 1
    · rfl
    · dsimp only [qq, F]
      ring
  have hLAd : ∀ᵐ t ∂volume, t ∈ interval P → HasDerivAt LA (U t * F t) t := by
    filter_upwards [hAE, hzd, ae_interior P.a P.b] with t he hz hi ht
    rcases he ht with ⟨hA, hB, hU, hV, hUF, hVF⟩
    have hy' := (hyd t ht).hasDerivAt (Icc_mem_nhds (hi ht).1 (hi ht).2)
    convert ((hUF.mul hy').sub (hU.mul (hz ht))) using 1
    ring
  have hLBd : ∀ᵐ t ∂volume, t ∈ interval P → HasDerivAt LB (-V t * F t) t := by
    filter_upwards [hAE, hzd, ae_interior P.a P.b] with t he hz hi ht
    rcases he ht with ⟨hA, hB, hU, hV, hUF, hVF⟩
    have hy' := (hyd t ht).hasDerivAt (Icc_mem_nhds (hi ht).1 (hi ht).2)
    convert ((hV.mul (hz ht)).sub (hVF.mul hy')) using 1
    ring
  have hLAa : LA P.a = 0 := by simp [LA, hy.2.2.1, U, (left_initial P c).1]
  have hLBb : LB P.b = 0 := by simp [LB, hy.2.2.2.1, V, (right_initial P c).1]
  have heA : EqOn LA A (interval P) := by
    have he : ∀ᵐ t ∂volume, t ∈ uIcc P.a P.b → HasDerivAt (LA - A) 0 t := by
      filter_upwards [hLAd, hAE] with t hh he ht
      have htI : t ∈ interval P := by
        rw [uIcc_of_le P.a_lt_b.le] at ht
        exact ht
      simpa using (hh htI).sub (he htI).1
    obtain ⟨C, hC⟩ := (hLAac.sub hAac).const_of_ae_hasDerivAt_zero he
    have hCa := hC P.a left_mem_uIcc
    have hC0 : C = 0 := by simpa [hLAa, A] using hCa.symm
    intro x hx
    have hh := hC x (Icc_subset_uIcc hx)
    simpa only [Pi.sub_apply, hC0, sub_eq_zero] using hh
  have heB : EqOn LB B (interval P) := by
    have he : ∀ᵐ t ∂volume, t ∈ uIcc P.a P.b → HasDerivAt (LB - B) 0 t := by
      filter_upwards [hLBd, hAE] with t hh he ht
      have htI : t ∈ interval P := by
        rw [uIcc_of_le P.a_lt_b.le] at ht
        exact ht
      simpa using (hh htI).sub (he htI).2.1
    obtain ⟨C, hC⟩ := (hLBac.sub hBac).const_of_ae_hasDerivAt_zero he
    have hCb := hC P.b right_mem_uIcc
    have hC0 : C = 0 := by simpa [hLBb, B] using hCb.symm
    intro x hx
    have hh := hC x (Icc_subset_uIcc hx)
    simpa only [Pi.sub_apply, hC0, sub_eq_zero] using hh
  intro x hx
  rw [hsplit hx]
  change y x = (V x * A x + U x * B x) / d
  apply (eq_div_iff hd0).mpr
  rw [← heA hx, ← heB hx, ← hW x hx]
  dsimp [LA, LB]
  ring

/-- The AE equation for the original differential expression. -/
theorem weak_equation : Specs.D13Unified.Ch10.GreenWeakInverse.WeakEquation := by
  intro P c f y hy
  filter_upwards [hy.2.2.2.2, ae_restrict_mem measurableSet_Icc] with x hd hx
  have he := hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc P.a_lt_b x hx)
  change -derivWithin (fun t => (P.p t : ℂ) * derivative P y t) (interval P) x +
    (Q P c x : ℂ) * y x = (P.w x : ℂ) * f x
  change derivWithin (fun t => (P.p t : ℂ) * derivative P y t) (interval P) x =
    (Q P c x : ℂ) * y x - (P.w x : ℂ) * f x at he
  rw [he]
  ring

/-- The actual Green representative lies in L² and represents the class Kf. -/
theorem class_representative : Specs.D13Unified.Ch10.GreenWeakInverse.ClassRepresentative := by
  intro P c hc hQ f
  have hs := (inverse_weak P c hc hQ (f : ℝ → ℂ) (Lp.memLp f)).1
  have hm : MemLp (representative P c f) 2 (weightedMeasure P) :=
    continuous_memLp P _ hs.1.continuousOn
  refine ⟨hm, ?_⟩
  have he : operator P c f = toHilbert P (representative P c f) hm := by
    unfold operator Specs.D13Unified.Ch10.GreenWeakInverse.operatorValue
    rw [dite_eq_left hm]
  change (operator P c f : ℝ → ℂ) =ᵐ[baseMeasure P] representative P c f
  rw [he]
  exact (weighted_ae P _).mp (representative_ae P _ hm)

/-- Every weak regular Dirichlet solution equals the canonical integral on
[a,b], including the endpoints, and determines exactly its Hilbert class. -/
theorem converse : Specs.D13Unified.Ch10.GreenWeakInverse.Converse := by
  intro P c hc hQ f y hy
  have he := (inverse_weak P c hc hQ (f : ℝ → ℂ) (Lp.memLp f)).2 y hy
  have hm : MemLp (representative P c f) 2 (weightedMeasure P) :=
    (class_representative P c hc hQ f).1
  have hym : MemLp y 2 (weightedMeasure P) := continuous_memLp P y hy.1.continuousOn
  refine ⟨he, hym, ?_⟩
  have hop : operator P c f = toHilbert P (representative P c f) hm := by
    unfold operator Specs.D13Unified.Ch10.GreenWeakInverse.operatorValue
    rw [dite_eq_left hm]
  change toHilbert P y hym = operator P c f
  rw [hop]
  apply (quotient_equality P y (representative P c f) hym hm).mpr
  exact he.aeEq_restrict measurableSet_Icc

end D13Unified.Ch10.GreenWeakInverse
