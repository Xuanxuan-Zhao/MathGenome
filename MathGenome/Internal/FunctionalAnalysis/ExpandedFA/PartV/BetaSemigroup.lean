import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.BetaSemigroup
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.FractionalIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The semigroup clause of `fa2:p5:weak-volterra` (paper.tex:21995–22023).
The canonical objects are the upstream `fractionalValue` and its bounded
realizations. Absolute Fubini is proved from the nonnegative kernel convolution
and Young's bound before convolution associativity is applied.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ExpandedFA.PartV.BetaSemigroup
open ExpandedFA.PartV.FractionalIntegrals
open ExpandedFA.PartV.FractionalIntegrals.Spec

lemma complex_power {x a : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) ^ ((a : ℂ) - 1) = (x ^ (a-1) : ℝ) := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hx]

lemma beta_left_integrable {α β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    IntervalIntegrable (fun s : ℝ => s ^ (β-1) * (d-s) ^ (α-1)) volume 0 (d/2) := by
  apply IntervalIntegrable.mul_continuousOn
  · exact intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < β-1)
  · apply ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
    intro s hs
    rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ d/2)] at hs
    left
    change d-s ≠ 0
    linarith [hs.2]

lemma beta_scaled_integrable {α β d : ℝ} (hα : 0 < α) (hβ : 0 < β) (hd : 0 < d) :
    IntervalIntegrable (fun s : ℝ => s ^ (β-1) * (d-s) ^ (α-1)) volume 0 d := by
  refine (beta_left_integrable hβ hd).trans ?_
  have h := (beta_left_integrable (α := β) hα hd).comp_sub_left d
  convert h.symm using 1
  · ext s
    simp only [sub_sub_cancel]
    ring
  · ring
  · ring

lemma beta_scaled {α β d : ℝ} (hα : 0 < α) (hβ : 0 < β) (hd : 0 < d) :
    (∫ s in Ioc 0 d, s ^ (β-1) * (d-s) ^ (α-1)) =
      (Real.Gamma α * Real.Gamma β / Real.Gamma (α+β)) * d ^ (α+β-1) := by
  have he : (fun s : ℝ => (s : ℂ) ^ ((β : ℂ)-1) * ((d : ℂ)-(s : ℂ)) ^ ((α : ℂ)-1))
      =ᵐ[volume.restrict (Ioc 0 d)]
        (fun s : ℝ => ((s ^ (β-1) * (d-s) ^ (α-1) : ℝ) : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [complex_power hs.1.le, ← Complex.ofReal_sub,
      complex_power (sub_nonneg.mpr hs.2), Complex.ofReal_mul]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_congr_ae he,
    ← intervalIntegral.integral_of_le hd.le,
    Complex.betaIntegral_scaled _ _ hd,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ hβ hα]
  have hp : (d : ℂ) ^ ((β : ℂ)+(α : ℂ)-1) = (d ^ (α+β-1) : ℝ) := by
    rw [add_comm (β : ℂ), ← Complex.ofReal_add, complex_power hd.le]
  rw [hp]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
    ← Complex.Gamma_ofReal]
  rw [add_comm (β : ℂ) (α : ℂ)]
  ring

/-- Beta rescaling with the exact Gamma coefficient. -/
theorem beta_convolution : Spec.BetaConvolution := by
  intro α β v t hα hβ hvt
  have hd : 0 < t-v := sub_pos.mpr hvt
  have hi := (beta_scaled_integrable hα hβ hd).comp_sub_right v
  have hi' : IntervalIntegrable
      (fun s : ℝ => (t-s) ^ (α-1) * (s-v) ^ (β-1)) volume v t := by
    convert hi using 1
    · ext s
      rw [show t-v-(s-v) = t-s by ring, mul_comm]
    · ring
    · ring
  refine ⟨hi'.1, ?_⟩
  rw [← intervalIntegral.integral_of_le hvt.le]
  have he := intervalIntegral.integral_comp_sub_right
    (fun s : ℝ => s ^ (β-1) * ((t-v)-s) ^ (α-1)) (a := v) (b := t) v
  rw [sub_self, intervalIntegral.integral_of_le hd.le, beta_scaled hα hβ hd] at he
  convert he using 1
  congr 1
  ext s
  rw [show t-v-(s-v) = t-s by ring, mul_comm]

lemma powerKernel_nonneg (α T r : ℝ) : 0 ≤ powerKernel α T r := by
  by_cases hr : r ∈ Ioc (0 : ℝ) T
  · simpa [powerKernel, hr] using Real.rpow_nonneg hr.1.le (α-1)
  · simp [powerKernel, hr]

lemma convolution_zero_nonpos {𝕜 : Type} [RCLike 𝕜] (α T : ℝ) (f : ℝ → 𝕜)
    {t : ℝ} (ht : t ≤ 0) :
    realConvolution (powerKernel α T) ((Ioc 0 T).indicator f) t = 0 := by
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro r
  by_cases hr : r ∈ Ioc (0 : ℝ) T
  · have htr : t-r ∉ Ioc (0 : ℝ) T := by intro h; linarith [hr.1, h.1]
    simp [htr]
  · simp [powerKernel, hr]

lemma power_convolution_below {𝕜 : Type} [RCLike 𝕜] (α T : ℝ) (f : ℝ → 𝕜)
    {t : ℝ} (ht : t ≤ T) :
    realConvolution (powerKernel α T) ((Ioc 0 T).indicator f) t =
      (Ioc 0 T).indicator (powerValue α f) t := by
  by_cases hp : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) T from ⟨hp, ht⟩)]
    exact (power_convolution_bridge α T f ⟨hp.le, ht⟩).2
  · rw [convolution_zero_nonpos α T f (not_lt.mp hp)]
    simp [indicator_of_notMem, show t ∉ Ioc (0 : ℝ) T from fun h => hp h.1]

lemma kernel_convolution {α β T t : ℝ} (hα : 0 < α) (hβ : 0 < β) (ht : t ≤ T) :
    realConvolution (powerKernel α T) (powerKernel β T) t =
      (Real.Gamma α * Real.Gamma β / Real.Gamma (α+β)) * powerKernel (α+β) T t := by
  have hind : (Ioc (0 : ℝ) T).indicator (powerKernel β T) = powerKernel β T := by
    simp [powerKernel]
  by_cases hp : 0 < t
  · have he := (power_convolution_bridge α T (powerKernel β T) ⟨hp.le, ht⟩).2
    rw [hind] at he
    rw [he]
    change (∫ s in Ioc 0 t, (t-s) ^ (α-1) • powerKernel β T s) = _
    have he' : (∫ s in Ioc 0 t, (t-s) ^ (α-1) • powerKernel β T s) =
        ∫ s in Ioc 0 t, (t-s) ^ (α-1) * s ^ (β-1) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      simp [powerKernel, show s ∈ Ioc (0 : ℝ) T from ⟨hs.1, hs.2.trans ht⟩]
    rw [he']
    have hb := (beta_convolution α β 0 t hα hβ hp).2
    simp only [sub_zero] at hb
    rw [hb]
    simp [powerKernel, show t ∈ Ioc (0 : ℝ) T from ⟨hp, ht⟩]
  · have hz := convolution_zero_nonpos α T (powerKernel β T) (not_lt.mp hp)
    rw [hind] at hz
    rw [hz]
    simp [powerKernel, show t ∉ Ioc (0 : ℝ) T from fun h => hp h.1]

/-- Kernel replacement needs equality only below T: the zero extension removes
all other arguments of the outer convolution. -/
lemma kernel_composition_bridge {𝕜 : Type} [RCLike 𝕜] {α β T t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (f : ℝ → 𝕜) (ht : t ∈ Icc (0 : ℝ) T) :
    realConvolution (realConvolution (powerKernel α T) (powerKernel β T))
      ((Ioc 0 T).indicator f) t =
      (Real.Gamma α * Real.Gamma β / Real.Gamma (α+β)) • powerValue (α+β) f t := by
  rw [← (power_convolution_bridge (α+β) T f ht).2, realConvolution, realConvolution,
    ← integral_smul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  dsimp only
  by_cases hr : r ≤ T
  · rw [kernel_convolution hα hβ hr, mul_smul]
  · have htr : t-r ∉ Ioc (0 : ℝ) T := by intro h; linarith [h.1, ht.2]
    simp [htr]

lemma nested_composition_bridge {𝕜 : Type} [RCLike 𝕜] (α β T : ℝ)
    (f : ℝ → 𝕜) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    realConvolution (powerKernel α T)
      (realConvolution (powerKernel β T) ((Ioc 0 T).indicator f)) t =
      powerValue α (powerValue β f) t := by
  rw [← (power_convolution_bridge α T (powerValue β f) ht).2]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  dsimp only
  by_cases hr : r ∈ Ioc (0 : ℝ) T
  · rw [power_convolution_below β T f (by linarith [ht.2, hr.1] : t-r ≤ T)]
  · simp [powerKernel, hr]

/-- Positive scalar kernels give an exact norm majorant. Young's bound makes
its outer integral finite a.e.; Tonelli then proves absolute double integrability. -/
lemma absolute_fubini_global {𝕜 : Type} [RCLike 𝕜] {α β T : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hT : 0 < T)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (f : ℝ → 𝕜) (hf : MemLp f p volume) :
    ∀ᵐ t ∂volume, Integrable (fun z : ℝ × ℝ =>
      powerKernel α T z.2 • (powerKernel β T (z.1-z.2) • f (t-z.1)))
      (volume.prod volume) := by
  let a := powerKernel α T
  let b := powerKernel β T
  have ha : Integrable a := (kernel_mass α T hα hT).1
  have hb : Integrable b := (kernel_mass β T hβ hT).1
  have hab : Integrable (realConvolution a b) :=
    ha.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hb
  have hrow : ∀ᵐ x ∂volume, Integrable (fun y => a y * b (x-y)) :=
    (ha.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hb).prod_right_ae
  have hout := (real_young p hp (realConvolution a b) f
    (memLp_one_iff_integrable.mpr hab) hf).1
  filter_upwards [hout] with t ht
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => a z.2 • (b (z.1-z.2) • f (t-z.1)))
      (volume.prod volume) := by
    apply ha.aestronglyMeasurable.comp_snd.smul
    apply AEStronglyMeasurable.smul
    · exact hb.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)
    · exact (hf.aestronglyMeasurable.comp_measurePreserving
        (volume.measurePreserving_sub_left t)).comp_fst
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [hrow] with x hx
    simpa only [mul_smul] using hx.smul_const (f (t-x))
  · convert ht.norm using 1
    ext x
    simp only [norm_smul]
    rw [show (fun y => ‖a y‖ * (‖b (x-y)‖ * ‖f (t-x)‖)) =
      (fun y => (a y * b (x-y)) * ‖f (t-x)‖) by
        ext y
        rw [Real.norm_of_nonneg (powerKernel_nonneg α T y),
          Real.norm_of_nonneg (powerKernel_nonneg β T (x-y)), mul_assoc],
      integral_mul_const,
      Real.norm_of_nonneg (show 0 ≤ realConvolution a b x from
        integral_nonneg (fun y => mul_nonneg (powerKernel_nonneg α T y)
          (powerKernel_nonneg β T (x-y))))]
    rfl

theorem absolute_fubini : Spec.AbsoluteFubini := by
  intro 𝕜 _ α β T hα hβ hT p hp f hf
  by_cases hpos : 0 < T
  · exact ae_restrict_of_ae (absolute_fubini_global hα hβ hpos p hp _
      ((memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr hf))
  · have hz : intervalMeasure T = 0 := by
      simp [intervalMeasure, Ioc_eq_empty hpos]
    simp [hz]

lemma power_semigroup_ae {𝕜 : Type} [RCLike 𝕜] {α β T : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hT : 0 < T)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)) :
    powerValue α (powerValue β f) =ᵐ[intervalMeasure T]
      (fun t => (Real.Gamma α * Real.Gamma β / Real.Gamma (α+β)) • powerValue (α+β) f t) := by
  let a := powerKernel α T
  let b := powerKernel β T
  let f₀ := (Ioc (0 : ℝ) T).indicator f
  let L : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜 := ContinuousLinearMap.lsmul ℝ ℝ
  have ha : Integrable a := (kernel_mass α T hα hT).1
  have hb : Integrable b := (kernel_mass β T hβ hT).1
  have hf₀ : MemLp f₀ p volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr hf
  have hab : ∀ᵐ x ∂volume, ConvolutionExistsAt a b x (ContinuousLinearMap.mul ℝ ℝ) volume :=
    (ha.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hb).prod_right_ae
  have hbf : ∀ᵐ x ∂volume, ConvolutionExistsAt b f₀ x L volume :=
    (real_young p hp b f₀ (memLp_one_iff_integrable.mpr hb) hf₀).1
  filter_upwards [absolute_fubini α β T hα hβ hT.le p hp f hf,
    ae_restrict_mem measurableSet_Ioc] with t hit ht
  have he := convolution_assoc' (ContinuousLinearMap.mul ℝ ℝ) L L L
    (fun x y z => mul_smul x y z) hab hbf hit
  change realConvolution (realConvolution a b) f₀ t =
    realConvolution a (realConvolution b f₀) t at he
  rw [kernel_composition_bridge hα hβ f ⟨ht.1.le, ht.2⟩,
    nested_composition_bridge α β T f ⟨ht.1.le, ht.2⟩] at he
  exact he.symm

lemma powerValue_real_smul {𝕜 : Type} [RCLike 𝕜] (α c : ℝ) (f : ℝ → 𝕜) :
    powerValue α (c • f) = c • powerValue α f := by
  ext t
  simp only [powerValue, Pi.smul_apply, smul_comm (_ : ℝ) c, integral_smul]

/-- Cancellation of the exact Gamma constants after absolute Fubini. -/
theorem representative_semigroup : Spec.RepresentativeSemigroup := by
  intro 𝕜 _ α β T hα hβ hT p hp f hf
  by_cases hpos : 0 < T
  · filter_upwards [power_semigroup_ae hα hβ hpos p hp f hf] with t ht
    change (Real.Gamma α)⁻¹ • powerValue α ((Real.Gamma β)⁻¹ • powerValue β f) t = _
    rw [powerValue_real_smul, Pi.smul_apply, ht]
    simp only [fractionalValue, smul_smul]
    congr 1
    field_simp [(Real.Gamma_pos_of_pos hα).ne', (Real.Gamma_pos_of_pos hβ).ne']
  · have hz : intervalMeasure T = 0 := by
      simp [intervalMeasure, Ioc_eq_empty hpos]
    simp [Filter.EventuallyEq, hz]

/-- Equality of bounded operators on the actual a.e. quotient, including p=∞. -/
theorem lp_semigroup : Spec.LpSemigroup := by
  intro 𝕜 _ α β T hα hβ hT p hp A B C hA hB hC
  ext f
  exact (hA (B f)).trans ((fractionalValue_congr_ae α T (hB f)).trans
    ((representative_semigroup α β T hα hβ hT p hp.out f (Lp.memLp f)).trans (hC f).symm))

/-- Continuous functions agree everywhere, including both endpoints: the a.e.
identity is promoted by continuity on the original closed interval. -/
theorem continuous_semigroup : Spec.ContinuousSemigroup := by
  intro 𝕜 _ α β T hα hβ hT A B C hA hB hC
  have hext (f : C(Icc (0 : ℝ) T, 𝕜)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      continuousExtension hT f t = f ⟨t, ht⟩ := by
    simp [continuousExtension, projIcc_of_mem hT ht]
  apply ContinuousLinearMap.ext
  intro f
  have hf : MemLp (continuousExtension hT f) ∞ (intervalMeasure T) :=
    memLp_top_of_bound (continuous_extension hT f).aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall (extension_norm_le hT f))
  have hb : continuousExtension hT (B f) =ᵐ[intervalMeasure T]
      fractionalValue β (continuousExtension hT f) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [hext (B f) t ⟨ht.1.le, ht.2⟩, hB]
  have he : continuousExtension hT (A (B f)) =ᵐ[intervalMeasure T]
      continuousExtension hT (C f) := by
    have h := (fractionalValue_congr_ae α T hb).trans
      (representative_semigroup α β T hα hβ hT ∞ (by simp) _ hf)
    filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with t ht hmem
    rw [hext (A (B f)) t ⟨hmem.1.le, hmem.2⟩, hA,
      hext (C f) t ⟨hmem.1.le, hmem.2⟩, hC]
    exact ht
  have he' := MeasureTheory.Measure.eqOn_Ioc_of_ae_eq volume he
    (continuous_extension hT (A (B f))).continuousOn
    (continuous_extension hT (C f)).continuousOn
  apply ContinuousMap.ext
  intro t
  change A (B f) t = C f t
  by_cases ht : (t : ℝ) = 0
  · rw [hA, hC, ht, fractional_zero_time, fractional_zero_time]
  · have ht' : (t : ℝ) ∈ Ioc (0 : ℝ) T := ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht), t.property.2⟩
    simpa only [hext _ _ t.property] using he' ht'

lemma continuous_realization {𝕜 : Type} [RCLike 𝕜] {γ T : ℝ}
    (hγ : 0 < γ) (hT : 0 ≤ T) :
    ∃ J : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜),
      ∀ f t, J f t = fractionalValue γ (continuousExtension hT f) t := by
  by_cases hpos : 0 < T
  · obtain ⟨J, hJ, _⟩ := continuous_construction γ T hγ hpos (𝕜 := 𝕜)
    exact ⟨J, fun f t => (hJ f t).2⟩
  · have hz : T = 0 := le_antisymm (not_lt.mp hpos) hT
    subst T
    refine ⟨0, ?_⟩
    intro f t
    have ht : (t : ℝ) = 0 := le_antisymm t.property.2 t.property.1
    simp [ht, fractionalValue, powerValue]

lemma lp_realization {𝕜 : Type} [RCLike 𝕜] {γ T : ℝ}
    (hγ : 0 < γ) (_hT : 0 ≤ T) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ J : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T),
      ∀ f : Lp 𝕜 p (intervalMeasure T),
        (J f : ℝ → 𝕜) =ᵐ[intervalMeasure T] fractionalValue γ f := by
  by_cases hpos : 0 < T
  · obtain ⟨J, hJ, _⟩ := lp_construction γ T hγ hpos p (𝕜 := 𝕜)
    refine ⟨J, fun f => ?_⟩
    simpa only [Lp.toLp_coeFn] using (hJ f (Lp.memLp f)).2
  · have hz : intervalMeasure T = 0 := by simp [intervalMeasure, Ioc_eq_empty hpos]
    exact ⟨0, fun f => by simp [Filter.EventuallyEq, hz]⟩

/-- The existing bounded constructions satisfy the law; at zero length the
continuous realization is zero and the Lp space has only its zero class. -/
theorem continuous_semigroup_realization : Spec.ContinuousSemigroupRealization := by
  intro 𝕜 _ α β T hα hβ hT
  obtain ⟨A, hA⟩ := continuous_realization hα hT (𝕜 := 𝕜)
  obtain ⟨B, hB⟩ := continuous_realization hβ hT (𝕜 := 𝕜)
  obtain ⟨C, hC⟩ := continuous_realization (add_pos hα hβ) hT (𝕜 := 𝕜)
  exact ⟨A, B, C, hA, hB, hC, continuous_semigroup α β T hα hβ hT A B C hA hB hC⟩

theorem lp_semigroup_realization : Spec.LpSemigroupRealization := by
  intro 𝕜 _ α β T hα hβ hT p hp
  obtain ⟨A, hA⟩ := lp_realization hα hT p (𝕜 := 𝕜)
  obtain ⟨B, hB⟩ := lp_realization hβ hT p (𝕜 := 𝕜)
  obtain ⟨C, hC⟩ := lp_realization (add_pos hα hβ) hT p (𝕜 := 𝕜)
  exact ⟨A, B, C, hA, hB, hC, lp_semigroup α β T hα hβ hT p A B C hA hB hC⟩

end ExpandedFA.PartV.BetaSemigroup
