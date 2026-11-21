import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FractionalIntegrals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ExpandedFA.PartV.FractionalIntegrals
open Spec

/-- The unnormalized Brunner power integral. -/
def brunnerPower {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (f : ℝ → 𝕜) : ℝ → 𝕜 :=
  powerValue α f

/-- The normalized Riemann--Liouville integral; its bounded realizations below
are only asserted for positive order. -/
def fractionalIntegral {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (f : ℝ → 𝕜) : ℝ → 𝕜 :=
  fractionalValue α f

def brunnerLogarithmic {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) : ℝ → 𝕜 :=
  logarithmicValue f

lemma power_integrable {α T : ℝ} (hα : 0 < α) :
    IntegrableOn (fun r : ℝ => r ^ (α - 1)) (Ioc 0 T) := by
  exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)).1

lemma power_integral {α T : ℝ} (hα : 0 < α) (hT : 0 ≤ T) :
    (∫ r in Ioc 0 T, r ^ (α - 1)) = T ^ α / α := by
  rw [← intervalIntegral.integral_of_le hT]
  simpa only [sub_add_cancel, Real.zero_rpow hα.ne', sub_zero] using
    (integral_rpow (a := (0 : ℝ)) (b := T) (Or.inl (by linarith : -1 < α - 1)))

/-- Exact L1 mass of the truncated weakly singular kernel. -/
theorem kernel_mass : KernelMass := by
  intro α T hα hT
  have hi := power_integrable (T := T) hα
  have hiK : Integrable (powerKernel α T) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hi
  have hn : ∀ r, ‖powerKernel α T r‖ = powerKernel α T r := by
    intro r
    apply Real.norm_of_nonneg
    by_cases hr : r ∈ Ioc (0 : ℝ) T
    · simpa [powerKernel, hr] using Real.rpow_nonneg hr.1.le (α - 1)
    · simp [powerKernel, hr]
  have hm : (∫ r, ‖powerKernel α T r‖) = T ^ α / α := by
    simp_rw [hn]
    rw [powerKernel, integral_indicator measurableSet_Ioc]
    exact power_integral hα hT.le
  refine ⟨hiK, hm, ?_⟩
  rw [hm, operatorBound, Real.Gamma_add_one hα.ne']
  ring

/-- On the interval, changing representatives cannot change any integral,
even at an exceptional time for which the Bochner integral defaults to zero. -/
theorem representative_independence : RepresentativeIndependence := by
  intro 𝕜 _ α T f g hfg t ht
  have hsub : Ioc (0 : ℝ) t ⊆ Ioc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have he : (fun s => (t-s) ^ (α-1) • f s) =ᵐ[volume.restrict (Ioc 0 t)]
      (fun s => (t-s) ^ (α-1) • g s) := by
    have h := ae_restrict_of_ae_restrict_of_subset hsub hfg
    filter_upwards [h] with s hs
    rw [hs]
  exact ⟨integrable_congr he, congrArg ((Real.Gamma α)⁻¹ • ·) (integral_congr_ae he)⟩

theorem kernel_distinction : KernelDistinction := by
  constructor
  · intro T hT
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hT]
    norm_num
  · intro T hT
    exact (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := T)).1

lemma fractional_zero_time {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (f : ℝ → 𝕜) :
    fractionalValue α f 0 = 0 := by
  simp [fractionalValue, powerValue]

lemma normalization {𝕜 : Type} [RCLike 𝕜] {α : ℝ} (hα : 0 < α)
    (f : ℝ → 𝕜) (t : ℝ) :
    brunnerPower α f t = Real.Gamma α • fractionalIntegral α f t := by
  simp [brunnerPower, fractionalIntegral, fractionalValue, smul_smul,
    (Real.Gamma_pos_of_pos hα).ne']


lemma continuous_extension {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, 𝕜)) : Continuous (continuousExtension hT f) :=
  f.continuous.comp continuous_projIcc

lemma extension_norm_le {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, 𝕜)) (s : ℝ) : ‖continuousExtension hT f s‖ ≤ ‖f‖ :=
  ContinuousMap.norm_coe_le_norm f _

lemma reflected_power_integrable {α t : ℝ} (hα : 0 < α) :
    IntegrableOn (fun s : ℝ => (t-s) ^ (α-1)) (Ioc 0 t) := by
  have h := (intervalIntegral.intervalIntegrable_rpow'
    (a := (0 : ℝ)) (b := t) (by linarith : -1 < α-1)).comp_sub_left t
  simpa only [sub_self, sub_zero] using h.symm.1

lemma reflected_power_integral {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    (∫ s in Ioc 0 t, (t-s) ^ (α-1)) = t ^ α / α := by
  rw [← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_comp_sub_left (fun r : ℝ => r ^ (α-1)) t, sub_self, sub_zero,
    intervalIntegral.integral_of_le ht]
  exact power_integral hα ht

lemma continuous_input_integrable {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, 𝕜)) (t : ℝ) :
    IntegrableOn (fun s => (t-s) ^ (α-1) • continuousExtension hT f s) (Ioc 0 t) := by
  exact (reflected_power_integrable hα).smul_bdd ‖f‖
    (continuous_extension hT f).aestronglyMeasurable
    (Filter.Eventually.of_forall (extension_norm_le hT f))

lemma continuous_input_bound {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, 𝕜))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖fractionalValue α (continuousExtension hT f) t‖ ≤ operatorBound α T * ‖f‖ := by
  have hw : IntegrableOn (fun s : ℝ => (t-s) ^ (α-1) * ‖f‖) (Ioc 0 t) :=
    (reflected_power_integrable hα).mul_const _
  have hb : ‖powerValue α (continuousExtension hT f) t‖ ≤ t ^ α / α * ‖f‖ := by
    rw [← reflected_power_integral hα ht.1, ← integral_mul_const]
    apply norm_integral_le_of_norm_le hw
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)]
    exact mul_le_mul_of_nonneg_left (extension_norm_le hT f s)
      (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)
  rw [fractionalValue, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr
    (Real.Gamma_pos_of_pos hα).le)]
  calc
    _ ≤ (Real.Gamma α)⁻¹ * (t ^ α / α * ‖f‖) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.Gamma_pos_of_pos hα).le)
    _ ≤ (Real.Gamma α)⁻¹ * (T ^ α / α * ‖f‖) := by
      gcongr <;> first | exact ht.1 | exact ht.2
    _ = _ := by rw [operatorBound, Real.Gamma_add_one hα.ne']; ring

/-- Reflection of the integration variable, needed to put the moving endpoint
in an indicator while leaving the singular majorant fixed. -/
lemma powerValue_reflect {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (f : ℝ → 𝕜)
    {t : ℝ} (ht : 0 ≤ t) :
    powerValue α f t = ∫ r in Ioc 0 t, r ^ (α-1) • f (t-r) := by
  rw [powerValue, ← intervalIntegral.integral_of_le ht,
    ← intervalIntegral.integral_of_le ht]
  have he := intervalIntegral.integral_comp_sub_left
    (fun r : ℝ => r ^ (α-1) • f (t-r)) (a := (0 : ℝ)) (b := t) t
  simpa only [sub_sub_cancel, sub_self, sub_zero] using he

lemma continuous_powerValue {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, 𝕜)) :
    ContinuousOn (powerValue α (continuousExtension hT f)) (Icc (0 : ℝ) T) := by
  let F : ℝ → ℝ → 𝕜 := fun t r =>
    r ^ (α-1) • (if r ≤ t then continuousExtension hT f (t-r) else 0)
  have hm (t : ℝ) : AEStronglyMeasurable (F t) (volume.restrict (Ioc 0 T)) := by
    exact (power_integrable (T := T) hα).aestronglyMeasurable.smul
      (Measurable.ite (measurableSet_le measurable_id measurable_const)
        ((continuous_extension hT f).measurable.comp (measurable_const.sub measurable_id))
        measurable_const).aestronglyMeasurable
  have hb (t : ℝ) : ∀ᵐ r ∂volume.restrict (Ioc 0 T), ‖F t r‖ ≤ r ^ (α-1) * ‖f‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    dsimp [F]
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hr.1.le _)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hr.1.le _)
    split_ifs
    · exact extension_norm_le hT f _
    · simp
  have hc : Continuous (fun t => ∫ r in Ioc 0 T, F t r) := by
    apply continuous_iff_continuousAt.mpr
    intro t₀
    apply continuousAt_of_dominated (Filter.Eventually.of_forall hm)
      (Filter.Eventually.of_forall hb) ((power_integrable hα).mul_const ‖f‖)
    have hne : ∀ᵐ r ∂volume.restrict (Ioc 0 T), r ≠ t₀ :=
      ae_restrict_of_ae (volume.ae_ne t₀)
    filter_upwards [hne] with r hr
    have hec : ContinuousAt (fun t => r ^ (α-1) • continuousExtension hT f (t-r)) t₀ :=
      continuousAt_const.smul ((continuous_extension hT f).continuousAt.comp
        (continuousAt_id.sub continuousAt_const))
    rcases lt_or_gt_of_ne hr with hrt | htr
    · apply hec.congr
      filter_upwards [eventually_gt_nhds hrt] with t ht
      simp [F, ht.le]
    · apply (continuousAt_const (y := (0 : 𝕜))).congr
      filter_upwards [eventually_lt_nhds htr] with t ht
      simp [F, not_le.mpr ht]
  apply hc.continuousOn.congr
  intro t ht
  rw [powerValue_reflect α _ ht.1]
  have he : F t = (Iic t).indicator (fun r : ℝ => r ^ (α-1) • continuousExtension hT f (t-r)) := by
    ext r
    simp only [F, indicator_apply, mem_Iic]
    split_ifs <;> simp_all
  change _ = ∫ r in Ioc 0 T, F t r
  rw [he, setIntegral_indicator measurableSet_Iic]
  have hi : Ioc (0 : ℝ) T ∩ Iic t = Ioc 0 t := by
    ext r
    simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨⟨hr, _⟩, hrt⟩; exact ⟨hr, hrt⟩
    · rintro ⟨hr, hrt⟩; exact ⟨⟨hr, hrt.trans ht.2⟩, hrt⟩
  rw [hi]


/-- A bounded realization on continuous functions, with the defining singular
Bochner integral at every time, including zero. -/
theorem continuous_construction : ContinuousConstruction := by
  intro 𝕜 _ α T hα hT
  let hcont (f : C(Icc (0 : ℝ) T, 𝕜)) :
      Continuous (fun t : Icc (0 : ℝ) T => fractionalValue α (continuousExtension hT.le f) t) :=
    (continuous_const.smul ((continuous_powerValue hα hT.le f).comp_continuous
      continuous_subtype_val (fun t => t.property)))
  let L : C(Icc (0 : ℝ) T, 𝕜) →ₗ[𝕜] C(Icc (0 : ℝ) T, 𝕜) :=
    { toFun := fun f => ⟨_, hcont f⟩
      map_add' := by
        intro f g
        ext t
        change fractionalValue α (continuousExtension hT.le (f+g)) t =
          fractionalValue α (continuousExtension hT.le f) t +
          fractionalValue α (continuousExtension hT.le g) t
        simp only [fractionalValue, powerValue, continuousExtension,
          ContinuousMap.add_apply, smul_add]
        have hf := continuous_input_integrable hα hT.le f t
        have hg := continuous_input_integrable hα hT.le g t
        dsimp [continuousExtension] at hf hg
        rw [integral_add hf hg, smul_add]
      map_smul' := by
        intro c f
        ext t
        change fractionalValue α (continuousExtension hT.le (c • f)) t =
          c • fractionalValue α (continuousExtension hT.le f) t
        simp only [fractionalValue, powerValue, continuousExtension,
          ContinuousMap.smul_apply, smul_comm (_ : ℝ) c, integral_smul] }
  have hB : 0 ≤ operatorBound α T :=
    div_nonneg (Real.rpow_nonneg hT.le _) (Real.Gamma_pos_of_pos (by linarith)).le
  have hb (f) : ‖L f‖ ≤ operatorBound α T * ‖f‖ := by
    apply (ContinuousMap.norm_le (L f) (mul_nonneg hB (norm_nonneg f))).mpr
    intro t
    exact continuous_input_bound hα hT.le f t.property
  refine ⟨L.mkContinuous (operatorBound α T) hb, ?_, ?_⟩
  · intro f t
    exact ⟨continuous_input_integrable hα hT.le f t, rfl⟩
  · exact LinearMap.mkContinuous_norm_le _ hB hb


/-- Real-kernel convolution, allowing either real or complex data. -/
def realConvolution {𝕜 : Type} [RCLike 𝕜] (k : ℝ → ℝ) (f : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  ∫ r, k r • f (t-r)

lemma realConvolution_congr {𝕜 : Type} [RCLike 𝕜]
    {k k' : ℝ → ℝ} {f f' : ℝ → 𝕜} (hk : k =ᵐ[volume] k') (hf : f =ᵐ[volume] f') :
    (∀ t, Integrable (fun r => k r • f (t-r)) ↔ Integrable (fun r => k' r • f' (t-r))) ∧
      realConvolution k f = realConvolution k' f' := by
  have he (t : ℝ) : (fun r => k r • f (t-r)) =ᵐ[volume] (fun r => k' r • f' (t-r)) :=
    hk.smul ((volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae hf)
  exact ⟨fun t => integrable_congr (he t), funext fun t => integral_congr_ae (he t)⟩

/-- Young's endpoint estimate on the real line, using the accepted scalar
Minkowski interface for finite exponents and native Hölder for infinity. -/
lemma real_young_measurable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (k : ℝ → ℝ) (f : ℝ → 𝕜)
    (hkm : Measurable k) (hfm : Measurable f) (hk : MemLp k 1 volume) (hf : MemLp f p volume) :
    (∀ᵐ t ∂volume, Integrable (fun r => k r • f (t-r))) ∧
      eLpNorm (realConvolution k f) p volume ≤ eLpNorm k 1 volume * eLpNorm f p volume := by
  let L : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜 := ContinuousLinearMap.lsmul ℝ ℝ
  by_cases hpt : p = ∞
  · subst p
    have hi := ConvolutionExists.of_memLp_memLp L hk hf
    refine ⟨Filter.Eventually.of_forall hi, ?_⟩
    have hm := hk.aestronglyMeasurable.convolution L hf.aestronglyMeasurable
    change eLpNorm (MeasureTheory.convolution k f L volume) ∞ volume ≤ _
    rw [eLpNorm_exponent_top hm]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    apply Filter.Eventually.of_forall
    intro t
    simpa [L] using (enorm_convolution_le L hk.aestronglyMeasurable hf.aestronglyMeasurable t)
  let F : ℝ × ℝ → 𝕜 := fun z => k z.2 • f (z.1-z.2)
  have hF : Measurable F := (hkm.comp measurable_snd).smul
    (hfm.comp (measurable_fst.sub measurable_snd))
  have hs (r : ℝ) : eLpNorm (fun t => F (t,r)) p volume = ‖k r‖ₑ * eLpNorm f p volume := by
    change eLpNorm ((k r) • (fun t => f (t-r))) p volume = _
    rw [eLpNorm_const_smul]
    exact congrArg (‖k r‖ₑ * ·) (eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
      (measurePreserving_sub_right volume r))
  have hR : (∫⁻ r, eLpNorm (fun t => F (t,r)) p volume) =
      eLpNorm k 1 volume * eLpNorm f p volume := by
    simp_rw [hs]
    rw [lintegral_mul_const _ hkm.enorm, ← eLpNorm_one_eq_lintegral_enorm hk.aestronglyMeasurable]
  obtain ⟨hi, hb⟩ := ExpandedFA.Distributions.minkowski_integral_eLpNorm
    volume volume p hp hpt F hF
    (by rw [hR]; exact ENNReal.mul_lt_top hk.eLpNorm_lt_top hf.eLpNorm_lt_top)
  exact ⟨hi, hb.trans_eq hR⟩

lemma real_young {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) (hp : 1 ≤ p)
    (k : ℝ → ℝ) (f : ℝ → 𝕜) (hk : MemLp k 1 volume) (hf : MemLp f p volume) :
    (∀ᵐ t ∂volume, Integrable (fun r => k r • f (t-r))) ∧
    MemLp (realConvolution k f) p volume ∧
    eLpNorm (realConvolution k f) p volume ≤ eLpNorm k 1 volume * eLpNorm f p volume := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  have hkm := hk.aestronglyMeasurable
  have hfm := hf.aestronglyMeasurable
  let k' := hkm.mk k
  let f' := hfm.mk f
  have hkk : k =ᵐ[volume] k' := hkm.ae_eq_mk
  have hff : f =ᵐ[volume] f' := hfm.ae_eq_mk
  have he := realConvolution_congr hkk hff
  obtain ⟨hi, hb⟩ := real_young_measurable p hp k' f'
    hkm.stronglyMeasurable_mk.measurable hfm.stronglyMeasurable_mk.measurable
    (hk.ae_eq hkk) (hf.ae_eq hff)
  rw [← he.2, eLpNorm_congr_ae hkk.symm, eLpNorm_congr_ae hff.symm] at hb
  exact ⟨hi.mono (fun t ht => (he.1 t).mpr ht),
    hb.trans_lt (ENNReal.mul_lt_top hk.eLpNorm_lt_top hf.eLpNorm_lt_top), hb⟩


/-- The truncated convolution is the original triangular integral on the
interval. Endpoint differences are removed only on Lebesgue null sets. -/
lemma power_convolution_bridge {𝕜 : Type} [RCLike 𝕜] (α T : ℝ) (f : ℝ → 𝕜)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (Integrable (fun r => powerKernel α T r • ((Ioc 0 T).indicator f) (t-r)) ↔
      IntegrableOn (fun s => (t-s) ^ (α-1) • f s) (Ioc 0 t)) ∧
    realConvolution (powerKernel α T) ((Ioc 0 T).indicator f) t = powerValue α f t := by
  let L : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜 := ContinuousLinearMap.lsmul ℝ ℝ
  have he : (fun s => powerKernel α T (t-s) • (Ioc 0 T).indicator f s) =ᵐ[volume]
      (Ioc 0 t).indicator (fun s => (t-s) ^ (α-1) • f s) := by
    filter_upwards [volume.ae_ne t] with s hst
    by_cases hs : s ∈ Ioc (0 : ℝ) t
    · have hsT : s ∈ Ioc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      have hts : t-s ∈ Ioc (0 : ℝ) T := by
        constructor
        · exact sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
        · linarith [hs.1, ht.2]
      simp [powerKernel, hs, hsT, hts]
    · by_cases hsT : s ∈ Ioc (0 : ℝ) T
      · have hts : t-s ∉ Ioc (0 : ℝ) T := by
          intro h
          exact hs ⟨hsT.1, (sub_pos.mp h.1).le⟩
        simp [powerKernel, hs, hsT, hts]
      · simp [powerKernel, hs, hsT]
  have hi : Integrable (fun r => powerKernel α T r • ((Ioc 0 T).indicator f) (t-r)) ↔
      Integrable (fun s => powerKernel α T (t-s) • (Ioc 0 T).indicator f s) := by
    exact convolutionExistsAt_iff_integrable_swap (L := L)
  refine ⟨hi.trans ((integrable_congr he).trans (integrable_indicator_iff measurableSet_Ioc)), ?_⟩
  change MeasureTheory.convolution _ _ L volume t = _
  rw [convolution_eq_swap L]
  change (∫ s, powerKernel α T (t-s) • (Ioc 0 T).indicator f s) = _
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioc]
  rfl

lemma kernel_eLpNorm {α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    eLpNorm (powerKernel α T) 1 volume = ENNReal.ofReal (T ^ α / α) := by
  obtain ⟨hi, hm, _⟩ := kernel_mass α T hα hT
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi, hm]

/-- MemLp, absolute existence a.e., and the quantitative extended norm bound
for the actual interval integral, before passing to quotient spaces. -/
lemma fractional_memLp {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 < T) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)) :
    (∀ᵐ t ∂intervalMeasure T,
      IntegrableOn (fun s => (t-s) ^ (α-1) • f s) (Ioc 0 t)) ∧
    MemLp (fractionalValue α f) p (intervalMeasure T) ∧
    eLpNorm (fractionalValue α f) p (intervalMeasure T) ≤
      ENNReal.ofReal (operatorBound α T) * eLpNorm f p (intervalMeasure T) := by
  have hk := (kernel_mass α T hα hT).1
  have hfe : MemLp ((Ioc (0 : ℝ) T).indicator f) p volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr hf
  obtain ⟨hi, hm, hb⟩ := real_young p hp (powerKernel α T) _
    (memLp_one_iff_integrable.mpr hk) hfe
  have he : realConvolution (powerKernel α T) ((Ioc 0 T).indicator f) =ᵐ[intervalMeasure T]
      powerValue α f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (power_convolution_bridge α T f ⟨ht.1.le, ht.2⟩).2
  have hi' : ∀ᵐ t ∂intervalMeasure T,
      IntegrableOn (fun s => (t-s) ^ (α-1) • f s) (Ioc 0 t) := by
    filter_upwards [ae_restrict_of_ae hi, ae_restrict_mem measurableSet_Ioc] with t hit ht
    exact (power_convolution_bridge α T f ⟨ht.1.le, ht.2⟩).1.mp hit
  have hb' : eLpNorm (powerValue α f) p (intervalMeasure T) ≤
      ENNReal.ofReal (T ^ α / α) * eLpNorm f p (intervalMeasure T) := by
    rw [← eLpNorm_congr_ae he]
    apply (eLpNorm_restrict_le _ _ _ _).trans
    simpa only [kernel_eLpNorm hα hT,
      eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc.nullMeasurableSet, intervalMeasure] using hb
  have hbound : eLpNorm (fractionalValue α f) p (intervalMeasure T) ≤
      ENNReal.ofReal (operatorBound α T) * eLpNorm f p (intervalMeasure T) := by
    change eLpNorm ((Real.Gamma α)⁻¹ • powerValue α f) p (intervalMeasure T) ≤ _
    rw [eLpNorm_const_smul]
    calc
      _ ≤ ‖(Real.Gamma α)⁻¹‖ₑ * (ENNReal.ofReal (T ^ α / α) * eLpNorm f p (intervalMeasure T)) :=
        mul_le_mul' le_rfl hb'
      _ = _ := by
        rw [Real.enorm_eq_ofReal (inv_nonneg.mpr (Real.Gamma_pos_of_pos hα).le),
          ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.Gamma_pos_of_pos hα).le)]
        congr 2
        rw [operatorBound, Real.Gamma_add_one hα.ne']
        ring
  exact ⟨hi', hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf), hbound⟩


lemma fractionalValue_congr_ae {𝕜 : Type} [RCLike 𝕜] (α T : ℝ)
    {f g : ℝ → 𝕜} (he : f =ᵐ[intervalMeasure T] g) :
    fractionalValue α f =ᵐ[intervalMeasure T] fractionalValue α g := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (representative_independence α T f g he t ⟨ht.1.le, ht.2⟩).2

lemma fractionalValue_add {𝕜 : Type} [RCLike 𝕜] {α t : ℝ} {f g : ℝ → 𝕜}
    (hf : IntegrableOn (fun s => (t-s) ^ (α-1) • f s) (Ioc 0 t))
    (hg : IntegrableOn (fun s => (t-s) ^ (α-1) • g s) (Ioc 0 t)) :
    fractionalValue α (f+g) t = fractionalValue α f t + fractionalValue α g t := by
  simp only [fractionalValue, powerValue, Pi.add_apply, smul_add]
  rw [integral_add hf hg, smul_add]

lemma fractionalValue_smul {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (c : 𝕜) (f : ℝ → 𝕜) :
    fractionalValue α (c • f) = c • fractionalValue α f := by
  funext t
  simp only [fractionalValue, powerValue, Pi.smul_apply, smul_comm (_ : ℝ) c, integral_smul]

/-- Realization on the ordinary Lp quotient for every 1 ≤ p ≤ infinity. The
formula holds for every representative, and the operator bound is unchanged. -/
theorem lp_construction : LpConstruction := by
  intro 𝕜 _ α T hα hT p hp
  let μ := intervalMeasure T
  let mem (f : Lp 𝕜 p μ) : MemLp (fractionalValue α f) p μ :=
    (fractional_memLp hα hT p hp.out f (Lp.memLp f)).2.1
  let out (f : Lp 𝕜 p μ) : Lp 𝕜 p μ := (mem f).toLp (fractionalValue α f)
  have ho (f : Lp 𝕜 p μ) : (out f : ℝ → 𝕜) =ᵐ[μ] fractionalValue α f := (mem f).coeFn_toLp
  let L : Lp 𝕜 p μ →ₗ[𝕜] Lp 𝕜 p μ :=
    { toFun := out
      map_add' := by
        intro f g
        apply Lp.ext
        have he := fractionalValue_congr_ae α T (Lp.coeFn_add f g)
        have ha : fractionalValue α ((f : ℝ → 𝕜) + (g : ℝ → 𝕜)) =ᵐ[μ]
            (fractionalValue α f + fractionalValue α g) := by
          filter_upwards [(fractional_memLp hα hT p hp.out f (Lp.memLp f)).1,
            (fractional_memLp hα hT p hp.out g (Lp.memLp g)).1] with t hft hgt
          exact fractionalValue_add hft hgt
        exact (ho (f+g)).trans (he.trans (ha.trans
          (((ho f).add (ho g)).symm.trans (Lp.coeFn_add (out f) (out g)).symm)))
      map_smul' := by
        intro c f
        apply Lp.ext
        have he := fractionalValue_congr_ae α T (Lp.coeFn_smul c f)
        rw [fractionalValue_smul] at he
        exact (ho (c • f)).trans (he.trans
          (((ho f).const_smul c).symm.trans (Lp.coeFn_smul c (out f)).symm)) }
  have hB : 0 ≤ operatorBound α T :=
    div_nonneg (Real.rpow_nonneg hT.le _) (Real.Gamma_pos_of_pos (by linarith)).le
  have hb (f : Lp 𝕜 p μ) : ‖L f‖ ≤ operatorBound α T * ‖f‖ := by
    change ‖(mem f).toLp (fractionalValue α f)‖ ≤ _
    rw [Lp.norm_toLp, Lp.norm_def]
    have h := (fractional_memLp hα hT p hp.out f (Lp.memLp f)).2.2
    have hn := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp f).ne) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] at hn
    exact hn
  refine ⟨L.mkContinuous (operatorBound α T) hb, ?_, LinearMap.mkContinuous_norm_le _ hB hb⟩
  intro f hf
  refine ⟨(fractional_memLp hα hT p hp.out f hf).1, ?_⟩
  exact (ho (hf.toLp f)).trans (fractionalValue_congr_ae α T hf.coeFn_toLp)

end ExpandedFA.PartV.FractionalIntegrals
