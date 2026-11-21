import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.SchurLp
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Interpolation.RieszThorin
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal

namespace ExpandedFA.PartV.SchurLp

@[simp] theorem schurConstant_one (A B : ℝ≥0) : schurConstant A B 1 = B := by
  simp [schurConstant]

@[simp] theorem schurConstant_top (A B : ℝ≥0) : schurConstant A B ∞ = A := by
  simp [schurConstant]

/-- Changing the input on a null set changes no section integral. -/
theorem kernelValue_congr {X Y 𝕜 : Type*} [MeasurableSpace Y] [RCLike 𝕜]
    (ν : Measure Y) (k : X × Y → 𝕜) {f g : Y → 𝕜} (h : f =ᵐ[ν] g) :
    kernelValue ν k f = kernelValue ν k g := by
  funext x
  exact integral_congr_ae (h.mono fun y hy => congrArg (k (x,y) * ·) hy)

section Endpoints
variable {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
  (k : X × Y → 𝕜) (hk : Measurable k)

include hk

omit [SigmaFinite μ] in
lemma kernelValue_aestronglyMeasurable {f : Y → 𝕜}
    (hf : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable (kernelValue ν k f) μ := by
  exact (hk.aestronglyMeasurable.mul hf.comp_snd).integral_prod_right'

/-- Tonelli applied to the column bound, before taking any Bochner integral. -/
lemma kernel_lintegral_bound {B : ℝ≥0}
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖k (x,y)‖ₑ ∂μ ≤ B)
    {f : Y → 𝕜} (hf : AEStronglyMeasurable f ν) :
    (∫⁻ z : X × Y, ‖k z * f z.2‖ₑ ∂μ.prod ν) ≤ B * ∫⁻ y, ‖f y‖ₑ ∂ν := by
  have hFm : AEStronglyMeasurable (fun z : X × Y => k z * f z.2) (μ.prod ν) :=
    hk.aestronglyMeasurable.mul hf.comp_snd
  rw [lintegral_prod_symm _ hFm.enorm]
  calc
    _ = ∫⁻ y, (∫⁻ x, ‖k (x,y)‖ₑ ∂μ) * ‖f y‖ₑ ∂ν := by
      apply lintegral_congr
      intro y
      simp_rw [enorm_mul]
      exact lintegral_mul_const _ (hk.comp measurable_prodMk_right).enorm
    _ ≤ ∫⁻ y, (B : ℝ≥0∞) * ‖f y‖ₑ ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hB] with y hy using mul_le_mul_left hy _
    _ = _ := lintegral_const_mul'' _ hf.enorm

lemma kernel_endpoint_one {B : ℝ≥0}
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖k (x,y)‖ₑ ∂μ ≤ B)
    {f : Y → 𝕜} (hf : MemLp f 1 ν) :
    (∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν) ∧
      MemLp (kernelValue ν k f) 1 μ ∧
      eLpNorm (kernelValue ν k f) 1 μ ≤ B * eLpNorm f 1 ν := by
  have hbound := kernel_lintegral_bound μ ν k hk hB hf.aestronglyMeasurable
  have hfin : (∫⁻ z : X × Y, ‖k z * f z.2‖ₑ ∂μ.prod ν) < ∞ := by
    apply hbound.trans_lt
    rw [← eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hf
  have hF : Integrable (fun z : X × Y => k z * f z.2) (μ.prod ν) :=
    ⟨hk.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd, hfin⟩
  refine ⟨hF.prod_right_ae, memLp_one_iff_integrable.mpr hF.integral_prod_left, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm (kernelValue_aestronglyMeasurable μ ν k hk hf.aestronglyMeasurable),
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ‖k (x,y) * f y‖ₑ ∂ν ∂μ :=
      lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ z : X × Y, ‖k z * f z.2‖ₑ ∂μ.prod ν :=
      (lintegral_prod _ hF.aestronglyMeasurable.enorm).symm
    _ ≤ _ := hbound

lemma kernel_endpoint_top {A : ℝ≥0}
    (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖k (x,y)‖ₑ ∂ν ≤ A)
    {f : Y → 𝕜} (hf : MemLp f ∞ ν) :
    (∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν) ∧
      MemLp (kernelValue ν k f) ∞ μ ∧
      eLpNorm (kernelValue ν k f) ∞ μ ≤ A * eLpNorm f ∞ ν := by
  have hs : ∀ x, AEStronglyMeasurable (fun y => k (x,y) * f y) ν :=
    fun x => (hk.comp measurable_prodMk_left).aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, (∫⁻ y, ‖k (x,y) * f y‖ₑ ∂ν) ≤ A * eLpNorm f ∞ ν := by
    filter_upwards [hA] with x hx
    calc
      _ ≤ ∫⁻ y, ‖k (x,y)‖ₑ * eLpNorm f ∞ ν ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [enorm_ae_le_eLpNormEssSup f ν] with y hy
        simpa only [enorm_mul, eLpNorm_exponent_top hf.aestronglyMeasurable] using mul_le_mul_right hy ‖k (x,y)‖ₑ
      _ = (∫⁻ y, ‖k (x,y)‖ₑ ∂ν) * eLpNorm f ∞ ν :=
        lintegral_mul_const _ (hk.comp measurable_prodMk_left).enorm
      _ ≤ _ := mul_le_mul_left hx _
  have hfin : (A : ℝ≥0∞) * eLpNorm f ∞ ν < ∞ :=
    ENNReal.mul_lt_top ENNReal.coe_lt_top hf
  have hi : ∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν := by
    filter_upwards [hbound] with x hx
    exact ⟨hs x, hx.trans_lt hfin⟩
  have hnorm : ∀ᵐ x ∂μ, ‖kernelValue ν k f x‖ₑ ≤ A * eLpNorm f ∞ ν := by
    filter_upwards [hbound] with x hx
    exact (enorm_integral_le_lintegral_enorm _).trans hx
  have hb : eLpNorm (kernelValue ν k f) ∞ μ ≤ A * eLpNorm f ∞ ν := by
    rw [eLpNorm_exponent_top (kernelValue_aestronglyMeasurable μ ν k hk hf.aestronglyMeasurable)]
    exact eLpNormEssSup_le_of_ae_enorm_bound hnorm
  exact ⟨hi, hb.trans_lt hfin, hb⟩

end Endpoints

/-- Both endpoint estimates use the actual integral, including absolute existence. -/
theorem kernel_endpoint_estimates : Spec.EndpointEstimates := by
  intro X Y 𝕜 _ _ _ _ _ μ ν _ _ k hk A B h f
  exact ⟨fun hf => kernel_endpoint_one μ ν k hk h.2 hf,
    fun hf => kernel_endpoint_top μ ν k hk h.1 hf⟩


/-- Absolute existence does not depend on the chosen input representative. -/
lemma kernel_integrable_congr {X Y 𝕜 : Type*} [MeasurableSpace Y] [RCLike 𝕜]
    (ν : Measure Y) (k : X × Y → 𝕜) {f g : Y → 𝕜} (h : f =ᵐ[ν] g) (x : X) :
    Integrable (fun y => k (x,y) * f y) ν ↔ Integrable (fun y => k (x,y) * g y) ν :=
  integrable_congr (h.mono fun y hy => congrArg (k (x,y) * ·) hy)

/-- The maximal a.e. absolute-existence domain in the ordinary a.e. quotient. -/
def kernelDomain {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    (μ : Measure X) (ν : Measure Y) (k : X × Y → 𝕜) : Submodule 𝕜 (Y →ₘ[ν] 𝕜) where
  carrier := {f | ∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν}
  zero_mem' := by
    change ∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * (0 : Y →ₘ[ν] 𝕜) y) ν
    exact Eventually.of_forall fun x =>
      (kernel_integrable_congr ν k AEEqFun.coeFn_zero x).mpr (by simp)
  add_mem' := by
    intro f g hf hg
    change ∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * (f+g) y) ν
    filter_upwards [hf, hg] with x hx hx'
    apply (kernel_integrable_congr ν k (AEEqFun.coeFn_add f g) x).mpr
    convert hx.add hx' using 1
    ext y
    simp only [Pi.add_apply, mul_add]
  smul_mem' := by
    intro c f hf
    change ∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * (c • f) y) ν
    filter_upwards [hf] with x hx
    apply (kernel_integrable_congr ν k (AEEqFun.coeFn_smul c f) x).mpr
    simpa only [Pi.smul_apply, smul_eq_mul, mul_left_comm] using hx.const_mul c

/-- A single linear map, before choosing any exponent. -/
def kernelDomainMap {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → 𝕜) (hk : Measurable k) :
    kernelDomain μ ν k →ₗ[𝕜] (X →ₘ[μ] 𝕜) where
  toFun f := AEEqFun.mk (kernelValue ν k (f : Y →ₘ[ν] 𝕜))
    (kernelValue_aestronglyMeasurable μ ν k hk (f : Y →ₘ[ν] 𝕜).aestronglyMeasurable)
  map_add' f g := by
    apply AEEqFun.ext
    have he := kernelValue_congr ν k (AEEqFun.coeFn_add (f : Y →ₘ[ν] 𝕜) (g : Y →ₘ[ν] 𝕜))
    refine (AEEqFun.coeFn_mk _ _).trans ?_
    refine EventuallyEq.trans ?_
      (((AEEqFun.coeFn_mk _ _).add (AEEqFun.coeFn_mk _ _)).symm.trans (AEEqFun.coeFn_add _ _).symm)
    filter_upwards [f.property, g.property] with x hx hx'
    change kernelValue ν k ((f : Y →ₘ[ν] 𝕜) + (g : Y →ₘ[ν] 𝕜) : Y →ₘ[ν] 𝕜) x = _
    rw [he]
    simpa only [kernelValue, Pi.add_apply, mul_add] using integral_add hx hx'
  map_smul' c f := by
    apply AEEqFun.ext
    have he := kernelValue_congr ν k (AEEqFun.coeFn_smul c (f : Y →ₘ[ν] 𝕜))
    refine (AEEqFun.coeFn_mk _ _).trans ?_
    refine EventuallyEq.trans ?_
      (((AEEqFun.coeFn_mk _ _).const_smul c).symm.trans (AEEqFun.coeFn_smul _ _).symm)
    exact Eventually.of_forall fun x => by
      change kernelValue ν k (c • (f : Y →ₘ[ν] 𝕜) : Y →ₘ[ν] 𝕜) x = _
      rw [he]
      simp only [kernelValue, Pi.smul_apply, smul_eq_mul, mul_left_comm,
        integral_const_mul]

section Complex
open ExpandedFA.Interpolation.RieszThorinSpec
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → ℂ) (hk : Measurable k) (A B : ℝ≥0)
    (h : KernelBounds μ ν k A B)

include hk h

lemma sum_le_kernelDomain : SumSpace ν 1 ∞ ≤ kernelDomain μ ν k := by
  apply sup_le
  · intro f hf
    exact (kernel_endpoint_one μ ν k hk h.2 hf).1
  · intro f hf
    exact (kernel_endpoint_top μ ν k hk h.1 hf).1

/-- Compatible endpoints inside the common L¹ + L∞ domain. -/
def kernelSumMap : SumSpace ν 1 ∞ →ₗ[ℂ] (X →ₘ[μ] ℂ) :=
  (kernelDomainMap μ ν k hk).comp
    (Submodule.inclusion (sum_le_kernelDomain μ ν k hk A B h))

lemma kernelSumMap_coe (f : SumSpace ν 1 ∞) :
    (kernelSumMap μ ν k hk A B h f : X → ℂ) =ᵐ[μ]
      kernelValue ν k (f : Y →ₘ[ν] ℂ) := AEEqFun.coeFn_mk _ _

lemma kernelSumMap_endpoints :
    EndpointBound (kernelSumMap μ ν k hk A B h) 1 1 B ∧
    EndpointBound (kernelSumMap μ ν k hk A B h) ∞ ∞ A := by
  constructor
  · intro f hf
    obtain ⟨_, hm, hb⟩ := kernel_endpoint_one μ ν k hk h.2 hf
    have he := kernelSumMap_coe μ ν k hk A B h f
    refine ⟨hm.ae_eq he.symm, ?_⟩
    rw [eLpNorm_congr_ae he]
    simpa only [ENNReal.ofReal_coe_nnreal] using hb
  · intro f hf
    obtain ⟨_, hm, hb⟩ := kernel_endpoint_top μ ν k hk h.1 hf
    have he := kernelSumMap_coe μ ν k hk A B h f
    refine ⟨hm.ae_eq he.symm, ?_⟩
    rw [eLpNorm_congr_ae he]
    simpa only [ENNReal.ofReal_coe_nnreal] using hb


omit hk h in
lemma schur_interpolation_parameter (p : ℝ≥0∞) (hp : 1 < p) (hpt : p ≠ ∞) :
    0 < 1 - (p⁻¹).toReal ∧ 1 - (p⁻¹).toReal < 1 ∧
      Interpolates 1 ∞ p (1 - (p⁻¹).toReal) := by
  have hpn : p⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (ne_of_gt (zero_lt_one.trans hp))
  have hpr : (p⁻¹).toReal < 1 := by
    exact (ENNReal.toReal_lt_toReal hpn ENNReal.one_ne_top).mpr
      (by simpa using ENNReal.inv_lt_inv.mpr hp)
  have hpr0 : 0 < (p⁻¹).toReal := ENNReal.toReal_pos (by simpa using hpt) hpn
  refine ⟨sub_pos.mpr hpr, by linarith, ?_⟩
  simp only [Interpolates, inv_one, ENNReal.inv_top, mul_one, mul_zero, add_zero]
  rw [sub_sub_cancel, ENNReal.ofReal_toReal hpn]

lemma kernel_complex_interior (p : ℝ≥0∞) (hp : 1 < p) (hpt : p ≠ ∞)
    {f : Y → ℂ} (hf : MemLp f p ν) :
    (∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν) ∧
      MemLp (kernelValue ν k f) p μ ∧
      eLpNorm (kernelValue ν k f) p μ ≤
        ENNReal.ofReal (schurConstant A B p) * eLpNorm f p ν := by
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  obtain ⟨hθ0, hθ1, hpi⟩ := schur_interpolation_parameter p hp hpt
  obtain ⟨h₀, h₁⟩ := kernelSumMap_endpoints μ ν k hk A B h
  obtain ⟨hF, hmem, hb⟩ := ExpandedFA.Interpolation.riesz_thorin ν μ 1 ∞ 1 ∞ p p
    (1 - (p⁻¹).toReal) B A hθ0 hθ1 B.coe_nonneg A.coe_nonneg hpi hpi
    (kernelSumMap μ ν k hk A B h) h₀ h₁ (hf.toLp f)
  let F : SumSpace ν 1 ∞ := ⟨(hf.toLp f : Y →ₘ[ν] ℂ), hF⟩
  have hff : (F : Y →ₘ[ν] ℂ) =ᵐ[ν] f := hf.coeFn_toLp
  have he := (kernelSumMap_coe μ ν k hk A B h F).trans
    (Eventually.of_forall fun x => congrFun (kernelValue_congr ν k hff) x)
  have hiF := (sum_le_kernelDomain μ ν k hk A B h) hF
  have hi : ∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν := by
    filter_upwards [hiF] with x hx
    exact (kernel_integrable_congr ν k hff x).mp hx
  have hm := hmem.ae_eq he
  have hC : 0 ≤ schurConstant A B p :=
    mul_nonneg (Real.rpow_nonneg A.coe_nonneg _) (Real.rpow_nonneg B.coe_nonneg _)
  refine ⟨hi, hm, ?_⟩
  have hb' : (eLpNorm (kernelValue ν k f) p μ).toReal ≤
      schurConstant A B p * (eLpNorm f p ν).toReal := by
    rw [← eLpNorm_congr_ae he]
    simpa only [schurConstant, sub_sub_cancel, Lp.norm_toLp, mul_comm] using hb
  apply (ENNReal.toReal_le_toReal hm.ne
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.ne)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using hb'

end Complex


/-- Complexification of a modulus preserves every Lp norm. -/
lemma eLpNorm_complex_modulus {Y 𝕜 : Type*} [MeasurableSpace Y] [RCLike 𝕜]
    (ν : Measure Y) (p : ℝ≥0∞) {f : Y → 𝕜} (hf : AEStronglyMeasurable f ν) :
    eLpNorm (fun y => (‖f y‖ : ℂ)) p ν = eLpNorm f p ν := by
  apply eLpNorm_congr_norm_ae
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.norm) hf
  exact Eventually.of_forall fun y => by simp

/-- The sharp representative estimate for either scalar field and every exponent.
Complex interpolation is applied to the positive kernel and to the modulus of f. -/
lemma kernel_estimate {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → 𝕜) (hk : Measurable k) (A B : ℝ≥0)
    (h : KernelBounds μ ν k A B) (p : ℝ≥0∞) (hp : 1 ≤ p)
    {f : Y → 𝕜} (hf : MemLp f p ν) :
    (∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν) ∧
      MemLp (kernelValue ν k f) p μ ∧
      eLpNorm (kernelValue ν k f) p μ ≤
        ENNReal.ofReal (schurConstant A B p) * eLpNorm f p ν := by
  by_cases hp1 : p = 1
  · subst p
    simpa only [schurConstant_one, ENNReal.ofReal_coe_nnreal] using
      kernel_endpoint_one μ ν k hk h.2 hf
  by_cases hpt : p = ∞
  · subst p
    simpa only [schurConstant_top, ENNReal.ofReal_coe_nnreal] using
      kernel_endpoint_top μ ν k hk h.1 hf
  let K : X × Y → ℂ := fun z => (‖k z‖ : ℂ)
  let F : Y → ℂ := fun y => (‖f y‖ : ℂ)
  have hK : Measurable K := Complex.measurable_ofReal.comp hk.norm
  have hF : AEStronglyMeasurable F ν :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable.norm
  have hFn : eLpNorm F p ν = eLpNorm f p ν := eLpNorm_complex_modulus ν p hf.aestronglyMeasurable
  have hKB : KernelBounds μ ν K A B := by
    simpa only [KernelBounds, K, enorm_eq_nnnorm, Complex.nnnorm_real,
      nnnorm_norm] using h
  obtain ⟨hi, hm, hb⟩ := kernel_complex_interior μ ν K hK A B hKB p
    (lt_of_le_of_ne hp (Ne.symm hp1)) hpt (by rw [memLp_iff, hFn]; exact hf)
  have hi' : ∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν := by
    filter_upwards [hi] with x hx
    have hn : Integrable (fun y => ‖k (x,y) * f y‖) ν := by
      have H := hx.norm
      simpa only [K, F, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm] using H
    exact (integrable_norm_iff
      ((hk.comp measurable_prodMk_left).aestronglyMeasurable.mul hf.aestronglyMeasurable)).mp hn
  have hmeas := kernelValue_aestronglyMeasurable μ ν k hk hf.aestronglyMeasurable
  have hdom : ∀ᵐ x ∂μ, ‖kernelValue ν k f x‖ ≤ ‖kernelValue ν K F x‖ := by
    exact Eventually.of_forall fun x => by
      have he : kernelValue ν K F x = (∫ y, ‖k (x,y) * f y‖ ∂ν : ℝ) := by
        simp only [kernelValue, K, F, ← Complex.ofReal_mul, ← norm_mul, integral_complex_ofReal]
      rw [he, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg (fun y => norm_nonneg (k (x,y) * f y)))]
      exact norm_integral_le_integral_norm _
  have hbound := (eLpNorm_mono_ae hmeas hdom).trans hb
  rw [hFn] at hbound
  exact ⟨hi', (eLpNorm_mono_ae hmeas hdom).trans_lt hm, hbound⟩


section Operator
variable {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → 𝕜) (hk : Measurable k) (A B : ℝ≥0)
    (h : KernelBounds μ ν k A B) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The restriction of the common integral map to Lp. -/
def kernelLpLinear : Lp 𝕜 p ν →ₗ[𝕜] Lp 𝕜 p μ := by
  let j : Lp 𝕜 p ν →ₗ[𝕜] kernelDomain μ ν k := {
    toFun f := ⟨(f : Y →ₘ[ν] 𝕜), (kernel_estimate μ ν k hk A B h p Fact.out (Lp.memLp f)).1⟩
    map_add' f g := rfl
    map_smul' c f := rfl }
  let M := (kernelDomainMap μ ν k hk).comp j
  exact {
    toFun f := ⟨M f, ((kernel_estimate μ ν k hk A B h p Fact.out (Lp.memLp f)).2.1).ae_eq
      (AEEqFun.coeFn_mk _ _).symm⟩
    map_add' f g := Subtype.ext (M.map_add f g)
    map_smul' c f := Subtype.ext (M.map_smul c f) }

lemma kernelLpLinear_coe (f : Lp 𝕜 p ν) :
    (kernelLpLinear μ ν k hk A B h p f : X → 𝕜) =ᵐ[μ] kernelValue ν k f :=
  AEEqFun.coeFn_mk _ _

lemma kernelLpLinear_bound (f : Lp 𝕜 p ν) :
    ‖kernelLpLinear μ ν k hk A B h p f‖ ≤ schurConstant A B p * ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (kernelLpLinear_coe μ ν k hk A B h p f), Lp.norm_def]
  have hb := (kernel_estimate μ ν k hk A B h p Fact.out (Lp.memLp f)).2.2
  have hC : 0 ≤ schurConstant A B p :=
    mul_nonneg (Real.rpow_nonneg A.coe_nonneg _) (Real.rpow_nonneg B.coe_nonneg _)
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp f).ne) hb
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using ht

/-- The bounded operator, with no arbitrary extension choices at L∞. -/
def kernelLpOperator : Lp 𝕜 p ν →L[𝕜] Lp 𝕜 p μ :=
  (kernelLpLinear μ ν k hk A B h p).mkContinuous (schurConstant A B p)
    (kernelLpLinear_bound μ ν k hk A B h p)

lemma kernelLpOperator_norm_le :
    ‖kernelLpOperator μ ν k hk A B h p‖ ≤ schurConstant A B p := by
  apply LinearMap.mkContinuous_norm_le
  exact mul_nonneg (Real.rpow_nonneg A.coe_nonneg _) (Real.rpow_nonneg B.coe_nonneg _)

end Operator

/-- Unweighted Schur's test, including both fields, the endpoints, compatibility,
and the actual a.e. absolutely convergent integral on every Lp input. -/
theorem schur_boundedness : Spec.SchurBoundedness := by
  intro X Y 𝕜 _ _ _ _ _ μ ν _ _ k hk A B h
  refine ⟨{
    op := fun p _ => kernelLpOperator μ ν k hk A B h p
    integral_exists := fun p _ f => (kernel_estimate μ ν k hk A B h p Fact.out (Lp.memLp f)).1
    represents := fun p _ f => kernelLpLinear_coe μ ν k hk A B h p f
    norm_le := fun p _ => kernelLpOperator_norm_le μ ν k hk A B h p
    compatible := ?_ }⟩
  intro p q _ _ f g hfg
  have he : kernelValue ν k f =ᵐ[μ] kernelValue ν k g :=
    Eventually.of_forall fun x => congrFun (kernelValue_congr ν k hfg) x
  exact (kernelLpLinear_coe μ ν k hk A B h p f).trans
    (he.trans (kernelLpLinear_coe μ ν k hk A B h q g).symm)


section Noncompact
open Spec

lemma boxKernel_measurable : Measurable boxKernel :=
  measurable_const.indicator measurableSet_Icc

lemma boxKernel_support : HasCompactSupport boxKernel := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  exact Set.indicator_of_notMem hx _

lemma boxKernel_integrable : Integrable boxKernel volume := by
  exact (integrableOn_const (C := (1 : ℝ)) (measure_Icc_lt_top : volume (Set.Icc (0 : ℝ) 1) < ∞).ne).integrable_indicator
    measurableSet_Icc

lemma boxKernel_integral : (∫ x, boxKernel x) = 1 := by
  simp [boxKernel, integral_indicator measurableSet_Icc, measureReal_def, Real.volume_Icc]

lemma boxKernel_lintegral : (∫⁻ x, ‖boxKernel x‖ₑ) = 1 := by
  have he : (fun x => ‖boxKernel x‖ₑ) = (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [boxKernel, hx]
  rw [he]
  simp [lintegral_indicator measurableSet_Icc, Real.volume_Icc]

lemma boxKernel_bounds :
    KernelBounds volume volume (fun z : ℝ × ℝ => boxKernel (z.1-z.2)) 1 1 := by
  constructor
  · exact Eventually.of_forall fun x => by
      rw [lintegral_sub_left_eq_self (fun t => ‖boxKernel t‖ₑ) x, boxKernel_lintegral]
      rfl
  · exact Eventually.of_forall fun y => by
      rw [lintegral_sub_right_eq_self (fun t => ‖boxKernel t‖ₑ) y, boxKernel_lintegral]
      rfl

private def boxInput (n : ℕ) (x : ℝ) : ℝ :=
  (Set.Icc (4 * (n : ℝ)) (4 * n + 2)).indicator (fun _ => 1) x

private lemma boxInput_measurable (n : ℕ) : Measurable (boxInput n) :=
  measurable_const.indicator measurableSet_Icc

private lemma boxInput_norm_le (n : ℕ) (x : ℝ) : ‖boxInput n x‖ ≤ 1 := by
  by_cases hx : x ∈ Set.Icc (4 * (n : ℝ)) (4 * n + 2) <;> simp [boxInput, hx]

private lemma boxInput_memLp (n : ℕ) : MemLp (boxInput n) ∞ volume :=
  memLp_top_of_bound (boxInput_measurable n).aestronglyMeasurable 1
    (Eventually.of_forall (boxInput_norm_le n))

private def boxInputLp (n : ℕ) : Lp ℝ ∞ (volume : Measure ℝ) :=
  (boxInput_memLp n).toLp (boxInput n)

private lemma boxInputLp_norm_le (n : ℕ) : ‖boxInputLp n‖ ≤ 1 := by
  rw [boxInputLp, Lp.norm_toLp]
  have hb : eLpNorm (boxInput n) ∞ volume ≤ 1 := by
    rw [eLpNorm_exponent_top (boxInput_measurable n).aestronglyMeasurable]
    simpa only [ENNReal.ofReal_one] using
      eLpNormEssSup_le_of_ae_bound (Eventually.of_forall (boxInput_norm_le n))
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hb)

/-- Each translated input has a unit-height output plateau of positive measure. -/
private lemma boxIntegral_plateau (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (4 * (n : ℝ) + 1) (4 * n + 2)) :
    kernelValue volume (fun z : ℝ × ℝ => boxKernel (z.1-z.2)) (boxInput n) x = 1 := by
  have he : (fun y => boxKernel (x-y) * boxInput n y) = (fun y => boxKernel (x-y)) := by
    funext y
    by_cases hy : x-y ∈ Set.Icc (0 : ℝ) 1
    · have hy' : y ∈ Set.Icc (4 * (n : ℝ)) (4 * n + 2) := by
        constructor <;> linarith [hy.1, hy.2, hx.1, hx.2]
      simp [boxKernel, boxInput, hy, hy']
    · simp [boxKernel, hy]
  unfold kernelValue
  rw [he, integral_sub_left_eq_self, boxKernel_integral]

/-- All other translated outputs vanish on that plateau. -/
private lemma boxIntegral_other (n m : ℕ) (hnm : n ≠ m) {x : ℝ}
    (hx : x ∈ Set.Ioo (4 * (n : ℝ) + 1) (4 * n + 2)) :
    kernelValue volume (fun z : ℝ × ℝ => boxKernel (z.1-z.2)) (boxInput m) x = 0 := by
  have he : (fun y => boxKernel (x-y) * boxInput m y) = 0 := by
    funext y
    by_cases hy : x-y ∈ Set.Icc (0 : ℝ) 1
    · have hy' : y ∉ Set.Icc (4 * (m : ℝ)) (4 * m + 2) := by
        intro hy'
        have hxm : 4 * (m : ℝ) ≤ x ∧ x ≤ 4 * m + 3 := by
          constructor <;> linarith [hy.1, hy.2, hy'.1, hy'.2]
        rcases lt_or_gt_of_ne hnm with hnm | hmn
        · have hnm' : (n : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hnm)
          linarith [hx.2]
        · have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hmn)
          linarith [hx.1]
      simp [boxInput, hy']
    · simp [boxKernel, hy]
  unfold kernelValue
  rw [he]
  simp


private lemma boxOutputs_separated
    (T : Lp ℝ ∞ (volume : Measure ℝ) →L[ℝ] Lp ℝ ∞ volume)
    (hT : ∀ f : Lp ℝ ∞ volume,
      (T f : ℝ → ℝ) =ᵐ[volume]
        kernelValue volume (fun z : ℝ × ℝ => boxKernel (z.1-z.2)) f)
    (n m : ℕ) (hnm : n ≠ m) : 1 ≤ dist (T (boxInputLp n)) (T (boxInputLp m)) := by
  have hrep (j : ℕ) : (T (boxInputLp j) : ℝ → ℝ) =ᵐ[volume]
      kernelValue volume (fun z : ℝ × ℝ => boxKernel (z.1-z.2)) (boxInput j) := by
    have he := kernelValue_congr volume (fun z : ℝ × ℝ => boxKernel (z.1-z.2))
      (boxInput_memLp j).coeFn_toLp
    exact (hT (boxInputLp j)).trans (Eventually.of_forall fun x => congrFun he x)
  have hnorm : ∀ᵐ x ∂volume,
      ‖(T (boxInputLp n) - T (boxInputLp m) : Lp ℝ ∞ volume) x‖ ≤
        ‖T (boxInputLp n) - T (boxInputLp m)‖ := by
    simpa only [Lp.norm_def, toReal_eLpNorm] using
      ae_le_lpNorm_exponent_top (Lp.memLp (T (boxInputLp n) - T (boxInputLp m)))
  have hgood : ∀ᵐ x ∂volume,
      ‖kernelValue volume (fun z : ℝ × ℝ => boxKernel (z.1-z.2)) (boxInput n) x -
        kernelValue volume (fun z : ℝ × ℝ => boxKernel (z.1-z.2)) (boxInput m) x‖ ≤
      ‖T (boxInputLp n) - T (boxInputLp m)‖ := by
    filter_upwards [hnorm, Lp.coeFn_sub (T (boxInputLp n)) (T (boxInputLp m)), hrep n, hrep m]
      with x hx hsub hn hm
    simpa only [hsub, Pi.sub_apply, hn, hm] using hx
  have hs : volume (Set.Ioo (4 * (n : ℝ) + 1) (4 * n + 2)) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  obtain ⟨x, hx, hxn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hs (ae_restrict_of_ae hgood)
  rw [dist_eq_norm]
  simpa only [boxIntegral_plateau n hx, boxIntegral_other n m hnm hx, sub_zero, norm_one] using hxn

/-- Separated translated inputs rule out compactness, using positive-measure
plateaux rather than evaluation at single points of L∞ classes. -/
private lemma boxOperator_not_compact
    (T : Lp ℝ ∞ (volume : Measure ℝ) →L[ℝ] Lp ℝ ∞ volume)
    (hT : ∀ f : Lp ℝ ∞ volume,
      (T f : ℝ → ℝ) =ᵐ[volume]
        kernelValue volume (fun z : ℝ × ℝ => boxKernel (z.1-z.2)) f) :
    ¬ IsCompactOperator T := by
  intro hc
  have hc' : IsCompactOperator T.toLinearMap := hc
  have hK := hc'.isCompact_closure_image_closedBall 1
  have hmem : ∀ n : ℕ, T (boxInputLp n) ∈
      closure (T.toLinearMap '' Metric.closedBall 0 1) := by
    intro n
    apply subset_closure
    exact ⟨boxInputLp n, by simpa only [Metric.mem_closedBall, dist_zero_right] using boxInputLp_norm_le n, rfl⟩
  obtain ⟨a, _, φ, hφ, hconv⟩ := hK.tendsto_subseq hmem
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq 1 zero_lt_one
  have hn := hN N le_rfl (N+1) (Nat.le_succ N)
  have hl := boxOutputs_separated T hT (φ N) (φ (N+1))
    (ne_of_lt (hφ (Nat.lt_succ_self N)))
  exact (not_lt_of_ge hl) hn

/-- An explicit noncompact Schur-bounded translation convolution on ℝ. -/
theorem noncompact_convolution : Spec.NoncompactConvolution := by
  have hk : Measurable (fun z : ℝ × ℝ => boxKernel (z.1-z.2)) :=
    boxKernel_measurable.comp (measurable_fst.sub measurable_snd)
  obtain ⟨F⟩ := schur_boundedness volume volume _ hk 1 1 boxKernel_bounds
  refine ⟨boxKernel_measurable, boxKernel_support, boxKernel_integrable,
    boxKernel_integral, boxKernel_bounds, F.op ∞, ?_, ?_, ?_⟩
  · intro f
    exact ⟨F.integral_exists ∞ f, F.represents ∞ f⟩
  · simpa only [schurConstant_top, NNReal.coe_one] using F.norm_le ∞
  · exact boxOperator_not_compact (F.op ∞) (F.represents ∞)

end Noncompact

end ExpandedFA.PartV.SchurLp
