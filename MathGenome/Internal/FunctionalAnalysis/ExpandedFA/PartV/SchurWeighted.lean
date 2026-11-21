import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.SchurWeighted
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2Kernel
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.Positivity

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
universe u v
noncomputable section
namespace ExpandedFA.PartV.SchurWeighted

variable {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [RCLike 𝕜] {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]

/-- Cauchy–Schwarz for the nonnegative Lebesgue integral, in squared form. -/
lemma lintegral_cauchy_schwarz {f g : Y → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hg : AEMeasurable g ν) :
    (∫⁻ y, (f y) ^ (1/2 : ℝ) * (g y) ^ (1/2 : ℝ) ∂ν) ^ 2 ≤
      (∫⁻ y, f y ∂ν) * (∫⁻ y, g y ∂ν) := by
  have h := ENNReal.lintegral_mul_norm_pow_le hf hg
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) + 1/2 = 1)
  have hh := pow_le_pow_left' h 2
  simpa only [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show (1/2:ℝ) * (2:ℕ) = 1 by norm_num, ENNReal.rpow_one] using hh

/-- Weighted section Cauchy–Schwarz without any global hypothesis on the weight. -/
lemma weighted_section_bound {c v w : Y → ℝ≥0∞}
    (hc : AEMeasurable c ν) (hv : AEMeasurable v ν) (hw : Measurable w)
    (hwpos : ∀ᵐ y ∂ν, 0 < w y ∧ w y < ∞) :
    (∫⁻ y, c y * v y ∂ν) ^ 2 ≤
      (∫⁻ y, c y * w y ∂ν) * (∫⁻ y, c y * v y ^ 2 / w y ∂ν) := by
  have h := lintegral_cauchy_schwarz (hc.mul hw.aemeasurable)
    ((hc.mul (hv.pow_const 2)).div hw.aemeasurable)
  have heq : (fun y => (c y * w y) ^ (1/2:ℝ) *
      (c y * v y ^ 2 / w y) ^ (1/2:ℝ)) =ᵐ[ν] fun y => c y * v y := by
    filter_upwards [hwpos] with y hy
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
    have hp : (c y * w y) * (c y * v y ^ 2 / w y) = (c y * v y) ^ 2 := by
      calc
        _ = (c y * v y) ^ 2 * (w y * (w y)⁻¹) := by
          simp only [div_eq_mul_inv, pow_two]
          ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel hy.1.ne' hy.2.ne, mul_one]
    rw [hp, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, Pi.div_apply] at h
  rwa [lintegral_congr_ae heq] at h

/-- Tonelli moves the weighted energy to the column bound. -/
lemma weighted_energy_bound (k : X × Y → 𝕜) (a : X → ℝ≥0∞) (b : Y → ℝ≥0∞)
    (A B : ℝ≥0) (h : SchurWeightedSpec.Hypotheses μ ν k a b A B)
    (f : Y → 𝕜) (hf : MemLp f 2 ν) :
    (∫⁻ x, a x * (∫⁻ y, ‖k (x,y)‖ₑ * ‖f y‖ₑ ^ 2 / b y ∂ν) ∂μ) ≤
      B * (∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν) := by
  have hm : AEMeasurable
      (fun p : X × Y => ‖k p‖ₑ * a p.1 * (‖f p.2‖ₑ ^ 2 / b p.2)) (μ.prod ν) :=
    (h.kernel_measurable.enorm.mul (h.a_measurable.comp measurable_fst)).aemeasurable.mul
      ((hf.aestronglyMeasurable.enorm.pow_const 2).div h.b_measurable.aemeasurable).comp_snd
  calc
    _ = ∫⁻ x, ∫⁻ y, ‖k (x,y)‖ₑ * a x * (‖f y‖ₑ ^ 2 / b y) ∂ν ∂μ := by
      apply lintegral_congr
      intro x
      have hs : AEMeasurable (fun y => ‖k (x,y)‖ₑ * ‖f y‖ₑ ^ 2 / b y) ν :=
        (((h.kernel_measurable.comp measurable_prodMk_left).enorm.aemeasurable.mul
          (hf.aestronglyMeasurable.enorm.pow_const 2)).div h.b_measurable.aemeasurable)
      calc
        _ = ∫⁻ y, a x * (‖k (x,y)‖ₑ * ‖f y‖ₑ ^ 2 / b y) ∂ν :=
          (lintegral_const_mul'' _ hs).symm
        _ = _ := by
          apply lintegral_congr
          intro y
          simp only [div_eq_mul_inv]
          ac_rfl
    _ = ∫⁻ y, ∫⁻ x, ‖k (x,y)‖ₑ * a x * (‖f y‖ₑ ^ 2 / b y) ∂μ ∂ν :=
      lintegral_lintegral_swap hm
    _ = ∫⁻ y, (∫⁻ x, ‖k (x,y)‖ₑ * a x ∂μ) * (‖f y‖ₑ ^ 2 / b y) ∂ν := by
      apply lintegral_congr
      intro y
      exact lintegral_mul_const _
        ((h.kernel_measurable.comp measurable_prodMk_right).enorm.mul h.a_measurable)
    _ ≤ ∫⁻ y, (B:ℝ≥0∞) * ‖f y‖ₑ ^ 2 ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [h.column_bound, h.b_positive_finite] with y hy hb
      calc
        _ ≤ ((B:ℝ≥0∞) * b y) * (‖f y‖ₑ ^ 2 / b y) := mul_le_mul' hy le_rfl
        _ = _ := by
          rw [div_eq_mul_inv]
          calc
            _ = ((B:ℝ≥0∞) * ‖f y‖ₑ ^ 2) * (b y * (b y)⁻¹) := by ac_rfl
            _ = _ := by rw [ENNReal.mul_inv_cancel hb.1.ne' hb.2.ne, mul_one]
    _ = _ := lintegral_const_mul'' _ (hf.aestronglyMeasurable.enorm.pow_const 2)

/-- The square of the absolute section integral has the required global bound.
This simultaneously controls convergence of the sections and the output. -/
lemma absolute_integral_sq_bound (k : X × Y → 𝕜) (a : X → ℝ≥0∞)
    (b : Y → ℝ≥0∞) (A B : ℝ≥0)
    (h : SchurWeightedSpec.Hypotheses μ ν k a b A B)
    (f : Y → 𝕜) (hf : MemLp f 2 ν) :
    (∫⁻ x, (∫⁻ y, ‖k (x,y) * f y‖ₑ ∂ν) ^ 2 ∂μ) ≤
      ((A:ℝ≥0∞) * B) * (∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν) := by
  have hs : ∀ᵐ x ∂μ, (∫⁻ y, ‖k (x,y) * f y‖ₑ ∂ν) ^ 2 ≤
      (A:ℝ≥0∞) * (a x * (∫⁻ y, ‖k (x,y)‖ₑ * ‖f y‖ₑ ^ 2 / b y ∂ν)) := by
    filter_upwards [h.row_bound] with x hx
    have hc : AEMeasurable (fun y => ‖k (x,y)‖ₑ) ν :=
      (h.kernel_measurable.comp measurable_prodMk_left).enorm.aemeasurable
    have hb := weighted_section_bound hc hf.aestronglyMeasurable.enorm
      h.b_measurable h.b_positive_finite
    simp only [enorm_mul]
    exact hb.trans ((mul_le_mul' hx le_rfl).trans_eq (mul_assoc _ _ _))
  have henergy : AEMeasurable (fun x => a x *
      (∫⁻ y, ‖k (x,y)‖ₑ * ‖f y‖ₑ ^ 2 / b y ∂ν)) μ :=
    h.a_measurable.aemeasurable.mul
      (((h.kernel_measurable.enorm.aemeasurable.mul
        (hf.aestronglyMeasurable.enorm.pow_const 2).comp_snd).div
          (h.b_measurable.comp measurable_snd).aemeasurable).lintegral_prod_right')
  calc
    _ ≤ ∫⁻ x, (A:ℝ≥0∞) * (a x *
        (∫⁻ y, ‖k (x,y)‖ₑ * ‖f y‖ₑ ^ 2 / b y ∂ν)) ∂μ := lintegral_mono_ae hs
    _ = (A:ℝ≥0∞) * (∫⁻ x, a x *
        (∫⁻ y, ‖k (x,y)‖ₑ * ‖f y‖ₑ ^ 2 / b y ∂ν) ∂μ) :=
      lintegral_const_mul'' _ henergy
    _ ≤ (A:ℝ≥0∞) * ((B:ℝ≥0∞) * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν) :=
      mul_le_mul' le_rfl (weighted_energy_bound k a b A B h f hf)
    _ = _ := (mul_assoc _ _ _).symm

lemma input_sq_finite (f : Y → 𝕜) (hf : MemLp f 2 ν) :
    (∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν) < ∞ := by
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by simp : (2:ℝ≥0∞) ≠ ∞) hf.eLpNorm_lt_top

lemma absolute_integral_sq_finite (k : X × Y → 𝕜) (a : X → ℝ≥0∞)
    (b : Y → ℝ≥0∞) (A B : ℝ≥0)
    (h : SchurWeightedSpec.Hypotheses μ ν k a b A B)
    (f : Y → 𝕜) (hf : MemLp f 2 ν) :
    (∫⁻ x, (∫⁻ y, ‖k (x,y) * f y‖ₑ ∂ν) ^ 2 ∂μ) < ∞ :=
  (absolute_integral_sq_bound k a b A B h f hf).trans_lt
    (ENNReal.mul_lt_top (by finiteness) (input_sq_finite f hf))

lemma sections_integrable (k : X × Y → 𝕜) (a : X → ℝ≥0∞)
    (b : Y → ℝ≥0∞) (A B : ℝ≥0)
    (h : SchurWeightedSpec.Hypotheses μ ν k a b A B)
    (f : Y → 𝕜) (hf : MemLp f 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν := by
  have hm : AEStronglyMeasurable (fun p : X × Y => k p * f p.2) (μ.prod ν) :=
    h.kernel_measurable.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd
  have hfinite := ae_lt_top' (hm.enorm.lintegral_prod_right'.pow_const 2)
    (absolute_integral_sq_finite k a b A B h f hf).ne
  filter_upwards [hfinite, hm.prodMk_left] with x hx hmx
  refine ⟨hmx, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  by_contra hn
  have heq : (∫⁻ y, ‖k (x,y) * f y‖ₑ ∂ν) = ∞ :=
    top_unique (not_lt.mp hn)
  change (∫⁻ y, ‖k (x,y) * f y‖ₑ ∂ν) ^ (2:ℕ) < ∞ at hx
  rw [heq] at hx
  simpa using hx

lemma output_measurable (k : X × Y → 𝕜) (hk : Measurable k)
    (f : Y → 𝕜) (hf : MemLp f 2 ν) :
    AEStronglyMeasurable (fun x => ∫ y, k (x,y) * f y ∂ν) μ :=
  (hk.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).integral_prod_right'

lemma output_memLp (k : X × Y → 𝕜) (a : X → ℝ≥0∞)
    (b : Y → ℝ≥0∞) (A B : ℝ≥0)
    (h : SchurWeightedSpec.Hypotheses μ ν k a b A B)
    (f : Y → 𝕜) (hf : MemLp f 2 ν) :
    MemLp (fun x => ∫ y, k (x,y) * f y ∂ν) 2 μ := by
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2:ℝ≥0∞) ≠ 0) (by simp : (2:ℝ≥0∞) ≠ ∞)
    (output_measurable k h.kernel_measurable f hf)).mpr
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact (lintegral_mono fun x => pow_le_pow_left' (enorm_integral_le_lintegral_enorm _) 2).trans_lt
    (absolute_integral_sq_finite k a b A B h f hf)

lemma lintegral_sq_eq_enorm_sq {Z : Type*} [MeasurableSpace Z]
    {ρ : Measure Z} (f : Z → 𝕜) (hf : MemLp f 2 ρ) :
    (∫⁻ z, ‖f z‖ₑ ^ 2 ∂ρ) = ‖hf.toLp f‖ₑ ^ 2 := by
  rw [Lp.enorm_toLp, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2:ℝ≥0∞) ≠ 0) (by simp : (2:ℝ≥0∞) ≠ ∞) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma output_norm_bound (k : X × Y → 𝕜) (a : X → ℝ≥0∞)
    (b : Y → ℝ≥0∞) (A B : ℝ≥0)
    (h : SchurWeightedSpec.Hypotheses μ ν k a b A B)
    (f : Y → 𝕜) (hf : MemLp f 2 ν) :
    ‖(output_memLp k a b A B h f hf).toLp _‖ ≤
      Real.sqrt ((A:ℝ) * B) * ‖hf.toLp f‖ := by
  have ho := output_memLp k a b A B h f hf
  have hsq : ‖ho.toLp _‖ₑ ^ 2 ≤ ((A:ℝ≥0∞) * B) * ‖hf.toLp f‖ₑ ^ 2 := by
    calc
      _ = ∫⁻ x, ‖∫ y, k (x,y) * f y ∂ν‖ₑ ^ 2 ∂μ :=
        (lintegral_sq_eq_enorm_sq _ ho).symm
      _ ≤ ∫⁻ x, (∫⁻ y, ‖k (x,y) * f y‖ₑ ∂ν) ^ 2 ∂μ :=
        lintegral_mono fun x => pow_le_pow_left' (enorm_integral_le_lintegral_enorm _) 2
      _ ≤ ((A:ℝ≥0∞) * B) * (∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν) :=
        absolute_integral_sq_bound k a b A B h f hf
      _ = _ := by rw [lintegral_sq_eq_enorm_sq f hf]
  have hr := ENNReal.toReal_mono (by finiteness) hsq
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.coe_toReal, toReal_enorm] at hr
  have hsqrt := Real.sq_sqrt (mul_nonneg A.coe_nonneg B.coe_nonneg)
  have hnonneg := Real.sqrt_nonneg ((A:ℝ) * B)
  have htarget : (Real.sqrt ((A:ℝ) * B) * ‖hf.toLp f‖) ^ 2 =
      (A:ℝ) * B * ‖hf.toLp f‖ ^ 2 := by rw [mul_pow, hsqrt]
  nlinarith [norm_nonneg (ho.toLp (fun x => ∫ y, k (x,y) * f y ∂ν)),
    mul_nonneg hnonneg (norm_nonneg (hf.toLp f))]

section Construction

variable (k : X × Y → 𝕜) (a : X → ℝ≥0∞) (b : Y → ℝ≥0∞) (A B : ℝ≥0)
  (h : SchurWeightedSpec.Hypotheses μ ν k a b A B)

/-- The ordinary L² output class of the concrete integral. -/
def integralOutput (f : Lp 𝕜 2 ν) : Lp 𝕜 2 μ :=
  (output_memLp k a b A B h f (Lp.memLp f)).toLp _

lemma integralOutput_ae (f : Lp 𝕜 2 ν) :
    (integralOutput k a b A B h f : X → 𝕜) =ᵐ[μ]
      fun x => ∫ y, k (x,y) * f y ∂ν :=
  MemLp.coeFn_toLp _

lemma integralOutput_norm (f : Lp 𝕜 2 ν) :
    ‖integralOutput k a b A B h f‖ ≤ Real.sqrt ((A:ℝ) * B) * ‖f‖ := by
  simpa only [integralOutput, Lp.toLp_coeFn] using
    output_norm_bound k a b A B h f (Lp.memLp f)

/-- Sectionwise linearity descends to the a.e. quotient. -/
def integralLinearMap : Lp 𝕜 2 ν →ₗ[𝕜] Lp 𝕜 2 μ where
  toFun := integralOutput k a b A B h
  map_add' u v := by
    apply Lp.ext
    filter_upwards [integralOutput_ae k a b A B h (u + v), integralOutput_ae k a b A B h u,
      integralOutput_ae k a b A B h v,
      Lp.coeFn_add (integralOutput k a b A B h u) (integralOutput k a b A B h v),
      sections_integrable k a b A B h u (Lp.memLp u),
      sections_integrable k a b A B h v (Lp.memLp v)] with x huv hu hv hout hiu hiv
    rw [huv, hout, Pi.add_apply, hu, hv]
    calc
      _ = ∫ y, (k (x,y) * u y + k (x,y) * v y) ∂ν := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add u v] with y hy
        rw [hy, Pi.add_apply, mul_add]
      _ = _ := integral_add hiu hiv
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [integralOutput_ae k a b A B h (c • u), integralOutput_ae k a b A B h u,
      Lp.coeFn_smul c (integralOutput k a b A B h u)] with x hcu hu hout
    simp only [RingHom.id_apply]
    rw [hcu, hout, Pi.smul_apply, hu]
    calc
      _ = ∫ y, c • (k (x,y) * u y) ∂ν := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c u] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
      _ = _ := integral_smul c _

/-- The bounded operator constructed directly from the integral on every L² input. -/
def integralOperator : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ :=
  (integralLinearMap k a b A B h).mkContinuous (Real.sqrt ((A:ℝ) * B))
    (integralOutput_norm k a b A B h)

lemma integralOperator_ae (f : Lp 𝕜 2 ν) :
    (integralOperator k a b A B h f : X → 𝕜) =ᵐ[μ]
      fun x => ∫ y, k (x,y) * f y ∂ν :=
  integralOutput_ae k a b A B h f

lemma integralOperator_norm : ‖integralOperator k a b A B h‖ ≤ Real.sqrt ((A:ℝ) * B) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (integralOutput_norm k a b A B h)

end Construction

/-- Schur's weighted L² kernel test, including absolute section convergence
and its formula for every ordinary representative. -/
theorem weighted_schur : SchurWeightedSpec.WeightedSchur.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k a b A B h
  refine ⟨integralOperator k a b A B h, integralOperator_norm k a b A B h, ?_⟩
  intro f hf
  refine ⟨?_, output_memLp k a b A B h f hf, ?_⟩
  · filter_upwards [sections_integrable k a b A B h f hf] with x hx
    exact ⟨hx, hx.norm⟩
  · exact (integralOperator_ae k a b A B h (hf.toLp f)).trans
      (L2Kernel.kernel_representative_independence μ ν k k _ f
        Filter.EventuallyEq.rfl hf.coeFn_toLp)

/-- Ordinary a.e. quotients, for both the kernel and the input. -/
theorem representative_independence :
    SchurWeightedSpec.RepresentativeIndependence.{u,v} :=
  L2Kernel.kernel_representative_independence

end ExpandedFA.PartV.SchurWeighted
