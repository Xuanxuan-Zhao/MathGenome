import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.HardyAveragingCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.HardyAveragingLp
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.Ascoli
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal unitInterval Topology
namespace ExpandedFA.PartV.HardyAveragingCompact
open Spec

local instance : IsProbabilityMeasure μ := by
  constructor
  simp [μ, HardyAveragingLp.Spec.intervalMeasure, Real.volume_Ioo]

lemma measure_strip {δ : ℝ} (_hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ (Ioo 0 δ) = ENNReal.ofReal δ := by
  change (volume.restrict (Ioo (0 : ℝ) 1)) (Ioo 0 δ) = _
  rw [Measure.restrict_apply measurableSet_Ioo]
  rw [inter_eq_left.mpr (Ioo_subset_Ioo_right hδ1)]
  simp [Real.volume_Ioo]

/-- Finite-measure Hölder estimate on an arbitrary output set. -/
lemma restrict_norm_le {E : Type*} [NormedAddCommGroup E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : q ≤ p)
    (hpfin : p ≠ ∞) (f : Lp E p μ) (s : Set ℝ) :
    (eLpNorm (f : ℝ → E) q (μ.restrict s)).toReal ≤
      ‖f‖ * (μ s).toReal ^ (1 / q.toReal - 1 / p.toReal) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq (μ := μ.restrict s)
    ((Lp.aestronglyMeasurable f).mono_measure Measure.restrict_le_self)
  have he := eLpNorm_restrict_le (f : ℝ → E) p μ s
  have hb : eLpNorm (f : ℝ → E) q (μ.restrict s) ≤
      eLpNorm (f : ℝ → E) p μ * (μ s) ^ (1 / q.toReal - 1 / p.toReal) := by
    calc
      _ ≤ eLpNorm (f : ℝ → E) p (μ.restrict s) *
          (μ s) ^ (1 / q.toReal - 1 / p.toReal) := by
        simpa only [Measure.restrict_apply_univ] using h
      _ ≤ _ := by gcongr
  have hn : eLpNorm (f : ℝ → E) p μ *
      (μ s) ^ (1 / q.toReal - 1 / p.toReal) ≠ ∞ := by
    apply ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
    apply ENNReal.rpow_ne_top_of_nonneg
    · have hq : q.toReal ≤ p.toReal := ENNReal.toReal_mono hpfin hpq
      have hqpos := ENNReal.toReal_pos
        (ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : 1 ≤ q)))
        (ne_top_of_le_ne_top hpfin hpq)
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hqpos hq)
    · exact measure_ne_top μ s
  have ht := ENNReal.toReal_mono hn hb
  simpa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← Lp.norm_def] using ht

theorem lp_strip_estimate : Spec.LpStripEstimate := by
  intro p q _ _ hqp hpfin Q _ hQ δ hδ hδ1 f
  have hb := restrict_norm_le hqp.le hpfin (Q f) (Ioo 0 δ)
  rw [measure_strip hδ hδ1, ENNReal.toReal_ofReal hδ] at hb
  calc
    _ ≤ ‖Q f‖ * δ ^ (1 / q.toReal - 1 / p.toReal) := hb
    _ ≤ (HardyAveragingLp.Spec.conjugateExponent p * ‖f‖) *
        δ ^ (1 / q.toReal - 1 / p.toReal) := by
      gcongr
      exact (Q.le_opNorm f).trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg f))
    _ = _ := by ring

theorem continuous_strip_estimate : Spec.ContinuousStripEstimate := by
  intro q _ hqfin δ hδ hδ1 f
  let g := HardyAveragingContinuous.Spec.extension
    (HardyAveragingContinuous.Spec.operatorValue f)
  have hg : ∀ x : ℝ, ‖g x‖ ≤ ‖f‖ := by
    intro x
    exact (ContinuousMap.norm_coe_le_norm
      (HardyAveragingContinuous.Spec.operatorValue f)
      (Set.projIcc 0 1 zero_le_one x)).trans
      (HardyAveragingContinuous.hardy_norm_le |> fun h =>
        (HardyAveragingContinuous.hardy.le_opNorm f).trans
          (by simpa using mul_le_mul_of_nonneg_right h (norm_nonneg f)))
  have he := eLpNorm_le_of_ae_bound (p := q) (μ := μ.restrict (Ioo 0 δ))
    g.continuous.aestronglyMeasurable (Eventually.of_forall hg)
  simp only [Measure.restrict_apply_univ, measure_strip hδ hδ1] at he
  have hn : (ENNReal.ofReal δ) ^ q.toReal⁻¹ * ENNReal.ofReal ‖f‖ ≠ ∞ := by
    apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have ht := ENNReal.toReal_mono hn he
  simpa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hδ, ENNReal.toReal_ofReal (norm_nonneg f), one_div, g] using ht

section Primitives
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma lp_interval_integrable (f : Space p) (x : I) :
    IntervalIntegrable (f : ℝ → ℂ) volume 0 (x : ℝ) := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le x.2.1).mpr
  have hi := (Lp.memLp f).integrable (Fact.out : 1 ≤ p)
  change IntegrableOn (f : ℝ → ℂ) (Ioo 0 1) volume at hi
  exact hi.mono_set (Ioo_subset_Ioo_right x.2.2)

lemma interval_eq_set (f : ℝ → ℂ) (x y : I) (hxy : (x : ℝ) ≤ y) :
    (∫ t in (x : ℝ)..(y : ℝ), f t) = ∫ t in Ioo (x : ℝ) y, f t ∂μ := by
  change _ = ∫ t in Ioo (x : ℝ) y, f t ∂(volume.restrict (Ioo (0 : ℝ) 1))
  rw [Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (Ioo_subset_Ioo x.2.1 y.2.2),
    intervalIntegral.integral_of_le hxy, integral_Ioc_eq_integral_Ioo]

lemma interval_zero_eq_set (f : ℝ → ℂ) (x : I) :
    (∫ t in (0 : ℝ)..(x : ℝ), f t) = ∫ t in Ioo (0 : ℝ) x, f t ∂μ := by
  simpa only [Set.Icc.coe_zero] using interval_eq_set f 0 x x.2.1

omit [Fact (1 ≤ p)] in
lemma norm_setIntegral_le (f : Space p) (s : Set ℝ) :
    ‖∫ t in s, f t ∂μ‖ ≤ (eLpNorm (f : ℝ → ℂ) 1 (μ.restrict s)).toReal := by
  have hm := (Lp.aestronglyMeasurable f).mono_measure
    (Measure.restrict_le_self (s := s))
  simpa only [eLpNorm_one_eq_lintegral_enorm hm, ofReal_norm] using
    norm_integral_le_lintegral_norm (μ := μ.restrict s) (f : ℝ → ℂ)

lemma interval_norm_le (hpfin : p ≠ ∞) (f : Space p) (x y : I)
    (hxy : (x : ℝ) ≤ y) :
    ‖∫ t in (x : ℝ)..(y : ℝ), f t‖ ≤
      ‖f‖ * ((y : ℝ) - x) ^ (HardyAveragingLp.Spec.threshold p) := by
  rw [interval_eq_set _ x y hxy]
  have hm : μ (Ioo (x : ℝ) y) = ENNReal.ofReal ((y : ℝ) - x) := by
    change (volume.restrict (Ioo (0 : ℝ) 1)) _ = _
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (Ioo_subset_Ioo x.2.1 y.2.2), Real.volume_Ioo]
  have hb := restrict_norm_le (Fact.out : 1 ≤ p) hpfin f (Ioo (x : ℝ) y)
  rw [hm, ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)] at hb
  simpa [HardyAveragingLp.Spec.threshold] using (norm_setIntegral_le f _).trans hb

def primitiveFunction (f : Space p) : CSpace :=
  ⟨fun x => ∫ t in (0 : ℝ)..(x : ℝ), f t,
    (by
      have hc := intervalIntegral.continuousOn_primitive_interval'
        (lp_interval_integrable f 1) (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 1)
      have hc' : ContinuousOn (fun x : ℝ => ∫ t in (0 : ℝ)..x, f t) (Icc 0 1) := by
        simpa only [Set.Icc.coe_one, uIcc_of_le zero_le_one] using hc
      exact hc'.domRestrict)⟩

lemma primitiveFunction_bound (hpfin : p ≠ ∞) (f : Space p) :
    ‖primitiveFunction f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  have ht : 0 ≤ HardyAveragingLp.Spec.threshold p := by
    dsimp [HardyAveragingLp.Spec.threshold]
    have hp0 := ENNReal.toReal_pos
      (ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hpfin
    have hp1 : 1 ≤ p.toReal := by exact_mod_cast ENNReal.toReal_mono hpfin (Fact.out : 1 ≤ p)
    exact sub_nonneg.mpr (by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp1)
  have hx := interval_norm_le hpfin f 0 x x.2.1
  have hpow : (x : ℝ) ^ HardyAveragingLp.Spec.threshold p ≤ 1 :=
    Real.rpow_le_one x.2.1 x.2.2 ht
  change ‖∫ t in (0 : ℝ)..(x : ℝ), f t‖ ≤ ‖f‖
  simpa only [Set.Icc.coe_zero] using hx.trans (by simpa using mul_le_mul_of_nonneg_left hpow (norm_nonneg f))

/-- The primitive is linear on Lp equivalence classes and bounded into C[0,1]. -/
def primitive (hpfin : p ≠ ∞) : Space p →L[ℂ] CSpace :=
  ({ toFun := primitiveFunction
     map_add' := by
       intro f g
       ext x
       change (∫ t in (0 : ℝ)..(x : ℝ), (f + g) t) =
         (∫ t in (0 : ℝ)..(x : ℝ), f t) + ∫ t in (0 : ℝ)..(x : ℝ), g t
       simp only [interval_zero_eq_set]
       rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))]
       simpa only [Pi.add_apply] using integral_add (((Lp.memLp f).integrable (Fact.out : 1 ≤ p)).restrict)
           (((Lp.memLp g).integrable (Fact.out : 1 ≤ p)).restrict)
     map_smul' := by
       intro c f
       ext x
       change (∫ t in (0 : ℝ)..(x : ℝ), (c • f) t) = c • ∫ t in (0 : ℝ)..(x : ℝ), f t
       rw [interval_zero_eq_set, interval_zero_eq_set,
         integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f))]
       simpa only [Pi.smul_apply] using integral_smul (μ := μ.restrict (Ioo 0 (x : ℝ))) c (f : ℝ → ℂ) } :
      Space p →ₗ[ℂ] CSpace).mkContinuous 1
    (by intro f; simpa using primitiveFunction_bound hpfin f)

lemma primitive_apply (hpfin : p ≠ ∞) (f : Space p) (x : I) :
    primitive hpfin f x = ∫ t in (0 : ℝ)..(x : ℝ), f t := rfl

lemma primitive_holder (hpfin : p ≠ ∞) (f : Space p) (x y : I) :
    dist (primitive hpfin f x) (primitive hpfin f y) ≤
      ‖f‖ * dist x y ^ (HardyAveragingLp.Spec.threshold p) := by
  have hordered (x y : I) (hxy : (x : ℝ) ≤ y) :
      dist (primitive hpfin f y) (primitive hpfin f x) ≤
        ‖f‖ * dist x y ^ (HardyAveragingLp.Spec.threshold p) := by
    rw [dist_eq_norm, primitive_apply, primitive_apply,
      intervalIntegral.integral_interval_sub_left (lp_interval_integrable f y)
        (lp_interval_integrable f x)]
    have hd : dist x y = (y : ℝ) - x := by
      change dist (x : ℝ) (y : ℝ) = _
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
    rw [hd]
    exact interval_norm_le hpfin f x y hxy
  rcases le_total (x : ℝ) (y : ℝ) with hxy | hyx
  · simpa only [dist_comm] using hordered x y hxy
  · simpa only [dist_comm] using hordered y x hyx

/-- Ascoli for the primitives of the source unit ball. -/
theorem primitive_compact (hp : 1 < p) (hpfin : p ≠ ∞) :
    IsCompactOperator (primitive (p := p) hpfin) := by
  change IsCompactOperator (primitive (p := p) hpfin).toLinearMap
  rw [isCompactOperator_iff_isCompact_closure_image_closedBall
    (primitive (p := p) hpfin).toLinearMap zero_lt_one]
  apply (Ascoli.arzela_ascoli ℂ I _).mpr
  constructor
  · refine ⟨1, zero_le_one, ?_⟩
    rintro _ ⟨f, hf, rfl⟩ x
    exact (ContinuousMap.norm_coe_le_norm _ x).trans
      ((primitiveFunction_bound hpfin f).trans (by simpa [Metric.mem_closedBall, dist_zero_right] using hf))
  · intro x
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    have ht := HardyAveragingLp.threshold_pos hp hpfin
    have hc : Continuous (fun y : I => dist x y ^ HardyAveragingLp.Spec.threshold p) :=
      (continuous_const.dist continuous_id).rpow_const (fun _ => Or.inr ht.le)
    have hn : ∀ᶠ y : I in 𝓝 x, dist x y ^ HardyAveragingLp.Spec.threshold p < ε := by
      have hzero : dist x x ^ HardyAveragingLp.Spec.threshold p = 0 := by
        simp [Real.zero_rpow ht.ne']
      have he : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), r < ε := eventually_lt_nhds hε
      exact (hc.tendsto x).eventually (by rwa [hzero])
    filter_upwards [hn] with y hy g
    obtain ⟨f, hf, hfg⟩ := g.property
    have hf1 : ‖f‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hf
    rw [← hfg]
    exact ((primitive_holder hpfin f x y).trans (by
      simpa using mul_le_mul_of_nonneg_right hf1 (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist x y) _))).trans_lt hy

end Primitives
section Approximation
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
lemma lowerExponent_bound (hqp : q ≤ p) (f : Space p) :
    ‖((Lp.memLp f).mono_exponent hqp).toLp (f : ℝ → ℂ)‖ ≤ ‖f‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  exact eLpNorm_le_eLpNorm_of_exponent_le hqp

def lowerExponentValue (hqp : q ≤ p) (f : Space p) : Space q :=
  ((Lp.memLp f).mono_exponent hqp).toLp (f : ℝ → ℂ)

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
lemma lowerExponentValue_formula (hqp : q ≤ p) (f : Space p) :
    (lowerExponentValue hqp f : ℝ → ℂ) =ᵐ[μ] f :=
  ((Lp.memLp f).mono_exponent hqp).coeFn_toLp

/-- The canonical inclusion for the probability measure of the unit interval. -/
def lowerExponent (hqp : q ≤ p) : Space p →L[ℂ] Space q :=
  ({ toFun := lowerExponentValue hqp
     map_add' := by
       intro f g
       apply Lp.ext
       exact ((lowerExponentValue_formula hqp (f + g)).trans (Lp.coeFn_add f g)).trans
         ((Lp.coeFn_add (lowerExponentValue hqp f) (lowerExponentValue hqp g)).trans
           ((lowerExponentValue_formula hqp f).add (lowerExponentValue_formula hqp g))).symm
     map_smul' := by
       intro c f
       apply Lp.ext
       exact ((lowerExponentValue_formula hqp (c • f)).trans (Lp.coeFn_smul c f)).trans
         ((Lp.coeFn_smul c (lowerExponentValue hqp f)).trans
           ((lowerExponentValue_formula hqp f).const_smul c)).symm } :
      Space p →ₗ[ℂ] Space q).mkContinuous 1
    (by
      intro f
      change ‖lowerExponentValue hqp f‖ ≤ 1 * ‖f‖
      simpa only [lowerExponentValue, one_mul] using lowerExponent_bound hqp f)

lemma lowerExponent_formula (hqp : q ≤ p) (f : Space p) :
    (lowerExponent hqp f : ℝ → ℂ) =ᵐ[μ] f := lowerExponentValue_formula hqp f

/-- Replace the denominator x by max(δ,x). This continuous regularization
has the same error bound as discarding (0,δ), and factors through the compact
primitive map. -/
def clampCoefficient (δ : ℝ) (hδ : 0 < δ) : CSpace :=
  ⟨fun x => ((max δ (x : ℝ) : ℝ) : ℂ)⁻¹, by
    apply Continuous.inv₀
    · fun_prop
    · intro x
      exact_mod_cast ne_of_gt (hδ.trans_le (le_max_left _ _))⟩

def clampedAverage (hpfin : p ≠ ∞) (δ : ℝ) (hδ : 0 < δ) :
    Space p →L[ℂ] CSpace :=
  ((ContinuousLinearMap.mul ℂ CSpace) (clampCoefficient δ hδ)).comp (primitive hpfin)

lemma clampedAverage_apply (hpfin : p ≠ ∞) (δ : ℝ) (hδ : 0 < δ)
    (f : Space p) (x : I) :
    clampedAverage hpfin δ hδ f x =
      ((max δ (x : ℝ) : ℝ) : ℂ)⁻¹ * ∫ t in (0 : ℝ)..(x : ℝ), f t := rfl

lemma clampedAverage_compact (hp : 1 < p) (hpfin : p ≠ ∞) (δ : ℝ) (hδ : 0 < δ) :
    IsCompactOperator (clampedAverage (p := p) hpfin δ hδ) := by
  exact (primitive_compact hp hpfin).clm_comp
    ((ContinuousLinearMap.mul ℂ CSpace) (clampCoefficient δ hδ))

def approximant (hpfin : p ≠ ∞) (δ : ℝ) (hδ : 0 < δ) :
    Space p →L[ℂ] Space q :=
  (HardyAveragingLp.continuousEmbedding q).comp (clampedAverage hpfin δ hδ)

lemma approximant_formula (hpfin : p ≠ ∞) (δ : ℝ) (hδ : 0 < δ) (f : Space p) :
    (approximant (q := q) hpfin δ hδ f : ℝ → ℂ) =ᵐ[μ]
      fun x => ((max δ x : ℝ) : ℂ)⁻¹ * ∫ t in (0 : ℝ)..x, f t := by
  filter_upwards [HardyAveragingLp.continuousEmbedding_formula q
    (clampedAverage hpfin δ hδ f), ae_restrict_mem measurableSet_Ioo] with x hx hxm
  change ((HardyAveragingLp.continuousEmbedding q) (clampedAverage hpfin δ hδ f) : ℝ → ℂ) x = _
  rw [hx, HardyAveragingContinuous.extension_apply _ ⟨x, hxm.1.le, hxm.2.le⟩]
  rfl

lemma approximant_compact (hp : 1 < p) (hpfin : p ≠ ∞) (δ : ℝ) (hδ : 0 < δ) :
    IsCompactOperator (approximant (p := p) (q := q) hpfin δ hδ) := by
  exact (clampedAverage_compact hp hpfin δ hδ).clm_comp
    (HardyAveragingLp.continuousEmbedding q)

/-- Pointwise domination of the error by the discarded output strip. -/
lemma clamp_error_le (δ x : ℝ) (hδ : 0 < δ) (hx : 0 < x) (z : ℂ) :
    ‖z - ((max δ x : ℝ) : ℂ)⁻¹ * ((x : ℂ) * z)‖ ≤
      ‖(Ioo 0 δ).indicator (fun _ : ℝ => z) x‖ := by
  by_cases hxd : x < δ
  · rw [max_eq_left hxd.le, indicator_of_mem (show x ∈ Ioo (0 : ℝ) δ from ⟨hx, hxd⟩)]
    have hfac : 0 ≤ 1 - x / δ ∧ 1 - x / δ ≤ 1 := by
      constructor
      · exact sub_nonneg.mpr (div_le_one_of_le₀ hxd.le hδ.le)
      · exact sub_le_self _ (div_nonneg hx.le hδ.le)
    have heq : z - (δ : ℂ)⁻¹ * ((x : ℂ) * z) = ((1 - x / δ : ℝ) : ℂ) * z := by
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfac.1]
    simpa using mul_le_mul_of_nonneg_right hfac.2 (norm_nonneg z)
  · rw [max_eq_right (le_of_not_gt hxd), inv_mul_cancel_left₀ (by exact_mod_cast hx.ne'),
      sub_self, norm_zero]
    exact norm_nonneg _

lemma approximant_error_le (hqp : q ≤ p) (hpfin : p ≠ ∞)
    (Q : Space p →L[ℂ] Space p) (hQ : HardyAveragingLp.Spec.IsHardy Q)
    (δ : ℝ) (hδ : 0 < δ) (f : Space p) :
    ‖(lowerExponent hqp).comp Q f - approximant (q := q) hpfin δ hδ f‖ ≤
      (eLpNorm (Q f : ℝ → ℂ) q (μ.restrict (Ioo 0 δ))).toReal := by
  let hmem : MemLp ((Ioo 0 δ).indicator (Q f : ℝ → ℂ)) q μ :=
    ((Lp.memLp (Q f)).mono_exponent hqp).indicator measurableSet_Ioo.nullMeasurableSet
  let strip : Space q := hmem.toLp ((Ioo 0 δ).indicator (Q f : ℝ → ℂ))
  have hb : ‖(lowerExponent hqp).comp Q f - approximant (q := q) hpfin δ hδ f‖ ≤ ‖strip‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub ((lowerExponent hqp).comp Q f)
      (approximant (q := q) hpfin δ hδ f), lowerExponent_formula hqp (Q f),
      approximant_formula (q := q) hpfin δ hδ f, hmem.coeFn_toLp,
      (hQ f).2, ae_restrict_mem measurableSet_Ioo] with x hsub hinc happ hstrip hhardy hx
    rw [hsub]
    change ‖((lowerExponent hqp) (Q f) : ℝ → ℂ) x -
      (approximant (q := q) hpfin δ hδ f : ℝ → ℂ) x‖ ≤
      ‖(hmem.toLp ((Ioo 0 δ).indicator (Q f : ℝ → ℂ)) : ℝ → ℂ) x‖
    rw [hinc, happ, hstrip]
    have hid : (∫ t in (0 : ℝ)..x, f t) = (x : ℂ) * Q f x := by
      rw [hhardy]
      dsimp [HardyAveragingLp.Spec.average]
      rw [mul_inv_cancel_left₀ (by exact_mod_cast hx.1.ne')]
    rw [hid]
    exact clamp_error_le δ x hδ hx.1 (Q f x)
  have hs : ‖strip‖ = (eLpNorm (Q f : ℝ → ℂ) q (μ.restrict (Ioo 0 δ))).toReal := by
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo.nullMeasurableSet]
  exact hb.trans_eq hs

lemma approximant_opNorm_error (hqp : q < p) (hpfin : p ≠ ∞)
    (Q : Space p →L[ℂ] Space p) (hQ : HardyAveragingLp.Spec.IsHardy Q)
    (hbound : ‖Q‖ ≤ HardyAveragingLp.Spec.conjugateExponent p)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖(lowerExponent hqp.le).comp Q - approximant (q := q) hpfin δ hδ‖ ≤
      HardyAveragingLp.Spec.conjugateExponent p *
        δ ^ (1 / q.toReal - 1 / p.toReal) := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (HardyAveragingLp.conjugateExponent_pos
      ((Fact.out : 1 ≤ q).trans_lt hqp) hpfin).le (Real.rpow_nonneg hδ.le _)
  · intro f
    exact (approximant_error_le hqp.le hpfin Q hQ δ hδ f).trans
      (lp_strip_estimate p q hqp hpfin Q hQ hbound δ hδ.le hδ1 f)

lemma approximant_tendsto (hqp : q < p) (hpfin : p ≠ ∞)
    (Q : Space p →L[ℂ] Space p) (hQ : HardyAveragingLp.Spec.IsHardy Q)
    (hbound : ‖Q‖ ≤ HardyAveragingLp.Spec.conjugateExponent p) :
    Tendsto (fun n : ℕ => approximant (q := q) hpfin (1 / ((n : ℝ) + 1))
      (by positivity)) atTop (𝓝 ((lowerExponent hqp.le).comp Q)) := by
  have hqpos : 0 < q.toReal := ENNReal.toReal_pos
    (ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : 1 ≤ q)))
    (ne_top_of_lt (hqp.trans_le (le_top : p ≤ ∞)))
  have hpqreal : q.toReal < p.toReal := (ENNReal.toReal_lt_toReal
    (ne_top_of_le_ne_top hpfin hqp.le) hpfin).mpr hqp
  have hexp : 0 < 1 / q.toReal - 1 / p.toReal :=
    sub_pos.mpr (one_div_lt_one_div_of_lt hqpos hpqreal)
  have ht : Tendsto (fun n : ℕ => HardyAveragingLp.Spec.conjugateExponent p *
      (1 / ((n : ℝ) + 1)) ^ (1 / q.toReal - 1 / p.toReal)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).rpow_const_nhds_zero hexp)
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) _ ht
  intro n
  rw [dist_eq_norm, norm_sub_rev]
  exact approximant_opNorm_error hqp hpfin Q hQ hbound _ (by positivity)
    (by
      rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      linarith [Nat.cast_nonneg (α := ℝ) n])

end Approximation

/-- Hardy averaging is compact from Lp to every strictly weaker finite Lq. -/
theorem lp_compactness : Spec.LpCompactness := by
  intro p q _ _ hqp hpfin
  have hp : 1 < p := (Fact.out : 1 ≤ q).trans_lt hqp
  obtain ⟨Q, hQ, hbound⟩ :=
    HardyAveragingLp.operator_existence_of_weighted
      HardyAveragingLp.weighted_operator_existence p hp hpfin
  refine ⟨(lowerExponent hqp.le).comp Q, ?_, ?_⟩
  · intro f
    exact ⟨(hQ f).1, (lowerExponent_formula hqp.le (Q f)).trans (hQ f).2⟩
  · exact isCompactOperator_of_tendsto (approximant_tendsto hqp hpfin Q hQ hbound)
      (Eventually.of_forall (fun n => approximant_compact (q := q) hp hpfin
        (1 / ((n : ℝ) + 1)) (by positivity)))

/-- Factor C[0,1] through an Lp with p>q to retain precisely the finite Lq
norm on the target. -/
theorem continuous_compactness : Spec.ContinuousCompactness := by
  intro q _ hqfin
  let p : ℝ≥0∞ := q + 1
  have hpfin : p ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hqfin, ENNReal.one_ne_top⟩
  have hqp : q < p := ENNReal.lt_add_right hqfin (by norm_num)
  have hp1 : 1 ≤ p := (Fact.out : 1 ≤ q).trans (le_of_lt hqp)
  let : Fact (1 ≤ p) := ⟨hp1⟩
  obtain ⟨T, hT, hcompact⟩ := lp_compactness p q hqp hpfin
  refine ⟨T.comp (HardyAveragingLp.continuousEmbedding p), ?_, ?_⟩
  · intro f
    filter_upwards [(hT (HardyAveragingLp.continuousEmbedding p f)).2,
      ae_restrict_mem measurableSet_Ioo] with x hx hxm
    change (T (HardyAveragingLp.continuousEmbedding p f) : ℝ → ℂ) x = _
    rw [hx]
    dsimp only [HardyAveragingLp.Spec.average]
    rw [HardyAveragingLp.integral_congr_on_unit
      (HardyAveragingLp.continuousEmbedding_formula p f) hxm,
      HardyAveragingContinuous.extension_apply _ ⟨x, hxm.1.le, hxm.2.le⟩]
    exact (HardyAveragingContinuous.hardy_apply_pos f
      ⟨x, hxm.1.le, hxm.2.le⟩ hxm.1).symm
  · exact hcompact.comp_clm (HardyAveragingLp.continuousEmbedding p)

/-- Real compactness follows by complexification and real-part projection.
Both are bounded maps on the native Lp spaces, with the integral formula
transported explicitly. -/
theorem real_lp_compactness : Spec.RealLpCompactness := by
  intro p q _ _ hqp hpfin
  obtain ⟨T, hT, hc⟩ := lp_compactness p q hqp hpfin
  let J := Complex.ofRealCLM.compLpL p μ
  let R := Complex.reCLM.compLpL q μ
  refine ⟨R.comp ((T.restrictScalars ℝ).comp J), ?_, ?_⟩
  · intro f
    constructor
    · intro x hx
      apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1.le).mpr
      have hi := (Lp.memLp f).integrable (Fact.out : 1 ≤ p)
      change IntegrableOn (f : ℝ → ℝ) (Ioo 0 1) volume at hi
      exact hi.mono_set (Ioo_subset_Ioo_right hx.2)
    · filter_upwards [Complex.reCLM.coeFn_compLpL (T (J f)), (hT (J f)).2,
        ae_restrict_mem measurableSet_Ioo] with x hr ht hx
      change (R (T (J f)) : ℝ → ℝ) x = _
      rw [hr, ht]
      dsimp only [HardyAveragingLp.Spec.average, Complex.reCLM_apply]
      rw [HardyAveragingLp.integral_congr_on_unit
        (Complex.ofRealCLM.coeFn_compLpL f) hx]
      simp only [Complex.ofRealCLM_apply, intervalIntegral.integral_ofReal,
        ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  · exact (hc.comp_clm J).clm_comp R

/-- The real continuous-source assertion, with the same Lebesgue average. -/
theorem real_continuous_compactness : Spec.RealContinuousCompactness := by
  intro q _ hqfin
  obtain ⟨T, hT, hc⟩ := continuous_compactness q hqfin
  let J : RealCSpace →L[ℝ] CSpace := Complex.ofRealCLM.compLeftContinuous ℝ I
  let R := Complex.reCLM.compLpL q μ
  refine ⟨R.comp ((T.restrictScalars ℝ).comp J), ?_, ?_⟩
  · intro f
    filter_upwards [Complex.reCLM.coeFn_compLpL (T (J f)), hT (J f),
      ae_restrict_mem measurableSet_Ioo] with x hr ht hx
    change (R (T (J f)) : ℝ → ℝ) x = _
    rw [hr, ht, HardyAveragingContinuous.extension_apply _ ⟨x, hx.1.le, hx.2.le⟩]
    rw [show HardyAveragingContinuous.Spec.operatorValue = HardyAveragingContinuous.hardy from rfl,
      HardyAveragingContinuous.hardy_apply_pos _ _ hx.1]
    have he : (HardyAveragingContinuous.Spec.extension (J f) : ℝ → ℂ) =
        fun t => (ContinuousMap.IccExtendCM f t : ℂ) := rfl
    rw [he, intervalIntegral.integral_ofReal]
    simp only [Complex.reCLM_apply, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  · exact (hc.comp_clm J).clm_comp R

theorem real_lp_strip_estimate : Spec.RealLpStripEstimate := by
  intro p q _ _ hqp hpfin Q _ hQ δ hδ hδ1 f
  have hb := restrict_norm_le hqp.le hpfin (Q f) (Ioo 0 δ)
  rw [measure_strip hδ hδ1, ENNReal.toReal_ofReal hδ] at hb
  calc
    _ ≤ ‖Q f‖ * δ ^ (1 / q.toReal - 1 / p.toReal) := hb
    _ ≤ (HardyAveragingLp.Spec.conjugateExponent p * ‖f‖) *
        δ ^ (1 / q.toReal - 1 / p.toReal) := by
      gcongr
      exact (Q.le_opNorm f).trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg f))
    _ = _ := by ring

theorem real_continuous_strip_estimate : Spec.RealContinuousStripEstimate := by
  intro q _ _ T hT δ hδ hδ1 f
  have hb : ∀ᵐ x ∂μ, ‖T f x‖ ≤ ‖f‖ := by
    filter_upwards [hT f, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    rw [hx, norm_mul, norm_inv, Real.norm_eq_abs, abs_of_pos hxm.1]
    have hi : ‖∫ t in (0 : ℝ)..x, ContinuousMap.IccExtendCM f t‖ ≤ ‖f‖ * x := by
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := x) (C := ‖f‖) (f := fun t => ContinuousMap.IccExtendCM f t)
        (fun t _ => ContinuousMap.norm_coe_le_norm f (Set.projIcc 0 1 zero_le_one t))
      simpa only [sub_zero, abs_of_pos hxm.1] using hh
    calc
      _ ≤ x⁻¹ * (‖f‖ * x) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hxm.1.le)
      _ = ‖f‖ := by field_simp [hxm.1.ne']
  have he := eLpNorm_le_of_ae_bound (p := q) (μ := μ.restrict (Ioo 0 δ))
    ((Lp.aestronglyMeasurable (T f)).mono_measure Measure.restrict_le_self)
    (ae_restrict_of_ae hb)
  simp only [Measure.restrict_apply_univ, measure_strip hδ hδ1] at he
  have hn : (ENNReal.ofReal δ) ^ q.toReal⁻¹ * ENNReal.ofReal ‖f‖ ≠ ∞ := by
    apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have ht := ENNReal.toReal_mono hn he
  simpa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hδ, one_div] using ht

end ExpandedFA.PartV.HardyAveragingCompact
