import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.HeatPoissonL2
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.FourierHilbertScale
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ContDiff

namespace ExpandedFA.Models.HeatPoissonL2
open ExpandedFA.Fourier Semigroups Sobolev.FourierScale

section Multiplication
variable {d : ℕ}

/-- Bounded measurable multiplication on ordinary L² needs no smoothness. -/
lemma bounded_mul_memLp (b : Euclidean d → ℂ) (hb : Measurable b)
    {K : ℝ} (hK : ∀ ξ, ‖b ξ‖ ≤ K) (f : L2 d) :
    MemLp (fun ξ => b ξ * f ξ) 2 volume := by
  apply (Lp.memLp f).of_le_mul
    (hb.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) (c := K)
  exact Eventually.of_forall fun ξ => by
    change ‖b ξ * f ξ‖ ≤ K * ‖f ξ‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hK ξ) (norm_nonneg _)

def boundedMul (b : Euclidean d → ℂ) (hb : Measurable b)
    {K : ℝ} (hK : ∀ ξ, ‖b ξ‖ ≤ K) : L2 d →L[ℂ] L2 d :=
  LinearMap.mkContinuous
    { toFun := fun f => (bounded_mul_memLp b hb hK f).toLp (fun ξ => b ξ * f ξ)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(bounded_mul_memLp b hb hK (f+g)).coeFn_toLp,
          (bounded_mul_memLp b hb hK f).coeFn_toLp,
          (bounded_mul_memLp b hb hK g).coeFn_toLp,
          Lp.coeFn_add ((bounded_mul_memLp b hb hK f).toLp _) ((bounded_mul_memLp b hb hK g).toLp _),
          Lp.coeFn_add f g] with ξ h₀ h₁ h₂ h₃ h₄
        simp only [h₀, h₃, Pi.add_apply, h₁, h₂, h₄, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(bounded_mul_memLp b hb hK (c • f)).coeFn_toLp,
          (bounded_mul_memLp b hb hK f).coeFn_toLp,
          Lp.coeFn_smul c ((bounded_mul_memLp b hb hK f).toLp _),
          Lp.coeFn_smul c f] with ξ h₀ h₁ h₂ h₃
        simp only [h₀, h₂, Pi.smul_apply, h₁, h₃, smul_eq_mul, RingHom.id_apply]
        ring }
    K (by
      intro f
      change ‖(bounded_mul_memLp b hb hK f).toLp (fun ξ => b ξ * f ξ)‖ ≤ K * ‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(bounded_mul_memLp b hb hK f).coeFn_toLp] with ξ hξ
      rw [hξ, norm_mul]
      exact mul_le_mul_of_nonneg_right (hK ξ) (norm_nonneg _))

lemma boundedMul_coe (b : Euclidean d → ℂ) (hb : Measurable b)
    {K : ℝ} (hK : ∀ ξ, ‖b ξ‖ ≤ K) (f : L2 d) :
    boundedMul b hb hK f =ᵐ[volume] fun ξ => b ξ * f ξ :=
  (bounded_mul_memLp b hb hK f).coeFn_toLp

lemma boundedMul_norm_le (b : Euclidean d → ℂ) (hb : Measurable b)
    {K : ℝ} (hK : ∀ ξ, ‖b ξ‖ ≤ K) (f : L2 d) :
    ‖boundedMul b hb hK f‖ ≤ K * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedMul_coe b hb hK f] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_mul_of_nonneg_right (hK ξ) (norm_nonneg _)

lemma l2_norm_sq_integral (f : L2 d) : ‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ) f f
  have hi := L2.integrable_inner (𝕜 := ℂ) f f
  have hh := congrArg (RCLike.re : ℂ → ℝ) h
  rw [← integral_re hi] at hh
  simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] using hh

variable (a : Euclidean d → ℝ) (ha : Measurable a) (ha0 : ∀ ξ, 0 ≤ a ξ)

def decaySymbol (t : ℝ≥0) (ξ : Euclidean d) : ℂ := Real.exp (-(t : ℝ) * a ξ)

lemma decaySymbol_measurable (ha : Measurable a) (t : ℝ≥0) : Measurable (decaySymbol a t) :=
  Complex.measurable_ofReal.comp ((measurable_const.mul ha).exp)

lemma decaySymbol_norm (ha0 : ∀ ξ, 0 ≤ a ξ) (t : ℝ≥0) (ξ : Euclidean d) : ‖decaySymbol a t ξ‖ ≤ 1 := by
  rw [decaySymbol, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg) (ha0 ξ))

def decayMultiplier (t : ℝ≥0) : L2 d →L[ℂ] L2 d :=
  boundedMul (decaySymbol a t) (decaySymbol_measurable a ha t) (decaySymbol_norm a ha0 t)

lemma decayMultiplier_coe (t : ℝ≥0) (f : L2 d) :
    decayMultiplier a ha ha0 t f =ᵐ[volume] fun ξ => decaySymbol a t ξ * f ξ :=
  boundedMul_coe _ _ _ _

lemma decayMultiplier_contract (t : ℝ≥0) (f : L2 d) :
    ‖decayMultiplier a ha ha0 t f‖ ≤ ‖f‖ := by
  simpa only [decayMultiplier, one_mul] using boundedMul_norm_le (decaySymbol a t)
    (decaySymbol_measurable a ha t) (decaySymbol_norm a ha0 t) f

lemma decayMultiplier_zero : decayMultiplier a ha ha0 0 = ContinuousLinearMap.id ℂ (L2 d) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [decayMultiplier_coe a ha ha0 0 f] with ξ hξ
  simpa [decaySymbol] using hξ

lemma decayMultiplier_add (t s : ℝ≥0) :
    decayMultiplier a ha ha0 (t+s) =
      (decayMultiplier a ha ha0 t).comp (decayMultiplier a ha ha0 s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [decayMultiplier_coe a ha ha0 (t+s) f,
    decayMultiplier_coe a ha ha0 t (decayMultiplier a ha ha0 s f),
    decayMultiplier_coe a ha ha0 s f] with ξ h₀ h₁ h₂
  simp only [ContinuousLinearMap.comp_apply]
  rw [h₀, h₁, h₂]
  simp only [decaySymbol, NNReal.coe_add, neg_add, add_mul, Real.exp_add, Complex.ofReal_mul]
  ring

lemma decayMultiplier_strong_zero (f : L2 d) :
    Tendsto (fun h : ℝ => decayMultiplier a ha ha0 h.toNNReal f) (𝓝[>] 0) (𝓝 f) := by
  let F := fun h : ℝ => decayMultiplier a ha ha0 h.toNNReal f
  have hcoe (h : ℝ) := decayMultiplier_coe a ha ha0 h.toNNReal f
  -- First prove convergence for the explicit representatives by integration.
  have hs : Tendsto (fun h : ℝ => ∫ ξ, ‖decaySymbol a h.toNNReal ξ * f ξ - f ξ‖ ^ 2)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    have hbound : MemLp (fun ξ => 2 * ‖f ξ‖) 2 volume := (Lp.memLp f).norm.const_mul 2
    have hh := tendsto_integral_filter_of_dominated_convergence
      (fun ξ => (2 * ‖f ξ‖) ^ 2)
      (Eventually.of_forall fun h : ℝ =>
        ((((decaySymbol_measurable a ha h.toNNReal).aestronglyMeasurable.mul
          (Lp.aestronglyMeasurable f)).sub (Lp.aestronglyMeasurable f)).norm.pow 2))
      (Eventually.of_forall fun h : ℝ => Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _)
        calc
          ‖decaySymbol a h.toNNReal ξ * f ξ - f ξ‖ ≤
              ‖decaySymbol a h.toNNReal ξ‖ * ‖f ξ‖ + ‖f ξ‖ := by
                simpa only [norm_mul] using norm_sub_le (decaySymbol a h.toNNReal ξ * f ξ) (f ξ)
          _ ≤ 2 * ‖f ξ‖ := by nlinarith [decaySymbol_norm a ha0 h.toNNReal ξ, norm_nonneg (f ξ)])
      hbound.integrable_sq
      (Eventually.of_forall fun ξ => by
        have ht : Tendsto (fun h : ℝ => (h.toNNReal : ℝ)) (𝓝[>] 0) (𝓝 0) := by
          simpa only [Function.comp_def, Real.toNNReal_zero, NNReal.coe_zero] using ((NNReal.continuous_coe.comp continuous_real_toNNReal).tendsto 0).mono_left
            (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
        have hd : Tendsto (fun h : ℝ => decaySymbol a h.toNNReal ξ) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
          simpa only [Function.comp_def, decaySymbol, ← Real.exp_eq_exp_ℝ, neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one] using
            Complex.continuous_ofReal.continuousAt.tendsto.comp ((ht.neg.mul_const (a ξ)).exp)
        simpa using ((hd.mul_const (f ξ)).sub tendsto_const_nhds).norm.pow 2)
    simpa using hh
  have he (h : ℝ) : ‖F h - f‖ ^ 2 =
      ∫ ξ, ‖decaySymbol a h.toNNReal ξ * f ξ - f ξ‖ ^ 2 := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (F h) f, hcoe h] with ξ h₁ h₂
    rw [h₁]
    change ‖F h ξ - f ξ‖ ^ 2 = _
    rw [show F h ξ = _ from h₂]
  have hsq : Tendsto (fun h => ‖F h - f‖ ^ 2) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [he] using hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using ht

/-- The frequency-side contraction semigroup. -/
def frequencySemigroup : C0Semigroup ℂ (L2 d) where
  operators := decayMultiplier a ha ha0
  at_zero := decayMultiplier_zero a ha ha0
  add_time := decayMultiplier_add a ha ha0
  strong_zero := decayMultiplier_strong_zero a ha ha0

/-- Conjugation back to the spatial L² space. -/
def multiplierSemigroup : C0Semigroup ℂ (L2 d) where
  operators t := (l2Fourier d).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((decayMultiplier a ha ha0 t).comp (l2Fourier d).toContinuousLinearEquiv.toContinuousLinearMap)
  at_zero := by
    ext f
    simp [decayMultiplier_zero]
  add_time t s := by
    ext f
    simp [decayMultiplier_add]
  strong_zero f := by
    have h := (l2Fourier d).symm.continuous.continuousAt.tendsto.comp
      (decayMultiplier_strong_zero a ha ha0 (l2Fourier d f))
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.symm_apply_apply] using h

lemma multiplierSemigroup_fourier (t : ℝ≥0) (f : L2 d) :
    (l2Fourier d ((multiplierSemigroup a ha ha0).operators t f) : Euclidean d → ℂ) =ᵐ[volume]
      fun ξ => (Real.exp (-(t : ℝ) * a ξ) : ℂ) * l2Fourier d f ξ := by
  simpa [multiplierSemigroup, decaySymbol] using
    decayMultiplier_coe a ha ha0 t (l2Fourier d f)

lemma multiplierSemigroup_contract (t : ℝ≥0) (f : L2 d) :
    ‖(multiplierSemigroup a ha ha0).operators t f‖ ≤ ‖f‖ := by
  simpa [multiplierSemigroup] using decayMultiplier_contract a ha ha0 t (l2Fourier d f)

/-- The scalar difference quotient, using the same nonnegative-time extension
as the canonical semigroup generator. -/
def quotientSymbol (a : Euclidean d → ℝ) (h : ℝ) (ξ : Euclidean d) : ℂ :=
  (h : ℂ)⁻¹ * (decaySymbol a h.toNNReal ξ - 1)

lemma real_decay_quotient_bound (r h : ℝ) (hr : 0 ≤ r) (hh : 0 < h) :
    |h⁻¹ * (Real.exp (-h * r) - 1)| ≤ r := by
  have hu : Real.exp (-h * r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hl := Real.add_one_le_exp (-h * r)
  rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hh.le) (sub_nonpos.mpr hu))]
  apply (le_of_mul_le_mul_left ?_ hh)
  calc
    h * -(h⁻¹ * (Real.exp (-h * r) - 1)) = 1 - Real.exp (-h * r) := by
      field_simp; ring
    _ ≤ h * r := by linarith

lemma quotientSymbol_norm (ha0 : ∀ ξ, 0 ≤ a ξ) (h : ℝ) (hh : 0 < h) (ξ : Euclidean d) :
    ‖quotientSymbol a h ξ‖ ≤ a ξ := by
  have he : quotientSymbol a h ξ =
      ((h⁻¹ * (Real.exp (-h * a ξ) - 1) : ℝ) : ℂ) := by
    simp only [quotientSymbol, decaySymbol, Real.toNNReal_of_nonneg hh.le,
      Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact real_decay_quotient_bound (a ξ) h (ha0 ξ) hh

lemma quotientSymbol_tendsto (ξ : Euclidean d) :
    Tendsto (fun h : ℝ => quotientSymbol a h ξ) (𝓝[>] 0) (𝓝 (-(a ξ : ℂ))) := by
  have hd : HasDerivAt (fun h : ℝ => Real.exp (-h * a ξ)) (-a ξ) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).neg.mul_const (a ξ)).exp) using 1 <;> simp
  have hl := Complex.continuous_ofReal.continuousAt.tendsto.comp hd.tendsto_slope_zero_right
  rw [Complex.ofReal_neg] at hl
  apply Tendsto.congr' ?_ hl
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [Function.comp_def, zero_add, neg_zero, zero_mul, Real.exp_zero,
    smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub,
    Complex.ofReal_one, quotientSymbol, decaySymbol, Real.toNNReal_of_nonneg hh.le]
  rfl

lemma frequency_quotient_coe (h : ℝ) (f : L2 d) :
    C0SemigroupSpec.differenceQuotientValue (frequencySemigroup a ha ha0) h f =ᵐ[volume]
      fun ξ => quotientSymbol a h ξ * f ξ := by
  let v := decayMultiplier a ha ha0 h.toNNReal f - f
  have hs := Lp.coeFn_smul ((h : ℂ)⁻¹) v
  have hv := Lp.coeFn_sub (decayMultiplier a ha ha0 h.toNNReal f) f
  filter_upwards [hs, hv, decayMultiplier_coe a ha ha0 h.toNNReal f] with ξ h₁ h₂ h₃
  change (((h : ℂ)⁻¹) • v) ξ = _
  rw [h₁]
  change (h : ℂ)⁻¹ * v ξ = _
  rw [show v ξ = _ from h₂]
  change (h : ℂ)⁻¹ * (decayMultiplier a ha ha0 h.toNNReal f ξ - f ξ) = _
  rw [h₃]
  simp only [quotientSymbol]
  ring

/-- A representative-wise dominated-convergence criterion. Equalities are
required separately at each index, avoiding an uncountable intersection of
null exceptional sets. -/
lemma l2_tendsto_of_representatives {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → L2 d) (u : ι → Euclidean d → ℂ) (g : L2 d)
    (hrep : ∀ i, (F i : Euclidean d → ℂ) =ᵐ[volume] u i)
    (B : Euclidean d → ℝ) (hB : MemLp B 2 volume)
    (hb : ∀ᶠ i in l, ∀ᵐ ξ, ‖u i ξ - g ξ‖ ≤ B ξ)
    (hl : ∀ᵐ ξ, Tendsto (fun i => u i ξ) l (𝓝 (g ξ))) :
    Tendsto F l (𝓝 g) := by
  have hs : Tendsto (fun i => ∫ ξ, ‖u i ξ - g ξ‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (fun ξ => B ξ ^ 2)
      (Eventually.of_forall fun i =>
        ((((Lp.aestronglyMeasurable (F i)).congr (hrep i)).sub
          (Lp.aestronglyMeasurable g)).norm.pow 2))
      (hb.mono fun i hi => hi.mono fun ξ hξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hξ 2)
      hB.integrable_sq
      (hl.mono fun ξ hξ => by simpa using
        (hξ.sub tendsto_const_nhds).norm.pow 2)
    simpa using hh
  have he (i : ι) : ‖F i - g‖ ^ 2 = ∫ ξ, ‖u i ξ - g ξ‖ ^ 2 := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (F i) g, hrep i] with ξ h₁ h₂
    rw [h₁]
    change ‖F i ξ - g ξ‖ ^ 2 = _
    rw [h₂]
  have hsq : Tendsto (fun i => ‖F i - g‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    simpa only [he] using hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using ht

lemma frequency_generator_limit_of_ae (f g : L2 d)
    (hg : (g : Euclidean d → ℂ) =ᵐ[volume] fun ξ => -(a ξ : ℂ) * f ξ) :
    C0SemigroupSpec.hasGeneratorLimitValue (frequencySemigroup a ha ha0) f g := by
  apply l2_tendsto_of_representatives
    (fun h => C0SemigroupSpec.differenceQuotientValue (frequencySemigroup a ha ha0) h f)
    (fun h ξ => quotientSymbol a h ξ * f ξ) g
    (fun h => frequency_quotient_coe a ha ha0 h f)
    (fun ξ => 2 * ‖g ξ‖) ((Lp.memLp g).norm.const_mul 2)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    filter_upwards [hg] with ξ hξ
    have hn : ‖g ξ‖ = a ξ * ‖f ξ‖ := by
      rw [hξ, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 ξ)]
    calc
      ‖quotientSymbol a h ξ * f ξ - g ξ‖ ≤
          ‖quotientSymbol a h ξ‖ * ‖f ξ‖ + ‖g ξ‖ := by
            simpa only [norm_mul] using norm_sub_le (quotientSymbol a h ξ * f ξ) (g ξ)
      _ ≤ 2 * ‖g ξ‖ := by
        nlinarith [quotientSymbol_norm a ha0 h hh ξ, norm_nonneg (f ξ)]
  · filter_upwards [hg] with ξ hξ
    rw [hξ]
    exact (quotientSymbol_tendsto a ξ).mul_const (f ξ)

/-- Necessity uses an almost-everywhere convergent subsequence of the L²
quotients; the pointwise derivative then identifies every graph value. -/
lemma frequency_generator_ae_of_limit (f g : L2 d)
    (hg : C0SemigroupSpec.hasGeneratorLimitValue (frequencySemigroup a ha ha0) f g) :
    (g : Euclidean d → ℂ) =ᵐ[volume] fun ξ => -(a ξ : ℂ) * f ξ := by
  obtain ⟨hs, hst, hsl⟩ := (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae'
  have hrep : ∀ᵐ ξ, ∀ n : ℕ,
      C0SemigroupSpec.differenceQuotientValue (frequencySemigroup a ha ha0) (hs n) f ξ =
        quotientSymbol a (hs n) ξ * f ξ := by
    exact ae_all_iff.mpr (fun n => frequency_quotient_coe a ha ha0 (hs n) f)
  filter_upwards [hsl, hrep] with ξ hξ hξrep
  have hpoint := ((quotientSymbol_tendsto a ξ).mul_const (f ξ)).comp hst
  have hother : Tendsto (fun n => quotientSymbol a (hs n) ξ * f ξ) atTop (𝓝 (g ξ)) := by
    simpa only [hξrep] using hξ
  exact tendsto_nhds_unique hother hpoint

lemma frequency_generator_graph (f g : L2 d) :
    (f,g) ∈ (C0SemigroupSpec.generatorValue (frequencySemigroup a ha ha0)).graph ↔
      (g : Euclidean d → ℂ) =ᵐ[volume] fun ξ => -(a ξ : ℂ) * f ξ := by
  rw [mem_generator_graph_iff]
  exact ⟨frequency_generator_ae_of_limit a ha ha0 f g,
    frequency_generator_limit_of_ae a ha ha0 f g⟩

lemma fourier_differenceQuotient (h : ℝ) (f : L2 d) :
    l2Fourier d (C0SemigroupSpec.differenceQuotientValue (multiplierSemigroup a ha ha0) h f) =
      C0SemigroupSpec.differenceQuotientValue (frequencySemigroup a ha ha0) h (l2Fourier d f) := by
  change l2Fourier d ((h : ℂ)⁻¹ •
    ((l2Fourier d).symm (decayMultiplier a ha ha0 h.toNNReal (l2Fourier d f)) - f)) = _
  simp only [map_smul, map_sub, LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma multiplierSemigroup_generator_graph (f g : L2 d) :
    (f,g) ∈ (C0SemigroupSpec.generatorValue (multiplierSemigroup a ha ha0)).graph ↔
      MultiplierGraph a f g := by
  rw [mem_generator_graph_iff]
  change Tendsto _ _ _ ↔ _
  have hiff : C0SemigroupSpec.hasGeneratorLimitValue (multiplierSemigroup a ha ha0) f g ↔
      C0SemigroupSpec.hasGeneratorLimitValue (frequencySemigroup a ha ha0)
        (l2Fourier d f) (l2Fourier d g) := by
    constructor
    · intro h
      have hh := (l2Fourier d).continuous.continuousAt.tendsto.comp h
      simpa only [C0SemigroupSpec.hasGeneratorLimitValue, Function.comp_def, fourier_differenceQuotient] using hh
    · intro h
      have hh := (l2Fourier d).symm.continuous.continuousAt.tendsto.comp h
      have he (h : ℝ) := congrArg (l2Fourier d).symm (fourier_differenceQuotient a ha ha0 h f)
      simp only [LinearIsometryEquiv.symm_apply_apply] at he
      simpa only [C0SemigroupSpec.hasGeneratorLimitValue, Function.comp_def, ← he, LinearIsometryEquiv.symm_apply_apply] using hh
  exact hiff.trans ⟨frequency_generator_ae_of_limit a ha ha0 (l2Fourier d f) (l2Fourier d g),
    frequency_generator_limit_of_ae a ha ha0 (l2Fourier d f) (l2Fourier d g)⟩

lemma multiplierSemigroup_generator_domain (f : L2 d) :
    f ∈ (C0SemigroupSpec.generatorValue (multiplierSemigroup a ha ha0)).domain ↔
      MemLp (fun ξ => (a ξ : ℂ) * l2Fourier d f ξ) 2 volume := by
  rw [LinearPMap.mem_domain_iff]
  simp_rw [multiplierSemigroup_generator_graph]
  constructor
  · rintro ⟨g, hg⟩
    apply (memLp_congr_ae (g := fun ξ => (a ξ : ℂ) * l2Fourier d f ξ) ?_).mp (Lp.memLp (l2Fourier d g)).neg
    filter_upwards [hg] with ξ hξ
    simp only [Pi.neg_apply, hξ, neg_mul, neg_neg]
  · intro hf
    let v : L2 d := hf.toLp (fun ξ => (a ξ : ℂ) * l2Fourier d f ξ)
    refine ⟨(l2Fourier d).symm (-v), ?_⟩
    change (l2Fourier d ((l2Fourier d).symm (-v)) : Euclidean d → ℂ) =ᵐ[volume] _
    rw [LinearIsometryEquiv.apply_symm_apply]
    filter_upwards [Lp.coeFn_neg v, hf.coeFn_toLp] with ξ h₁ h₂
    rw [h₁]
    change -(v ξ) = _
    rw [show v ξ = _ from h₂]
    ring

/-- Exact comparison with the existing distributional Sobolev interface. -/
lemma fourierDensity_unique {T : Tempered ℂ d} {f g : Euclidean d → ℂ}
    (hf : HasFourierDensity T f) (hg : HasFourierDensity T g) : f =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf.1 hg.1
  intro ψ hψ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hc.comp_left rfl
  have hψ' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
  let φ : Schwartz ℂ d := hc'.toSchwartzMap hψ'
  have he := (hf.2 φ).2.symm.trans (hg.2 φ).2
  change (∫ ξ, (ψ ξ : ℂ) * f ξ) = ∫ ξ, (ψ ξ : ℂ) * g ξ at he
  simpa only [Complex.real_smul] using he

lemma inSobolev_iff_weighted (s : ℝ) (f : L2 d) :
    InSobolev s f ↔ MemLp (fun ξ => complexWeight s ξ * l2Fourier d f ξ) 2 volume := by
  constructor
  · rintro ⟨v, hv, hm⟩
    apply (memLp_congr_ae (g := fun ξ => complexWeight s ξ * l2Fourier d f ξ) ?_).mp hm
    exact (fourierDensity_unique hv (regularL2_hasFourierDensity f)).mono fun ξ hξ => by dsimp only; rw [hξ]
  · intro h
    exact ⟨l2Fourier d f, regularL2_hasFourierDensity f, h⟩

lemma heatRate_nonneg (ξ : Euclidean d) : 0 ≤ heatRate ξ := by unfold heatRate; positivity

lemma poissonRate_nonneg (ξ : Euclidean d) : 0 ≤ poissonRate ξ := by unfold poissonRate; positivity

lemma heatRate_measurable : Measurable (heatRate : Euclidean d → ℝ) := by
  unfold heatRate
  fun_prop

lemma poissonRate_measurable : Measurable (poissonRate : Euclidean d → ℝ) := by
  unfold poissonRate
  fun_prop

lemma poissonRate_sq (ξ : Euclidean d) : poissonRate ξ ^ 2 = heatRate ξ := by
  unfold poissonRate heatRate
  ring

lemma complexWeight_two (ξ : Euclidean d) : complexWeight 2 ξ = 1 + (heatRate ξ : ℂ) := by
  simp only [complexWeight, weight, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one,
    frequencyWeight, heatRate, Complex.ofReal_add, Complex.ofReal_one]

lemma heat_memLp_iff (f : L2 d) :
    MemLp (fun ξ => (heatRate ξ : ℂ) * l2Fourier d f ξ) 2 volume ↔ InSobolev 2 f := by
  rw [inSobolev_iff_weighted]
  constructor
  · intro h
    convert (Lp.memLp (l2Fourier d f)).add h using 1
    funext ξ
    simp [complexWeight_two, add_mul]
  · intro h
    convert h.sub (Lp.memLp (l2Fourier d f)) using 1
    funext ξ
    simp [complexWeight_two, add_mul]

lemma weight_one_sq (ξ : Euclidean d) : weight 1 ξ ^ 2 = 1 + poissonRate ξ ^ 2 := by
  rw [weight_sq, Real.rpow_one, poissonRate_sq]
  rfl

lemma poissonRate_le_weight (ξ : Euclidean d) : poissonRate ξ ≤ weight 1 ξ := by
  have hp := weight_pos (1 : ℝ) ξ
  have hr := poissonRate_nonneg ξ
  nlinarith [weight_one_sq ξ]

lemma weight_le_one_add_poissonRate (ξ : Euclidean d) : weight 1 ξ ≤ 1 + poissonRate ξ := by
  have hp := weight_pos (1 : ℝ) ξ
  have hr := poissonRate_nonneg ξ
  nlinarith [weight_one_sq ξ]

lemma poisson_memLp_iff (f : L2 d) :
    MemLp (fun ξ => (poissonRate ξ : ℂ) * l2Fourier d f ξ) 2 volume ↔ InSobolev 1 f := by
  rw [inSobolev_iff_weighted]
  have hm : AEStronglyMeasurable (fun ξ => (poissonRate ξ : ℂ) * l2Fourier d f ξ) volume :=
    (Complex.measurable_ofReal.comp poissonRate_measurable).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable _)
  have hw : AEStronglyMeasurable (fun ξ => complexWeight 1 ξ * l2Fourier d f ξ) volume :=
    (complexWeight_hasTemperateGrowth (1 : ℝ)).1.continuous.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable _)
  have hnorm (ξ : Euclidean d) : ‖(poissonRate ξ : ℂ)‖ = poissonRate ξ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (poissonRate_nonneg ξ)]
  have hwnorm (ξ : Euclidean d) : ‖complexWeight 1 ξ‖ = weight 1 ξ := by
    rw [complexWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos _ _)]
  constructor
  · intro h
    have hh := (Lp.memLp (l2Fourier d f)).norm.add h.norm
    apply hh.of_le hw
    exact Eventually.of_forall fun ξ => by
      change ‖complexWeight 1 ξ * l2Fourier d f ξ‖ ≤
        ‖‖l2Fourier d f ξ‖ + ‖(poissonRate ξ : ℂ) * l2Fourier d f ξ‖‖
      rw [norm_mul, hwnorm, norm_mul, hnorm, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg (poissonRate_nonneg _) (norm_nonneg _)))]
      nlinarith [weight_le_one_add_poissonRate ξ, norm_nonneg (l2Fourier d f ξ)]
  · intro h
    apply h.of_le hm
    exact Eventually.of_forall fun ξ => by
      change ‖(poissonRate ξ : ℂ) * l2Fourier d f ξ‖ ≤ ‖complexWeight 1 ξ * l2Fourier d f ξ‖
      rw [norm_mul, norm_mul, hnorm, hwnorm]
      exact mul_le_mul_of_nonneg_right (poissonRate_le_weight ξ) (norm_nonneg _)


/-- A quantitative bound sufficient for every power domain. -/
lemma power_decay_bound (t r : ℝ) (ht : 0 < t) (hr : 0 ≤ r) (n : ℕ) :
    r ^ n * Real.exp (-t * r) ≤ (n.factorial : ℝ) / t ^ n := by
  have hf : (0 : ℝ) < n.factorial := by positivity
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (t * r) (mul_nonneg ht.le hr) n)
  have h' : (t * r) ^ n * Real.exp (-t * r) ≤ (n.factorial : ℝ) := by
    calc
      _ ≤ (Real.exp (t * r) * (n.factorial : ℝ)) * Real.exp (-t * r) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = (n.factorial : ℝ) := by
        rw [mul_right_comm, ← Real.exp_add]
        simp
  apply (le_div_iff₀ (pow_pos ht n)).mpr
  simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using h'

def smoothingSymbol (a : Euclidean d → ℝ) (t : ℝ≥0) (n : ℕ) (ξ : Euclidean d) : ℂ :=
  (-(a ξ : ℂ)) ^ n * decaySymbol a t ξ

lemma smoothingSymbol_measurable (ha : Measurable a) (t : ℝ≥0) (n : ℕ) :
    Measurable (smoothingSymbol a t n) :=
  (((Complex.measurable_ofReal.comp ha).neg).pow_const n).mul
    (decaySymbol_measurable a ha t)

lemma smoothingSymbol_norm (ha0 : ∀ ξ, 0 ≤ a ξ) (t : ℝ≥0) (ht : 0 < t)
    (n : ℕ) (ξ : Euclidean d) :
    ‖smoothingSymbol a t n ξ‖ ≤ (n.factorial : ℝ) / (t : ℝ) ^ n := by
  rw [smoothingSymbol, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ha0 ξ), decaySymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact power_decay_bound (t : ℝ) (a ξ) (show (0 : ℝ) < t from ht) (ha0 ξ) n

/-- Instant smoothing into the actual iterated canonical generator domains. -/
lemma multiplierSemigroup_smoothing (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (f : L2 d) :
    InPowerDomain (C0SemigroupSpec.generatorValue (multiplierSemigroup a ha ha0)) n
      ((multiplierSemigroup a ha ha0).operators t f) := by
  let b (k : ℕ) : L2 d := boundedMul (smoothingSymbol a t k)
    (smoothingSymbol_measurable a ha t k) (smoothingSymbol_norm a ha0 t ht k) (l2Fourier d f)
  let g (k : ℕ) : L2 d := (l2Fourier d).symm (b k)
  have hcoe (k : ℕ) : (l2Fourier d (g k) : Euclidean d → ℂ) =ᵐ[volume]
      fun ξ => smoothingSymbol a t k ξ * l2Fourier d f ξ := by
    simpa only [g, LinearIsometryEquiv.apply_symm_apply] using boundedMul_coe
      (smoothingSymbol a t k) (smoothingSymbol_measurable a ha t k)
        (smoothingSymbol_norm a ha0 t ht k) (l2Fourier d f)
  have hstep (k : ℕ) : (g k, g (k+1)) ∈
      (C0SemigroupSpec.generatorValue (multiplierSemigroup a ha ha0)).graph := by
    rw [multiplierSemigroup_generator_graph]
    filter_upwards [hcoe k, hcoe (k+1)] with ξ h₀ h₁
    change l2Fourier d (g (k+1)) ξ = -(a ξ : ℂ) * l2Fourier d (g k) ξ
    rw [h₀, h₁]
    simp only [smoothingSymbol, pow_succ]
    ring
  have hp : ∀ m k, InPowerDomain
      (C0SemigroupSpec.generatorValue (multiplierSemigroup a ha ha0)) m (g k) := by
    intro m
    induction m with
    | zero => intro k; trivial
    | succ m hm => intro k; exact ⟨g (k+1), hstep k, hm (k+1)⟩
  have hzero : g 0 = (multiplierSemigroup a ha ha0).operators t f := by
    apply (l2Fourier d).injective
    apply Lp.ext
    filter_upwards [hcoe 0, multiplierSemigroup_fourier a ha ha0 t f] with ξ h₀ h₁
    rw [h₀, h₁]
    simp only [smoothingSymbol, pow_zero, one_mul, decaySymbol]
  rw [← hzero]
  exact hp n 0

/-- Both constructions use the same maximal-domain and smoothing argument. -/
lemma semigroupResult_of_domain (ha : Measurable a) (ha0 : ∀ ξ, 0 ≤ a ξ) (s : ℝ)
    (hdom : ∀ f : L2 d, MemLp (fun ξ => (a ξ : ℂ) * l2Fourier d f ξ) 2 volume ↔
      InSobolev s f) : SemigroupResult d a s := by
  refine ⟨multiplierSemigroup a ha ha0, multiplierSemigroup_fourier a ha ha0,
    multiplierSemigroup_contract a ha ha0, multiplierSemigroup_generator_graph a ha ha0, ?_,
    multiplierSemigroup_smoothing a ha ha0⟩
  intro f
  exact (multiplierSemigroup_generator_domain a ha ha0 f).trans (hdom f)

/-- The heat multiplier generates precisely Δ with domain H². -/
theorem heat : Spec.Heat := by
  intro d
  exact semigroupResult_of_domain heatRate heatRate_measurable heatRate_nonneg 2 heat_memLp_iff

/-- The Poisson multiplier generates precisely -√(-Δ) with domain H¹. -/
theorem poisson : Spec.Poisson := by
  intro d
  exact semigroupResult_of_domain poissonRate poissonRate_measurable poissonRate_nonneg 1 poisson_memLp_iff

lemma regular_multiplier_of_ae (p : Euclidean d → ℂ) (hp : p.HasTemperateGrowth)
    (f g : L2 d) (h : (g : Euclidean d → ℂ) =ᵐ[volume] fun ξ => p ξ * f ξ) :
    Lp.toTemperedDistribution g =
      TemperedDistribution.smulLeftCLM ℂ p (Lp.toTemperedDistribution f) := by
  ext φ
  rw [Lp.toTemperedDistribution_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h] with ξ hξ
  change φ ξ * g ξ = _
  rw [hξ]
  simp only [SchwartzMap.smulLeftCLM_apply_apply hp, smul_eq_mul]
  ring

lemma heatSymbol_growth : (fun ξ : Euclidean d => -(heatRate ξ : ℂ)).HasTemperateGrowth := by
  unfold heatRate
  fun_prop

lemma distribution_laplacian_symbol (f : L2 d) :
    LineDeriv.laplacianCLM ℂ (Euclidean d) (TemperedDistribution (Euclidean d) ℂ) (Lp.toTemperedDistribution f) =
      TemperedDistribution.fourierMultiplierCLM ℂ (fun ξ => -(heatRate ξ : ℂ))
        (Lp.toTemperedDistribution f) := by
  rw [TemperedDistribution.laplacianCLM_apply,
    TemperedDistribution.laplacian_eq_fourierMultiplierCLM]
  have he : (fun ξ : Euclidean d => -(heatRate ξ : ℂ)) =
      (-(2 * (Real.pi : ℂ)) ^ 2) • (fun ξ : Euclidean d => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
    funext ξ
    simp only [heatRate, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_ofNat]
    ring
  rw [he, TemperedDistribution.fourierMultiplierCLM_smul (by fun_prop)]
  simp only [smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  congr 1
  simp only [map_neg, map_pow, map_mul, map_ofNat]
  rfl


lemma fourier_distribution_laplacian (f : L2 d) :
    temperedFourier (LineDeriv.laplacianCLM ℂ (Euclidean d) (TemperedDistribution (Euclidean d) ℂ)
      (Lp.toTemperedDistribution f)) =
      TemperedDistribution.smulLeftCLM ℂ (fun ξ => -(heatRate ξ : ℂ))
        (Lp.toTemperedDistribution (l2Fourier d f)) := by
  rw [distribution_laplacian_symbol, TemperedDistribution.fourierMultiplierCLM_apply]
  change (FourierTransform.fourier : TemperedDistribution (Euclidean d) ℂ → TemperedDistribution (Euclidean d) ℂ) _ = _
  rw [FourierTransform.fourier_fourierInv_eq, Lp.fourier_toTemperedDistribution_eq]
  rfl

/-- A semantic bridge to the actual distributional differential operator. -/
theorem laplacian_identification : Spec.LaplacianIdentification := by
  intro d f g
  constructor
  · intro h
    apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution (Euclidean d) ℂ)).injective
    change temperedFourier (Lp.toTemperedDistribution g) =
      temperedFourier (LineDeriv.laplacianCLM ℂ (Euclidean d) (TemperedDistribution (Euclidean d) ℂ)
        (Lp.toTemperedDistribution f))
    rw [fourier_distribution_laplacian]
    change FourierTransform.fourier (Lp.toTemperedDistribution g) = _
    rw [Lp.fourier_toTemperedDistribution_eq]
    exact regular_multiplier_of_ae _ heatSymbol_growth (l2Fourier d f) (l2Fourier d g) h
  · intro h
    have he := congrArg temperedFourier h
    change temperedFourier (Lp.toTemperedDistribution g) =
      temperedFourier (LineDeriv.laplacianCLM ℂ (Euclidean d) (TemperedDistribution (Euclidean d) ℂ)
        (Lp.toTemperedDistribution f)) at he
    rw [fourier_distribution_laplacian] at he
    change FourierTransform.fourier (Lp.toTemperedDistribution g) = _ at he
    rw [Lp.fourier_toTemperedDistribution_eq] at he
    exact regularMultiplier_ae_eq _ heatSymbol_growth (l2Fourier d f) (l2Fourier d g) he

lemma poissonRate_eq_sqrt (ξ : Euclidean d) : poissonRate ξ = Real.sqrt (heatRate ξ) := by
  rw [← poissonRate_sq]
  exact (Real.sqrt_sq (poissonRate_nonneg ξ)).symm

theorem squareRoot_identification : Spec.SquareRootIdentification := by
  intro d f g
  simp only [NegativeSqrtLaplacianGraph, MultiplierGraph, ← poissonRate_eq_sqrt]


/-- The square of the square-root graph has precisely the Laplacian domain. -/
theorem squareRoot_square : Spec.SquareRootSquare := by
  intro d f h
  rw [← laplacian_identification]
  have hs (ξ : Euclidean d) : (poissonRate ξ : ℂ) ^ 2 = (heatRate ξ : ℂ) := by
    exact_mod_cast poissonRate_sq ξ
  constructor
  · rintro ⟨g, hfg, hgh⟩
    change (l2Fourier d (-h) : Euclidean d → ℂ) =ᵐ[volume] _
    rw [map_neg]
    filter_upwards [Lp.coeFn_neg (l2Fourier d h), hfg, hgh] with ξ h₀ h₁ h₂
    change (-l2Fourier d h) ξ = _
    rw [h₀]
    change -(l2Fourier d h ξ) = _
    rw [h₂, h₁, ← hs]
    ring
  · intro hfh
    have hh : (l2Fourier d h : Euclidean d → ℂ) =ᵐ[volume]
        fun ξ => (heatRate ξ : ℂ) * l2Fourier d f ξ := by
      have hfh' : ((-l2Fourier d h : L2 d) : Euclidean d → ℂ) =ᵐ[volume]
          fun ξ => -(heatRate ξ : ℂ) * l2Fourier d f ξ := by
        simpa only [MultiplierGraph, map_neg] using hfh
      filter_upwards [Lp.coeFn_neg (l2Fourier d h), hfh'] with ξ h₀ h₁
      change (-l2Fourier d h) ξ = _ at h₁
      rw [h₀] at h₁
      change -(l2Fourier d h ξ) = _ at h₁
      simpa only [neg_neg, neg_mul] using congrArg Neg.neg h₁
    have hm : MemLp (fun ξ => (poissonRate ξ : ℂ) * l2Fourier d f ξ) 2 volume := by
      have hint := (Lp.memLp (l2Fourier d f)).norm.add (Lp.memLp (l2Fourier d h)).norm
      apply hint.of_le
        ((Complex.measurable_ofReal.comp poissonRate_measurable).aestronglyMeasurable.mul
          (Lp.aestronglyMeasurable _))
      filter_upwards [hh] with ξ hξ
      change ‖(poissonRate ξ : ℂ) * l2Fourier d f ξ‖ ≤ ‖‖l2Fourier d f ξ‖ + ‖l2Fourier d h ξ‖‖
      have ha : poissonRate ξ ≤ 1 + heatRate ξ := by
        nlinarith [sq_nonneg (poissonRate ξ - 1), poissonRate_sq ξ]
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
        hξ, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (poissonRate_nonneg ξ), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (heatRate_nonneg ξ)]
      nlinarith [norm_nonneg (l2Fourier d f ξ)]
    let v : L2 d := hm.neg.toLp (fun ξ => -((poissonRate ξ : ℂ) * l2Fourier d f ξ))
    let g : L2 d := (l2Fourier d).symm v
    have hg : (l2Fourier d g : Euclidean d → ℂ) =ᵐ[volume]
        fun ξ => -(poissonRate ξ : ℂ) * l2Fourier d f ξ := by
      rw [show l2Fourier d g = v from (l2Fourier d).apply_symm_apply v]
      exact hm.neg.coeFn_toLp |>.trans (Eventually.of_forall fun ξ => by simp only [Pi.neg_apply, neg_mul])
    refine ⟨g, hg, ?_⟩
    filter_upwards [hh, hg] with ξ h₀ h₁
    change l2Fourier d h ξ = -(poissonRate ξ : ℂ) * l2Fourier d g ξ
    rw [h₀, h₁, ← hs]
    ring

end Multiplication

section RealForm
variable {d : ℕ}

def realPartL2 (d : ℕ) : L2 d →L[ℝ] RealL2 d :=
  Complex.reCLM.compLpL 2 volume

lemma complexifyL2_coe (f : RealL2 d) :
    complexifyL2 d f =ᵐ[volume] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLp f

lemma realPartL2_coe (f : L2 d) :
    realPartL2 d f =ᵐ[volume] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLp f

@[simp] lemma realPartL2_complexify (f : RealL2 d) :
    realPartL2 d (complexifyL2 d f) = f := by
  apply Lp.ext
  filter_upwards [realPartL2_coe (complexifyL2 d f), complexifyL2_coe f] with x hx hy
  simp only [hx, hy, Complex.ofReal_re]

lemma complexifyL2_injective : Function.Injective (complexifyL2 d) :=
  Function.LeftInverse.injective realPartL2_complexify

theorem real_l2_embedding : Spec.RealL2Embedding := by
  intro d f
  refine ⟨complexifyL2_coe f, le_antisymm ?_ ?_⟩
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [complexifyL2_coe f] with x hx
    simp [hx]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [complexifyL2_coe f] with x hx
    simp [hx]

lemma integral_complexifyL2 (f : RealL2 d) (φ : Euclidean d → ℝ) :
    (∫ x, (φ x : ℂ) * complexifyL2 d f x) = ((∫ x, φ x * f x : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [complexifyL2_coe f] with x hx
  simp [hx]

lemma regular_complexify_real (f : RealL2 d) (φ : Schwartz ℝ d) :
    Lp.toTemperedDistribution (complexifyL2 d f) (complexifySchwartz φ) =
      ((∫ x, φ x * f x : ℝ) : ℂ) := by
  rw [Lp.toTemperedDistribution_apply]
  exact integral_complexifyL2 f φ

theorem real_regular_distribution : Spec.RealRegularDistribution := by
  intro d f
  constructor
  · intro φ
    change (Lp.toTemperedDistribution (complexifyL2 d f) (complexifySchwartz φ)).re = _
    rw [regular_complexify_real]
    rfl
  · apply complexify_restrict_of_real
    intro φ
    rw [regular_complexify_real]
    rfl

/-- Reality of an L² regular distribution detects reality of its density. -/
lemma regular_real_iff (v : L2 d) :
    (∀ φ : Schwartz ℝ d, (Lp.toTemperedDistribution v (complexifySchwartz φ)).im = 0) ↔
      complexifyL2 d (realPartL2 d v) = v := by
  constructor
  · intro hv
    have him : (fun x => (v x).im) =ᵐ[volume] (fun _ => (0 : ℝ)) := by
      apply ae_eq_of_integral_contDiff_smul_eq
        ((Lp.memLp v).im.locallyIntegrable (by norm_num))
        (fun x => locallyIntegrable_zero x)
      intro ψ hψ hc
      let φ : Schwartz ℝ d := hc.toSchwartzMap hψ
      have hi := hv φ
      rw [Lp.toTemperedDistribution_apply] at hi
      have hint : Integrable (fun x => (complexifySchwartz φ) x * v x) :=
        ((complexifySchwartz φ).memLp 2).integrable_mul (Lp.memLp v)
      change (∫ x, (complexifySchwartz φ) x * v x).im = 0 at hi
      have he := Complex.imCLM.integral_comp_comm hint
      change (∫ x, ((complexifySchwartz φ) x * v x).im) =
        (∫ x, (complexifySchwartz φ) x * v x).im at he
      rw [← he] at hi
      simpa [complexifySchwartz, Complex.mul_im, smul_eq_mul, φ] using hi
    apply Lp.ext
    filter_upwards [complexifyL2_coe (realPartL2 d v), realPartL2_coe v, him] with x hx hy hz
    rw [hx, hy]
    exact Complex.ext (by simp) (by simp [hz])
  · intro hv φ
    rw [← hv, regular_complexify_real]
    rfl

lemma realization_fourier_zero (v : L2 d) :
    @realization d 0 (l2Fourier d v) = Lp.toTemperedDistribution v := by
  rw [realization_zero]
  exact congrArg Lp.toTemperedDistribution ((l2Fourier d).symm_apply_apply v)

lemma fourier_real_iff (v : L2 d) :
    l2Fourier d v ∈ hermitianL2 d ↔ complexifyL2 d (realPartL2 d v) = v := by
  rw [realization_real_iff (show Hs d 0 from l2Fourier d v), realization_fourier_zero]
  exact regular_real_iff v

theorem real_fourier_form : Spec.RealFourierForm := by
  intro d u
  constructor
  · intro hu
    let v := (l2Fourier d).symm u
    have hv : complexifyL2 d (realPartL2 d v) = v :=
      (fourier_real_iff v).mp (by simpa [v] using hu)
    exact ⟨realPartL2 d v, by rw [hv]; exact (l2Fourier d).apply_symm_apply u⟩
  · rintro ⟨f, rfl⟩
    apply (fourier_real_iff _).mpr
    rw [realPartL2_complexify]

theorem real_sobolev_identification : Spec.RealSobolevIdentification := by
  intro d s f
  constructor
  · unfold RealInSobolev realMemHs InSobolev
    rw [(real_regular_distribution d f).2]
  · exact (real_realization_image d s (realRegularDistribution f)).symm

end RealForm

section Restriction
variable {d : ℕ}

lemma real_output_of_even_multiplier (b : Euclidean d → ℝ)
    (hb : ∀ ξ, b (-ξ) = b ξ) (f : RealL2 d) (g : L2 d)
    (hg : (l2Fourier d g : Euclidean d → ℂ) =ᵐ[volume]
      fun ξ => (b ξ : ℂ) * l2Fourier d (complexifyL2 d f) ξ) :
    complexifyL2 d (realPartL2 d g) = g := by
  apply (fourier_real_iff g).mp
  apply (hermitianL2_mem_iff_ae d _).mpr
  have hf := (hermitianL2_mem_iff_ae d _).mp
    ((real_fourier_form d _).mpr ⟨f, rfl⟩)
  filter_upwards [hg, (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae hg,
    hf] with ξ hξ hneg hfξ
  rw [hneg, hb, hfξ, hξ, star_mul]
  simp [mul_comm]

variable (T : C0Semigroup ℂ (L2 d))
    (hinv : ∀ (t : ℝ≥0) (f : RealL2 d),
      complexifyL2 d (realPartL2 d (T.operators t (complexifyL2 d f))) =
        T.operators t (complexifyL2 d f))

/-- The actual real semigroup, obtained with the pointwise real-part retraction. -/
def restrictRealSemigroup : C0Semigroup ℝ (RealL2 d) where
  operators t := (realPartL2 d).comp
    (((T.operators t).restrictScalars ℝ).comp (complexifyL2 d))
  at_zero := by
    apply ContinuousLinearMap.ext
    intro f
    change realPartL2 d (T.operators 0 (complexifyL2 d f)) = f
    rw [T.at_zero]
    exact realPartL2_complexify f
  add_time t s := by
    apply ContinuousLinearMap.ext
    intro f
    change realPartL2 d (T.operators (t+s) (complexifyL2 d f)) =
      realPartL2 d (T.operators t (complexifyL2 d
        (realPartL2 d (T.operators s (complexifyL2 d f)))))
    rw [hinv, T.add_time]
    rfl
  strong_zero f := by
    change Tendsto (fun h : ℝ => realPartL2 d (T.operators h.toNNReal (complexifyL2 d f))) _ _
    have h := (realPartL2 d).continuous.continuousAt.tendsto.comp
      (T.strong_zero (complexifyL2 d f))
    simpa only [Function.comp_def, realPartL2_complexify] using h

lemma restrictRealSemigroup_intertwine (t : ℝ≥0) (f : RealL2 d) :
    complexifyL2 d ((restrictRealSemigroup T hinv).operators t f) =
      T.operators t (complexifyL2 d f) := hinv t f

lemma restrictRealSemigroup_quotient (h : ℝ) (f : RealL2 d) :
    complexifyL2 d (C0SemigroupSpec.differenceQuotientValue
      (restrictRealSemigroup T hinv) h f) =
      C0SemigroupSpec.differenceQuotientValue T h (complexifyL2 d f) := by
  change complexifyL2 d (h⁻¹ •
    ((restrictRealSemigroup T hinv).operators h.toNNReal f - f)) =
      (algebraMap ℝ ℂ h)⁻¹ • (T.operators h.toNNReal (complexifyL2 d f) - complexifyL2 d f)
  rw [map_smul, map_sub, restrictRealSemigroup_intertwine]
  change h⁻¹ • (T.operators h.toNNReal (complexifyL2 d f) - complexifyL2 d f) =
    (h : ℂ)⁻¹ • (T.operators h.toNNReal (complexifyL2 d f) - complexifyL2 d f)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv]
  rfl

lemma restrictRealSemigroup_realPart_quotient (h : ℝ) (f : RealL2 d) :
    realPartL2 d (C0SemigroupSpec.differenceQuotientValue T h (complexifyL2 d f)) =
      C0SemigroupSpec.differenceQuotientValue (restrictRealSemigroup T hinv) h f := by
  rw [← restrictRealSemigroup_quotient T hinv, realPartL2_complexify]

lemma restrictRealSemigroup_graph (f g : RealL2 d) :
    (f,g) ∈ (C0SemigroupSpec.generatorValue (restrictRealSemigroup T hinv)).graph ↔
      (complexifyL2 d f, complexifyL2 d g) ∈ (C0SemigroupSpec.generatorValue T).graph := by
  rw [mem_generator_graph_iff, mem_generator_graph_iff]
  constructor
  · intro h
    have hh := (complexifyL2 d).continuous.continuousAt.tendsto.comp h
    simpa only [C0SemigroupSpec.hasGeneratorLimitValue, Function.comp_def,
      restrictRealSemigroup_quotient] using hh
  · intro h
    have hh := (realPartL2 d).continuous.continuousAt.tendsto.comp h
    simpa only [C0SemigroupSpec.hasGeneratorLimitValue, Function.comp_def,
      restrictRealSemigroup_realPart_quotient T hinv, realPartL2_complexify] using hh

/-- Every generator value at a real input is real: this follows from the
norm limit of real difference quotients, including necessity of the domain. -/
lemma restrictRealSemigroup_generator_output (f : RealL2 d) (g : L2 d)
    (hg : (complexifyL2 d f,g) ∈ (C0SemigroupSpec.generatorValue T).graph) :
    complexifyL2 d (realPartL2 d g) = g ∧
      (f, realPartL2 d g) ∈
        (C0SemigroupSpec.generatorValue (restrictRealSemigroup T hinv)).graph := by
  have hl := (mem_generator_graph_iff T _ _).mp hg
  have hr : (f, realPartL2 d g) ∈
      (C0SemigroupSpec.generatorValue (restrictRealSemigroup T hinv)).graph := by
    rw [mem_generator_graph_iff]
    have hh := (realPartL2 d).continuous.continuousAt.tendsto.comp hl
    simpa only [C0SemigroupSpec.hasGeneratorLimitValue, Function.comp_def,
      restrictRealSemigroup_realPart_quotient T hinv] using hh
  refine ⟨?_, hr⟩
  have he := (restrictRealSemigroup_graph T hinv f (realPartL2 d g)).mp hr
  exact tendsto_nhds_unique ((mem_generator_graph_iff T _ _).mp he) hl

lemma restrictRealSemigroup_power (n : ℕ) (f : RealL2 d) :
    RealInPowerDomain (C0SemigroupSpec.generatorValue (restrictRealSemigroup T hinv)) n f ↔
      InPowerDomain (C0SemigroupSpec.generatorValue T) n (complexifyL2 d f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    constructor
    · rintro ⟨g, hg, hn⟩
      exact ⟨complexifyL2 d g, (restrictRealSemigroup_graph T hinv f g).mp hg, (ih g).mp hn⟩
    · rintro ⟨g, hg, hn⟩
      obtain ⟨he, hr⟩ := restrictRealSemigroup_generator_output T hinv f g hg
      exact ⟨realPartL2 d g, hr, (ih _).mpr (by rwa [he])⟩

lemma restrictionResult_of_even (a : Euclidean d → ℝ) (ha : ∀ ξ, a (-ξ) = a ξ) :
    RealRestrictionResult d a := by
  intro T hT
  have hinv : ∀ (t : ℝ≥0) (f : RealL2 d),
      complexifyL2 d (realPartL2 d (T.operators t (complexifyL2 d f))) =
        T.operators t (complexifyL2 d f) := by
    intro t f
    exact real_output_of_even_multiplier (fun ξ => Real.exp (-(t : ℝ) * a ξ))
      (fun ξ => by rw [ha]) f _ (hT t _)
  exact ⟨fun t f => ⟨realPartL2 d (T.operators t (complexifyL2 d f)), hinv t f⟩,
    restrictRealSemigroup T hinv, restrictRealSemigroup_intertwine T hinv,
    restrictRealSemigroup_graph T hinv, restrictRealSemigroup_power T hinv⟩

theorem real_restriction : Spec.RealRestriction := by
  intro d
  exact ⟨restrictionResult_of_even heatRate (by intro ξ; simp [heatRate]),
    restrictionResult_of_even poissonRate (by intro ξ; simp [poissonRate])⟩

end Restriction

section RealResults
variable {d : ℕ}

lemma realSemigroupResult_of_complex (a : Euclidean d → ℝ) (s : ℝ)
    (h : SemigroupResult d a s) (hres : RealRestrictionResult d a) :
    RealSemigroupResult d a s := by
  obtain ⟨T, hformula, hcontract, hgraph, hdomain, hsmooth⟩ := h
  obtain ⟨_, R, hact, hgen, hpower⟩ := hres T hformula
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · intro t f
    rw [hact]
    exact hformula t _
  · intro t f
    rw [← (real_l2_embedding d (R.operators t f)).2, hact]
    exact (hcontract t _).trans_eq (real_l2_embedding d f).2
  · intro f g
    exact (hgen f g).trans (hgraph _ _)
  · intro f
    rw [(real_sobolev_identification d s f).1, ← hdomain]
    rw [LinearPMap.mem_domain_iff, LinearPMap.mem_domain_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨complexifyL2 d g, (hgen f g).mp hg⟩
    · rintro ⟨g, hg⟩
      have hp : InPowerDomain (C0SemigroupSpec.generatorValue T) 1 (complexifyL2 d f) :=
        ⟨g, hg, trivial⟩
      obtain ⟨v, hv, _⟩ := (hpower 1 f).mpr hp
      exact ⟨v, hv⟩
  · intro t ht n f
    apply (hpower n _).mpr
    rw [hact]
    exact hsmooth t ht n _

theorem real_heat : Spec.RealHeat := by
  intro d
  exact realSemigroupResult_of_complex heatRate 2 (heat d) (real_restriction d).1

theorem real_poisson : Spec.RealPoisson := by
  intro d
  exact realSemigroupResult_of_complex poissonRate 1 (poisson d) (real_restriction d).2

theorem real_squareRoot_identification : Spec.RealSquareRootIdentification := by
  intro d f g
  exact squareRoot_identification d (complexifyL2 d f) (complexifyL2 d g)

/-- Complex-linear tempered distributions are determined by real tests. -/
lemma tempered_eq_of_real_tests {S T : Tempered ℂ d}
    (h : ∀ φ : Schwartz ℝ d, S (complexifySchwartz φ) = T (complexifySchwartz φ)) : S = T := by
  ext φ
  rw [schwartz_decompose φ]
  simp only [map_add, map_smul, h]

lemma laplacian_complexifySchwartz (φ : Schwartz ℝ d) :
    LineDeriv.laplacianCLM ℂ (Euclidean d) (Schwartz ℂ d) (complexifySchwartz φ) =
      complexifySchwartz (LineDeriv.laplacianCLM ℝ (Euclidean d) (Schwartz ℝ d) φ) := by
  rw [SchwartzMap.laplacianCLM_eq, SchwartzMap.laplacianCLM_eq]
  ext x
  simp only [SchwartzMap.laplacian_apply]
  change Laplacian.laplacian (Complex.ofRealCLM ∘ φ) x =
    Complex.ofRealCLM ((Laplacian.laplacian φ) x)
  rw [SchwartzMap.laplacian_apply]
  exact (φ.smooth 2).contDiffAt.laplacian_CLM_comp_left

lemma regular_complexify_apply (f : RealL2 d) (φ : Schwartz ℝ d) :
    Lp.toTemperedDistribution (complexifyL2 d f) (complexifySchwartz φ) =
      (realRegularDistribution f φ : ℂ) := by
  rw [← (real_regular_distribution d f).2]
  exact complexifyTempered_apply_complexifySchwartz _ _

lemma real_laplacian_graph_iff (f g : RealL2 d) :
    RealLaplacianGraph f g ↔ LaplacianGraph (complexifyL2 d f) (complexifyL2 d g) := by
  have he (φ : Schwartz ℝ d) :
      (LineDeriv.laplacianCLM ℂ (Euclidean d) (TemperedDistribution (Euclidean d) ℂ)
        (Lp.toTemperedDistribution (complexifyL2 d f))) (complexifySchwartz φ) =
      (realRegularDistribution f
        (LineDeriv.laplacianCLM ℝ (Euclidean d) (Schwartz ℝ d) φ) : ℂ) := by
    rw [TemperedDistribution.laplacianCLM_apply, TemperedDistribution.laplacian_apply_apply]
    rw [← SchwartzMap.laplacianCLM_eq ℂ, laplacian_complexifySchwartz,
      regular_complexify_apply]
  constructor
  · intro h
    apply tempered_eq_of_real_tests
    intro φ
    rw [regular_complexify_apply, he, h φ]
  · intro h φ
    have hh := congrArg (fun S : Tempered ℂ d => S (complexifySchwartz φ)) h
    rw [regular_complexify_apply, he] at hh
    exact_mod_cast hh

theorem real_laplacian_identification : Spec.RealLaplacianIdentification := by
  intro d f g
  exact (laplacian_identification d (complexifyL2 d f) (complexifyL2 d g)).trans
    (real_laplacian_graph_iff f g).symm

/-- The intermediate negative square-root value is real, since its symbol
is real and even. Thus the full squared graph restricts without losing domain. -/
theorem real_squareRoot_square : Spec.RealSquareRootSquare := by
  intro d f h
  rw [real_laplacian_graph_iff]
  rw [map_neg]
  rw [← squareRoot_square]
  constructor
  · rintro ⟨g, hfg, hgh⟩
    exact ⟨complexifyL2 d g, hfg, hgh⟩
  · rintro ⟨g, hfg, hgh⟩
    have hg := real_output_of_even_multiplier (fun ξ : Euclidean d => -poissonRate ξ)
      (by intro ξ; simp [poissonRate]) f g (by
        simpa only [Complex.ofReal_neg] using (show (l2Fourier d g : Euclidean d → ℂ) =ᵐ[volume]
          fun ξ => -(poissonRate ξ : ℂ) * l2Fourier d (complexifyL2 d f) ξ from hfg))
    refine ⟨realPartL2 d g, ?_, ?_⟩
    · change MultiplierGraph poissonRate (complexifyL2 d f)
        (complexifyL2 d (realPartL2 d g))
      rwa [hg]
    · change MultiplierGraph poissonRate (complexifyL2 d (realPartL2 d g)) (complexifyL2 d h)
      rwa [hg]

end RealResults
end ExpandedFA.Models.HeatPoissonL2
