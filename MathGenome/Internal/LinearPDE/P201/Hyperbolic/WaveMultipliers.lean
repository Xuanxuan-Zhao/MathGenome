import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.WaveMultipliers
import MathGenome.Internal.FourierSobolev.P102.U4.SchwartzRestriction
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform
namespace P201.Wave

abbrev frequency : P201Specs.Wave.frequencyType := P201Specs.Wave.frequency
abbrev cosineSymbol : P201Specs.Wave.scalarSymbolType := P201Specs.Wave.cosineSymbol
abbrev sineSymbol : P201Specs.Wave.scalarSymbolType := P201Specs.Wave.sineSymbol
abbrev cosineDerivativeSymbol : P201Specs.Wave.scalarSymbolType :=
  P201Specs.Wave.cosineDerivativeSymbol

/-- A useful globally continuous expression for the sine quotient. -/
theorem sineSymbol_eq_sinc (t w : ℝ) : sineSymbol t w = t * Real.sinc (t * w) := by
  by_cases hw : w = 0
  · simp [sineSymbol, P201Specs.Wave.sineSymbol, hw]
  by_cases ht : t = 0
  · simp [sineSymbol, P201Specs.Wave.sineSymbol, ht, hw]
  rw [Real.sinc_of_ne_zero (mul_ne_zero ht hw)]
  simp only [P201Specs.Wave.sineSymbol, ite_eq_right hw]
  field_simp

theorem scalarBounds : P201Specs.Wave.scalarBoundsStatement := by
  intro t w
  refine ⟨?_, ?_, ?_⟩
  · change |sineSymbol t w| ≤ |t|
    rw [sineSymbol_eq_sinc, abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (abs_nonneg t)).trans_eq
      (mul_one _)
  · by_cases hw : w = 0
    · simp [hw]
    · simp only [P201Specs.Wave.sineSymbol, ite_eq_right hw]
      rw [mul_div_cancel₀ _ hw]
      exact Real.abs_sin_le_one _
  · exact Real.abs_cos_le_one _

theorem scalarInitial : P201Specs.Wave.scalarInitialStatement := by
  intro w
  simp [P201Specs.Wave.sineSymbol, P201Specs.Wave.cosineSymbol,
    P201Specs.Wave.cosineDerivativeSymbol]

theorem scalarContinuity : P201Specs.Wave.scalarContinuityStatement := by
  constructor
  · have he : (fun p : ℝ × ℝ => P201Specs.Wave.sineSymbol p.1 p.2) =
        fun p => p.1 * Real.sinc (p.1 * p.2) := by
      funext p
      exact sineSymbol_eq_sinc _ _
    rw [he]
    exact continuous_fst.mul (Real.continuous_sinc.comp (continuous_fst.mul continuous_snd))
  · exact Real.continuous_cos.comp (continuous_fst.mul continuous_snd)

theorem scalarDerivatives : P201Specs.Wave.scalarDerivativesStatement := by
  intro t w
  constructor
  · by_cases hw : w = 0
    · simpa [hw, P201Specs.Wave.sineSymbol, P201Specs.Wave.cosineSymbol] using
        hasDerivAt_id' t
    · have h := (((hasDerivAt_id t).mul_const w).sin).div_const w
      simpa [P201Specs.Wave.sineSymbol, P201Specs.Wave.cosineSymbol, hw] using h
  · have h := ((hasDerivAt_id t).mul_const w).cos
    convert h using 1 <;> simp [P201Specs.Wave.cosineSymbol,
      P201Specs.Wave.cosineDerivativeSymbol, mul_comm]

open P201Specs.Wave (FrequencyL2)

/-- Multiplication on frequency L² by an essentially bounded symbol. -/
def boundedFrequencyMultiplier {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) : FrequencyL2 n →L[ℂ] FrequencyL2 n :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 (hm.toLp m)

theorem boundedFrequencyMultiplier_ae {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) (f : FrequencyL2 n) :
    (boundedFrequencyMultiplier m hm f : Space n → ℂ) =ᵐ[volume]
      fun ξ => m ξ * f ξ := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    (hm.toLp m) f, hm.coeFn_toLp] with ξ hξ hmξ
  simpa [boundedFrequencyMultiplier, hmξ] using hξ

theorem boundedFrequencyMultiplier_norm_le {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ ξ, ‖m ξ‖ ≤ B) :
    ‖boundedFrequencyMultiplier m hm‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedFrequencyMultiplier_ae m hm f] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_mul_of_nonneg_right (hb ξ) (norm_nonneg _)

theorem cosineSymbol_memLp (n : ℕ) (c t : ℝ) :
    MemLp (fun ξ : Space n => (cosineSymbol t (frequency n c ξ) : ℂ)) ∞ volume := by
  apply memLp_top_of_bound (by
    unfold cosineSymbol P201Specs.Wave.cosineSymbol frequency P201Specs.Wave.frequency
    fun_prop) 1
  exact Filter.Eventually.of_forall (fun ξ => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (scalarBounds t (frequency n c ξ)).2.2)

theorem sineSymbol_memLp (n : ℕ) (c t : ℝ) :
    MemLp (fun ξ : Space n => (sineSymbol t (frequency n c ξ) : ℂ)) ∞ volume := by
  have hm : Continuous (fun ξ : Space n => (sineSymbol t (frequency n c ξ) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    have hc : Continuous (fun ξ : Space n => (t, frequency n c ξ)) := by
      unfold frequency P201Specs.Wave.frequency
      fun_prop
    exact scalarContinuity.1.comp hc
  apply memLp_top_of_bound hm.aestronglyMeasurable |t|
  exact Filter.Eventually.of_forall (fun ξ => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (scalarBounds t (frequency n c ξ)).1)

/-- The physical L² multiplier is conjugated by the canonical Plancherel map. -/
def fourierMultiplier {n : ℕ} (m : Space n → ℂ) (hm : MemLp m ∞ volume) :
    FrequencyL2 n →L[ℂ] FrequencyL2 n :=
  (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    ∘L boundedFrequencyMultiplier m hm ∘L
    (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).toContinuousLinearEquiv.toContinuousLinearMap

theorem fourierMultiplier_ae {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) (f : FrequencyL2 n) :
    (𝓕 (fourierMultiplier m hm f) : FrequencyL2 n) =ᵐ[volume]
      fun ξ => m ξ * (𝓕 f : FrequencyL2 n) ξ := by
  change ((MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ)
    ((MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm
      (boundedFrequencyMultiplier m hm (𝓕 f))) : Space n → ℂ) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact boundedFrequencyMultiplier_ae m hm _

theorem fourierMultiplier_norm_le {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ ξ, ‖m ξ‖ ≤ B) :
    ‖fourierMultiplier m hm‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  change ‖(MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm
    (boundedFrequencyMultiplier m hm (𝓕 f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ B * ‖𝓕 f‖ := ContinuousLinearMap.le_of_opNorm_le _
      (boundedFrequencyMultiplier_norm_le m hm B hB hb) _
    _ = B * ‖f‖ := by rw [MeasureTheory.Lp.norm_fourier_eq]

def cosineL2 (n : ℕ) (c t : ℝ) : FrequencyL2 n →L[ℂ] FrequencyL2 n :=
  fourierMultiplier _ (cosineSymbol_memLp n c t)

def sineL2 (n : ℕ) (c t : ℝ) : FrequencyL2 n →L[ℂ] FrequencyL2 n :=
  fourierMultiplier _ (sineSymbol_memLp n c t)

theorem cosineL2_norm_le (n : ℕ) (c t : ℝ) : ‖cosineL2 n c t‖ ≤ 1 := by
  apply fourierMultiplier_norm_le _ _ 1 zero_le_one
  intro ξ
  simpa only [Complex.norm_real, Real.norm_eq_abs] using (scalarBounds t (frequency n c ξ)).2.2

theorem sineL2_norm_le (n : ℕ) (c t : ℝ) : ‖sineL2 n c t‖ ≤ |t| := by
  apply fourierMultiplier_norm_le _ _ |t| (abs_nonneg t)
  intro ξ
  simpa only [Complex.norm_real, Real.norm_eq_abs] using (scalarBounds t (frequency n c ξ)).1

theorem l2_norm_sq_integral {n : ℕ} (f : FrequencyL2 n) :
    ‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Dominated convergence for bounded frequency multipliers, on each fixed L² input.
The local bound is allowed to depend on the filter's limiting parameter. -/
theorem boundedFrequencyMultiplier_tendsto {n : ℕ} {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (m : ι → Space n → ℂ)
    (hm : ∀ i, MemLp (m i) ∞ volume) (m₀ : Space n → ℂ)
    (hm₀ : MemLp m₀ ∞ volume) (B : ℝ)
    (hb : ∀ᶠ i in l, ∀ ξ, ‖m i ξ‖ ≤ B) (hb₀ : ∀ ξ, ‖m₀ ξ‖ ≤ B)
    (hlim : ∀ ξ, Tendsto (fun i => m i ξ) l (𝓝 (m₀ ξ))) (f : FrequencyL2 n) :
    Tendsto (fun i => boundedFrequencyMultiplier (m i) (hm i) f) l
      (𝓝 (boundedFrequencyMultiplier m₀ hm₀ f)) := by
  have hsq (i : ι) :
      ‖boundedFrequencyMultiplier (m i) (hm i) f - boundedFrequencyMultiplier m₀ hm₀ f‖ ^ 2 =
      ∫ ξ, ‖m i ξ * f ξ - m₀ ξ * f ξ‖ ^ 2 := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Lp.coeFn_sub
      (boundedFrequencyMultiplier (m i) (hm i) f) (boundedFrequencyMultiplier m₀ hm₀ f),
      boundedFrequencyMultiplier_ae (m i) (hm i) f,
      boundedFrequencyMultiplier_ae m₀ hm₀ f] with ξ hs hi h₀
    simp only [hs, Pi.sub_apply, hi, h₀]
  have hlim' : Tendsto (fun i => ∫ ξ, ‖m i ξ * f ξ - m₀ ξ * f ξ‖ ^ 2) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (l := l)
      (μ := (volume : Measure (Space n)))
      (F := fun i ξ => ‖m i ξ * f ξ - m₀ ξ * f ξ‖ ^ 2)
      (f := fun _ => (0 : ℝ)) (fun ξ => (2 * B * ‖f ξ‖) ^ 2)
    simp only [integral_zero] at h
    apply h
    · exact Eventually.of_forall (fun i =>
        ((((hm i).aestronglyMeasurable.mul (MeasureTheory.Lp.memLp f).aestronglyMeasurable).sub
        (hm₀.aestronglyMeasurable.mul (MeasureTheory.Lp.memLp f).aestronglyMeasurable)).norm.pow 2))
    · filter_upwards [hb] with i hi
      exact Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        calc
          ‖m i ξ * f ξ - m₀ ξ * f ξ‖ ≤ ‖m i ξ * f ξ‖ + ‖m₀ ξ * f ξ‖ := norm_sub_le _ _
          _ ≤ B * ‖f ξ‖ + B * ‖f ξ‖ := by
            simp only [norm_mul]
            exact add_le_add (mul_le_mul_of_nonneg_right (hi ξ) (norm_nonneg _))
              (mul_le_mul_of_nonneg_right (hb₀ ξ) (norm_nonneg _))
          _ = 2 * B * ‖f ξ‖ := by ring)
    · exact ((MeasureTheory.Lp.memLp f).norm.const_mul (2 * B)).integrable_sq
    · exact Eventually.of_forall (fun ξ => by
        have ht := ((hlim ξ).mul_const (f ξ)).sub_const (m₀ ξ * f ξ)
        simpa using ht.norm.pow 2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hlim'
  simp only [Real.sqrt_zero] at hsqrt
  convert hsqrt using 1
  ext i
  rw [Function.comp_apply, ← hsq, Real.sqrt_sq (norm_nonneg _)]

theorem cosineL2_continuous (n : ℕ) (c : ℝ) (f : FrequencyL2 n) :
    Continuous (fun t => cosineL2 n c t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm.continuous.continuousAt.tendsto.comp
  apply boundedFrequencyMultiplier_tendsto
    (m := fun s ξ => (cosineSymbol s (frequency n c ξ) : ℂ))
    (hm := cosineSymbol_memLp n c) (B := 1)
  · exact Eventually.of_forall (fun s ξ => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (scalarBounds s (frequency n c ξ)).2.2)
  · intro ξ
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (scalarBounds t (frequency n c ξ)).2.2
  · intro ξ
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((scalarDerivatives t (frequency n c ξ)).2.continuousAt.tendsto)

theorem sineL2_continuous (n : ℕ) (c : ℝ) (f : FrequencyL2 n) :
    Continuous (fun t => sineL2 n c t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm.continuous.continuousAt.tendsto.comp
  apply boundedFrequencyMultiplier_tendsto
    (m := fun s ξ => (sineSymbol s (frequency n c ξ) : ℂ))
    (hm := sineSymbol_memLp n c) (B := |t| + 1)
  · have hnear : ∀ᶠ s in 𝓝 t, |s - t| < 1 := by
      filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with s hs
      simpa only [Metric.mem_ball, Real.dist_eq] using hs
    filter_upwards [hnear] with s hs
    intro ξ
    have hs' : |s| ≤ |t| + 1 := by
      have htri := abs_add_le (s - t) t
      have he : s - t + t = s := by ring
      rw [he] at htri
      linarith
    calc
      _ ≤ |s| := by simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (scalarBounds s (frequency n c ξ)).1
      _ ≤ |t| + 1 := hs'
  · intro ξ
    calc
      _ ≤ |t| := by simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (scalarBounds t (frequency n c ξ)).1
      _ ≤ |t| + 1 := le_add_of_nonneg_right zero_le_one
  · intro ξ
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((scalarDerivatives t (frequency n c ξ)).1.continuousAt.tendsto)

/-- Uniform difference-quotient control, including the zero frequency. -/
theorem sineSymbol_slope_bound (t s w : ℝ) :
    |slope (fun r => sineSymbol r w) t s| ≤ 1 := by
  have hb : |sineSymbol s w - sineSymbol t w| ≤ |s - t| := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := (Set.univ : Set ℝ)) (f := fun r => sineSymbol r w)
      (f' := fun r => cosineSymbol r w) (C := 1)
      (fun r _ => (scalarDerivatives r w).1.hasDerivWithinAt)
      (fun r _ => by simpa only [Real.norm_eq_abs] using (scalarBounds r w).2.2)
      convex_univ (mem_univ t) (mem_univ s)
    simpa only [Real.norm_eq_abs, one_mul] using h
  rw [slope_def_field, abs_div]
  by_cases hst : s = t
  · simp [hst]
  · exact (div_le_one (abs_pos.mpr (sub_ne_zero.mpr hst))).mpr hb

theorem sineFrequency_hasDerivAt (n : ℕ) (c t : ℝ) (f : FrequencyL2 n) :
    HasDerivAt
      (fun s => boundedFrequencyMultiplier _ (sineSymbol_memLp n c s) f)
      (boundedFrequencyMultiplier _ (cosineSymbol_memLp n c t) f) t := by
  let m : ℝ → Space n → ℂ := fun s ξ =>
    (slope (fun r => sineSymbol r (frequency n c ξ)) t s : ℝ)
  have hm (s : ℝ) : MemLp (m s) ∞ volume := by
    apply memLp_top_of_bound _ 1
      (Eventually.of_forall (fun ξ => by
        simpa only [m, Complex.norm_real, Real.norm_eq_abs] using
          sineSymbol_slope_bound t s (frequency n c ξ)))
    have he : m s = fun ξ => ((s - t)⁻¹ : ℂ) *
        ((sineSymbol s (frequency n c ξ) : ℂ) - (sineSymbol t (frequency n c ξ) : ℂ)) := by
      funext ξ
      simp [m, slope_def_field, div_eq_inv_mul]
    rw [he]
    exact (((sineSymbol_memLp n c s).aestronglyMeasurable.sub
      (sineSymbol_memLp n c t).aestronglyMeasurable).const_mul _)
  have hlim := boundedFrequencyMultiplier_tendsto (l := 𝓝[≠] t) m hm
    (fun ξ => (cosineSymbol t (frequency n c ξ) : ℂ)) (cosineSymbol_memLp n c t) 1
    (Eventually.of_forall (fun s ξ => by
      simpa only [m, Complex.norm_real, Real.norm_eq_abs] using
        sineSymbol_slope_bound t s (frequency n c ξ)))
    (fun ξ => by simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (scalarBounds t (frequency n c ξ)).2.2)
    (fun ξ => Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((scalarDerivatives t (frequency n c ξ)).1.tendsto_slope)) f
  apply hasDerivAt_iff_tendsto_slope.mpr
  convert hlim using 1
  funext s
  apply MeasureTheory.Lp.ext
  filter_upwards [boundedFrequencyMultiplier_ae (m s) (hm s) f,
    boundedFrequencyMultiplier_ae _ (sineSymbol_memLp n c s) f,
    boundedFrequencyMultiplier_ae _ (sineSymbol_memLp n c t) f,
    MeasureTheory.Lp.coeFn_smul (s - t)⁻¹
      (boundedFrequencyMultiplier _ (sineSymbol_memLp n c s) f -
        boundedFrequencyMultiplier _ (sineSymbol_memLp n c t) f),
    MeasureTheory.Lp.coeFn_sub
      (boundedFrequencyMultiplier _ (sineSymbol_memLp n c s) f)
      (boundedFrequencyMultiplier _ (sineSymbol_memLp n c t) f)] with ξ hmξ hs ht hsm hsub
  simp only [slope_def_module]
  simp only [Pi.smul_apply] at hsm
  simp only [Pi.sub_apply] at hsub
  rw [hsm, hsub, hs, ht, hmξ]
  simp only [m, slope_def_field, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_sub]
  push_cast
  ring

theorem sineL2_hasDerivAt (n : ℕ) (c t : ℝ) (f : FrequencyL2 n) :
    HasDerivAt (fun s => sineL2 n c s f) (cosineL2 n c t f) t := by
  let J := (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  exact J.hasFDerivAt.comp_hasDerivAt t (sineFrequency_hasDerivAt n c t (𝓕 f))

theorem cosineSymbol_slope_bound (t s w : ℝ) :
    |slope (fun r => cosineSymbol r w) t s| ≤ |w| := by
  have hb : |cosineSymbol s w - cosineSymbol t w| ≤ |w| * |s - t| := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := (Set.univ : Set ℝ)) (f := fun r => cosineSymbol r w)
      (f' := fun r => cosineDerivativeSymbol r w) (C := |w|)
      (fun r _ => (scalarDerivatives r w).2.hasDerivWithinAt)
      (fun r _ => by
        change |-w * Real.sin (r * w)| ≤ |w|
        rw [abs_mul, abs_neg]
        exact mul_le_of_le_one_right (abs_nonneg w) (Real.abs_sin_le_one _))
      convex_univ (mem_univ t) (mem_univ s)
    simpa only [Real.norm_eq_abs] using h
  rw [slope_def_field, abs_div]
  by_cases hst : s = t
  · simp [hst]
  · exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hst))).mpr hb

theorem cosineSymbol_slope_div_bound (t s w : ℝ) :
    |slope (fun r => cosineSymbol r w) t s / w| ≤ 1 := by
  by_cases hw : w = 0
  · simp [hw]
  · rw [abs_div]
    exact (div_le_one (abs_pos.mpr hw)).mpr (cosineSymbol_slope_bound t s w)

theorem cosineSymbol_slope_div_mul (t s w : ℝ) :
    (slope (fun r => cosineSymbol r w) t s / w) * w =
      slope (fun r => cosineSymbol r w) t s := by
  by_cases hw : w = 0
  · simp [hw, slope_def_field, cosineSymbol, P201Specs.Wave.cosineSymbol]
  · exact div_mul_cancel₀ _ hw

theorem negativeSineSymbol_memLp (n : ℕ) (c t : ℝ) :
    MemLp (fun ξ : Space n => (-Real.sin (t * frequency n c ξ) : ℂ)) ∞ volume := by
  apply memLp_top_of_bound (by
    unfold frequency P201Specs.Wave.frequency
    fun_prop) 1
  exact Eventually.of_forall (fun ξ => by
    simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_neg] using Real.abs_sin_le_one _)

/-- Cosine differentiation needs precisely one frequency weight of the input.
The Euclidean H¹ bridge, still outstanding, will supply this relation. -/
theorem cosineFrequency_hasDerivAt (n : ℕ) (c t : ℝ) (f v : FrequencyL2 n)
    (hv : (v : Space n → ℂ) =ᵐ[volume] fun ξ => (frequency n c ξ : ℂ) * f ξ) :
    HasDerivAt
      (fun s => boundedFrequencyMultiplier _ (cosineSymbol_memLp n c s) f)
      (boundedFrequencyMultiplier _ (negativeSineSymbol_memLp n c t) v) t := by
  let m : ℝ → Space n → ℂ := fun s ξ =>
    (slope (fun r => cosineSymbol r (frequency n c ξ)) t s / frequency n c ξ : ℝ)
  have hm (s : ℝ) : MemLp (m s) ∞ volume := by
    apply memLp_top_of_bound _ 1
      (Eventually.of_forall (fun ξ => by
        simpa only [m, Complex.norm_real, Real.norm_eq_abs] using
          cosineSymbol_slope_div_bound t s (frequency n c ξ)))
    unfold m cosineSymbol P201Specs.Wave.cosineSymbol frequency P201Specs.Wave.frequency
    simp only [slope_def_field]
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hm_limit (ξ : Space n) : Tendsto (fun s => m s ξ) (𝓝[≠] t)
      (𝓝 (-Real.sin (t * frequency n c ξ) : ℂ)) := by
    have he : cosineDerivativeSymbol t (frequency n c ξ) / frequency n c ξ =
        -Real.sin (t * frequency n c ξ) := by
      by_cases hw : frequency n c ξ = 0
      · simp [hw, cosineDerivativeSymbol, P201Specs.Wave.cosineDerivativeSymbol]
      · simp only [cosineDerivativeSymbol, P201Specs.Wave.cosineDerivativeSymbol]
        field_simp
    have h := ((scalarDerivatives t (frequency n c ξ)).2.tendsto_slope).div_const
      (frequency n c ξ)
    change Tendsto _ _ (𝓝 (cosineDerivativeSymbol t (frequency n c ξ) / frequency n c ξ)) at h
    rw [he] at h
    simpa only [m, cosineSymbol, Function.comp_def, Complex.ofReal_neg] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp h
  have hlim := boundedFrequencyMultiplier_tendsto (l := 𝓝[≠] t) m hm
    (fun ξ => (-Real.sin (t * frequency n c ξ) : ℂ)) (negativeSineSymbol_memLp n c t) 1
    (Eventually.of_forall (fun s ξ => by
      simpa only [m, Complex.norm_real, Real.norm_eq_abs] using
        cosineSymbol_slope_div_bound t s (frequency n c ξ)))
    (fun ξ => by simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_neg] using
      Real.abs_sin_le_one (t * frequency n c ξ)) hm_limit v
  apply hasDerivAt_iff_tendsto_slope.mpr
  convert hlim using 1
  funext s
  apply MeasureTheory.Lp.ext
  filter_upwards [boundedFrequencyMultiplier_ae (m s) (hm s) v,
    boundedFrequencyMultiplier_ae _ (cosineSymbol_memLp n c s) f,
    boundedFrequencyMultiplier_ae _ (cosineSymbol_memLp n c t) f,
    MeasureTheory.Lp.coeFn_smul (s - t)⁻¹
      (boundedFrequencyMultiplier _ (cosineSymbol_memLp n c s) f -
        boundedFrequencyMultiplier _ (cosineSymbol_memLp n c t) f),
    MeasureTheory.Lp.coeFn_sub
      (boundedFrequencyMultiplier _ (cosineSymbol_memLp n c s) f)
      (boundedFrequencyMultiplier _ (cosineSymbol_memLp n c t) f), hv]
    with ξ hmξ hs ht hsm hsub hvξ
  simp only [slope_def_module]
  simp only [Pi.smul_apply] at hsm
  simp only [Pi.sub_apply] at hsub
  rw [hsm, hsub, hs, ht, hmξ, hvξ]
  have he : m s ξ * (frequency n c ξ : ℂ) =
      (slope (fun r => cosineSymbol r (frequency n c ξ)) t s : ℝ) := by
    dsimp only [m]
    rw [← Complex.ofReal_mul, cosineSymbol_slope_div_mul]
  rw [← mul_assoc, he]
  simp only [slope_def_field, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_sub]
  push_cast
  ring

theorem cosineL2_hasDerivAt_weighted (n : ℕ) (c t : ℝ) (f v : FrequencyL2 n)
    (hv : (v : Space n → ℂ) =ᵐ[volume]
      fun ξ => (frequency n c ξ : ℂ) * (𝓕 f : FrequencyL2 n) ξ) :
    ∃ d : FrequencyL2 n, HasDerivAt (fun s => cosineL2 n c s f) d t ∧
      (𝓕 d : FrequencyL2 n) =ᵐ[volume]
        fun ξ => (cosineDerivativeSymbol t (frequency n c ξ) : ℂ) *
          (𝓕 f : FrequencyL2 n) ξ := by
  let F := MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ
  let J := F.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  refine ⟨F.symm (boundedFrequencyMultiplier _ (negativeSineSymbol_memLp n c t) v), ?_, ?_⟩
  · exact J.hasFDerivAt.comp_hasDerivAt t (cosineFrequency_hasDerivAt n c t (𝓕 f) v hv)
  · change (F (F.symm _) : Space n → ℂ) =ᵐ[volume] _
    rw [LinearIsometryEquiv.apply_symm_apply]
    filter_upwards [boundedFrequencyMultiplier_ae _ (negativeSineSymbol_memLp n c t) v, hv]
      with ξ hξ hvξ
    rw [hξ, hvξ]
    simp only [cosineDerivativeSymbol, P201Specs.Wave.cosineDerivativeSymbol]
    push_cast
    ring

theorem cosineL2_zero (n : ℕ) (c : ℝ) :
    cosineL2 n c 0 = ContinuousLinearMap.id ℂ (FrequencyL2 n) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).injective
  change (𝓕 (cosineL2 n c 0 f) : FrequencyL2 n) = 𝓕 f
  apply MeasureTheory.Lp.ext
  filter_upwards [fourierMultiplier_ae _ (cosineSymbol_memLp n c 0) f] with ξ hξ
  change (𝓕 (cosineL2 n c 0 f) : FrequencyL2 n) ξ = (𝓕 f : FrequencyL2 n) ξ
  simpa only [cosineL2, cosineSymbol, P201Specs.Wave.cosineSymbol, zero_mul, Real.cos_zero,
    Complex.ofReal_one, one_mul] using hξ

theorem sineL2_zero (n : ℕ) (c : ℝ) : sineL2 n c 0 = 0 := by
  apply norm_le_zero_iff.mp
  simpa using sineL2_norm_le n c 0

theorem l2BoundedMultipliers : P201Specs.Wave.l2BoundedMultipliersStatement := by
  intro n c
  refine ⟨cosineL2 n c, sineL2 n c, ?_, ?_, ?_, cosineL2_zero n c, sineL2_zero n c,
    cosineL2_continuous n c, sineL2_continuous n c, sineL2_hasDerivAt n c,
    cosineL2_hasDerivAt_weighted n c⟩
  · intro t f
    exact fourierMultiplier_ae _ (cosineSymbol_memLp n c t) f
  · intro t f
    exact fourierMultiplier_ae _ (sineSymbol_memLp n c t) f
  · intro t
    exact ⟨cosineL2_norm_le n c t, sineL2_norm_le n c t⟩

/-! The Euclidean weak derivative / Fourier bridge uses the actual test-space
and L² embeddings, with the shared negative 2π phase. -/

open scoped SchwartzMap
open LineDeriv

/-- The compact-test inclusion commutes with each coordinate derivative. -/
theorem testToSchwartz_coordinateDerivative {n : ℕ}
    (j : Fin n) (φ : P102.U4.WholeTests n ℂ) :
    P102.U4.testToSchwartz n ℂ (P102.U4.testPartialWord ⊤ [j] φ) =
      ∂_{coordinate n j} (P102.U4.testToSchwartz n ℂ φ) := by
  ext x
  rw [P102.U4.testToSchwartz_apply, P102.U4.testPartialWord_coe,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

/-- Testing the L² tempered embedding on compact tests gives precisely the
shared regular distribution, without a conjugate in the test factor. -/
theorem l2_tempered_test {n : ℕ} (f : FrequencyL2 n)
    (φ : P102.U4.WholeTests n ℂ) :
    (f : 𝓢'(Space n, ℂ)) (P102.U4.testToSchwartz n ℂ φ) =
      P102.U4.regularDistribution ⊤ f φ := by
  rw [MeasureTheory.Lp.toTemperedDistribution_apply,
    P102.U4.regular_pairing n ℂ ⊤ f
      (((MeasureTheory.Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn _)]
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ, smul_eq_mul,
    P102.U4.testToSchwartz_apply]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- The weak coordinate derivative equation is equivalent to the same equation
in tempered distributions. Density supplies the extension to Schwartz tests. -/
theorem weakDerivative_iff_tempered {n : ℕ} (j : Fin n) (f v : FrequencyL2 n) :
    P102.U4.distributionPartial ({j} : MultiIndex n)
      (P102.U4.regularDistribution ⊤ f) = P102.U4.regularDistribution ⊤ v ↔
    ∂_{coordinate n j} (f : 𝓢'(Space n, ℂ)) = (v : 𝓢'(Space n, ℂ)) := by
  have he (φ : P102.U4.WholeTests n ℂ) :
      (∂_{coordinate n j} (f : 𝓢'(Space n, ℂ)))
          (P102.U4.testToSchwartz n ℂ φ) =
        P102.U4.distributionPartial ({j} : MultiIndex n)
          (P102.U4.regularDistribution ⊤ f) φ := by
    rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
      ← testToSchwartz_coordinateDerivative, l2_tempered_test]
    simp [P102.U4.distributionPartial]
  constructor
  · intro h
    apply DFunLike.coe_injective
    apply (P102.U4.testToSchwartz_denseRange n ℂ).equalizer
      (∂_{coordinate n j} (f : 𝓢'(Space n, ℂ))).continuous
      (v : 𝓢'(Space n, ℂ)).continuous
    funext φ
    simp only [Function.comp_apply]
    exact (he φ).trans ((congrArg (fun T => T φ) h).trans (l2_tempered_test v φ).symm)
  · intro h
    ext φ
    rw [← he, h, l2_tempered_test]

/-- Polynomially growing multiplication agrees with multiplication of regular
functions, even when the product has not yet been shown to belong to L². -/
theorem tempered_mul_iff_ae {n : ℕ} (a : Space n → ℂ)
    (ha : a.HasTemperateGrowth) (f v : FrequencyL2 n) :
    (v : 𝓢'(Space n, ℂ)) = TemperedDistribution.smulLeftCLM ℂ a f ↔
      (v : Space n → ℂ) =ᵐ[volume] fun x => a x * f x := by
  have hf := (MeasureTheory.Lp.memLp f).locallyIntegrable (by norm_num)
  have hv := (MeasureTheory.Lp.memLp v).locallyIntegrable (by norm_num)
  have haf : LocallyIntegrable (fun x => a x * f x) volume :=
    hf.continuous_mul ha.1.continuous
  have hp (φ : 𝓢(Space n, ℂ)) :
      TemperedDistribution.smulLeftCLM ℂ a (f : 𝓢'(Space n, ℂ)) φ =
        ∫ x, (a x * f x) * φ x := by
    rw [TemperedDistribution.smulLeftCLM_apply_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      dsimp only
      rw [SchwartzMap.smulLeftCLM_apply_apply ha]
      simp only [smul_eq_mul]
      ring)
  constructor
  · intro h
    have he : P102.U4.regularDistribution ⊤ v =
        P102.U4.regularDistribution ⊤ (fun x => a x * f x) := by
      ext φ
      rw [← l2_tempered_test, h, hp,
        P102.U4.regular_pairing n ℂ ⊤ _ (haf.locallyIntegrableOn _)]
      simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ,
        P102.U4.testToSchwartz_apply]
    have he' := (P102.U4.regular_injectivity n ℂ ⊤ _ _
      (hv.locallyIntegrableOn _) (haf.locallyIntegrableOn _)).mp he
    simpa only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using he'
  · intro h
    ext φ
    rw [MeasureTheory.Lp.toTemperedDistribution_apply, hp]
    apply integral_congr_ae
    filter_upwards [h] with x hx
    simp [hx, mul_comm]

/-- The exact 2π coordinate multiplier characterizes the shared weak derivative. -/
theorem weakDerivative_iff_fourier {n : ℕ} (j : Fin n) (f v : FrequencyL2 n) :
    P102.U4.distributionPartial ({j} : MultiIndex n)
      (P102.U4.regularDistribution ⊤ f) = P102.U4.regularDistribution ⊤ v ↔
    (𝓕 v : FrequencyL2 n) =ᵐ[volume]
      fun ξ => (2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) *
        (𝓕 f : FrequencyL2 n) ξ := by
  let a : Space n → ℂ := fun ξ => 2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)
  have hcoord : (fun ξ : Space n => (inner ℝ ξ (coordinate n j) : ℂ)) =
      fun ξ => (ξ j : ℂ) := by
    funext ξ
    rw [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.inner_basisFun_real]
  have hg : (fun ξ : Space n => (ξ j : ℂ)).HasTemperateGrowth := by
    rw [← hcoord]
    fun_prop
  have ha : a.HasTemperateGrowth :=
    Function.HasTemperateGrowth.mul (Function.HasTemperateGrowth.const _) hg
  have hp : 𝓕 (∂_{coordinate n j} (f : 𝓢'(Space n, ℂ))) =
      TemperedDistribution.smulLeftCLM ℂ a
        ((𝓕 f : FrequencyL2 n) : 𝓢'(Space n, ℂ)) := by
    rw [TemperedDistribution.fourier_lineDerivOp_eq,
      MeasureTheory.Lp.fourier_toTemperedDistribution_eq, hcoord]
    exact (congrArg (fun L : 𝓢'(Space n, ℂ) →L[ℂ] 𝓢'(Space n, ℂ) =>
      L ((𝓕 f : FrequencyL2 n) : 𝓢'(Space n, ℂ)))
        (TemperedDistribution.smulLeftCLM_smul (F := ℂ) hg
          (2 * (Real.pi : ℂ) * Complex.I))).symm
  rw [weakDerivative_iff_tempered]
  constructor
  · intro h
    apply (tempered_mul_iff_ae a ha (𝓕 f) (𝓕 v)).mp
    rw [← hp, h, MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
  · intro h
    have he := (tempered_mul_iff_ae a ha (𝓕 f) (𝓕 v)).mpr h
    have he' : 𝓕 (∂_{coordinate n j} (f : 𝓢'(Space n, ℂ))) =
        𝓕 (v : 𝓢'(Space n, ℂ)) := by
      rw [hp, ← he, MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
    have := congrArg (fun T : 𝓢'(Space n, ℂ) => 𝓕⁻ T) he'
    simpa only [FourierTransform.fourierInv_fourier_eq] using this

open P201Specs.Wave (WholeL2 WholeH1 wholeL2Standard embeddedFourier WaveOperators WaveFamilyLaws)

/-- Removing restriction to the whole space preserves representatives a.e. -/
theorem wholeL2Standard_ae {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : WholeL2 n 𝕜) :
    (wholeL2Standard n 𝕜 f : Space n → 𝕜) =ᵐ[volume] f := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f _

/-- H¹ indices consist exactly of the zeroth derivative and the coordinate derivatives. -/
def firstOrderIndexEquiv (n : ℕ) : Option (Fin n) ≃ P102.U4.SobolevIndex n 1 :=
  Equiv.ofBijective
    (fun o => o.elim (P102.U4.zeroSobolevIndex n 1) (fun j => ⟨{j}, by simp⟩)) (by
      constructor
      · intro a b h
        cases a <;> cases b
        · rfl
        · have hc := congrArg (fun α : P102.U4.SobolevIndex n 1 => α.val.card) h
          change (0 : ℕ) = 1 at hc
          omega
        · have hc := congrArg (fun α : P102.U4.SobolevIndex n 1 => α.val.card) h
          change (1 : ℕ) = 0 at hc
          omega
        · congr 1
          exact Multiset.singleton_inj.mp (congrArg Subtype.val h)
      · intro α
        by_cases h0 : α.val.card = 0
        · refine ⟨none, ?_⟩
          apply Subtype.ext
          exact (Multiset.card_eq_zero.mp h0).symm
        · obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp (by have hα := α.property; omega : α.val.card = 1)
          exact ⟨some j, Subtype.ext hj.symm⟩)

/-- The full shared H¹ norm has exactly its displacement and gradient coordinates. -/
theorem h1_norm_sq {n : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Domain n}
    (u : H 𝕜 Ω 1) :
    ‖u‖ ^ 2 = ‖hUnderlying Ω 1 u‖ ^ 2 + ∑ j : Fin n, ‖hFirstDerivative u j‖ ^ 2 := by
  rw [fullHilbertNorm Ω 1 u, ← Equiv.sum_comp (firstOrderIndexEquiv n)]
  rw [Fintype.sum_option]
  rfl

/-- First weak derivatives suffice for the actual H¹ graph, on any open domain. -/
theorem exists_h1_of_weakDerivatives {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (f : Lp 𝕜 Ω 2) (v : Fin n → Lp 𝕜 Ω 2)
    (hv : ∀ j, P102.U4.distributionPartial ({j} : MultiIndex n)
      (regularDistribution Ω f) = regularDistribution Ω (v j)) :
    ∃ u : H 𝕜 Ω 1, hUnderlying Ω 1 u = f ∧ ∀ j, hFirstDerivative u j = v j := by
  have hf : P102.U4.HasSobolevDerivatives Ω 1 2 f := by
    intro α hα
    by_cases h0 : α.card = 0
    · refine ⟨f, ?_⟩
      rw [Multiset.card_eq_zero.mp h0]
      exact P102.U4.derivative_zero n 𝕜 Ω _
    · obtain ⟨j, rfl⟩ := Multiset.card_eq_one.mp (by omega : α.card = 1)
      exact ⟨v j, hv j⟩
  have hr := (Set.ext_iff.mp (P102.U4.sobolev_range Ω 1 2) f).mpr hf
  obtain ⟨w, hw⟩ := hr
  let u := (P201Specs.hToW 𝕜 Ω 1).symm w
  have hu : hUnderlying Ω 1 u = f := by
    change P102.U4.sobolevUnderlying (P201Specs.hToW 𝕜 Ω 1 u) = f
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hw
  refine ⟨u, hu, fun j => ?_⟩
  apply P102.U4.regularLp_injective Ω 2
  change regularDistribution Ω (P102.U4.sobolevDerivative
    (P201Specs.hToW 𝕜 Ω 1 u) ⟨{j}, by simp⟩) = regularDistribution Ω (v j)
  exact (hilbertDerivativeDistribution Ω 1 u ⟨{j}, by simp⟩).symm.trans (by
    change P102.U4.distributionPartial ({j} : MultiIndex n)
      (regularDistribution Ω (hUnderlying Ω 1 u)) = _
    rw [hu]
    exact hv j)

/-- The whole-space change of measure also preserves the regular distribution. -/
theorem wholeL2Standard_regular {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : WholeL2 n 𝕜) :
    regularDistribution ⊤ (wholeL2Standard n 𝕜 f : Space n → 𝕜) =
      regularDistribution ⊤ (f : Space n → 𝕜) := by
  apply (P102.U4.regular_injectivity n 𝕜 ⊤ _ _
    (((MeasureTheory.Lp.memLp (wholeL2Standard n 𝕜 f)).locallyIntegrable
      (by norm_num)).locallyIntegrableOn _)
    (P102.U4.domainLp_locallyIntegrable ⊤ 2 f)).mpr
  simpa only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using wholeL2Standard_ae f

/-- The Fourier transform of each retained weak H¹ derivative has exactly the
coordinate symbol 2π i ξ_j. -/
theorem h1_fourier_derivative {n : ℕ} (g : WholeH1 n ℂ) (j : Fin n) :
    (𝓕 (wholeL2Standard n ℂ (hFirstDerivative g j)) : FrequencyL2 n) =ᵐ[volume]
      fun ξ => (2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) *
        (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g)) : FrequencyL2 n) ξ := by
  apply (weakDerivative_iff_fourier j _ _).mp
  change distributionDerivative ({j} : MultiIndex n)
    (regularDistribution ⊤ (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g) : Space n → ℂ)) =
      regularDistribution ⊤ (wholeL2Standard n ℂ (hFirstDerivative g j) : Space n → ℂ)
  rw [wholeL2Standard_regular, wholeL2Standard_regular]
  exact hilbertDerivativeDistribution ⊤ 1 g ⟨{j}, by simp⟩

/-- The converse bridge constructs the actual shared inhomogeneous H¹ element
from its Fourier coordinate derivatives. -/
theorem exists_h1_of_fourier_derivatives {n : ℕ} (f : WholeL2 n ℂ)
    (hf : ∀ j : Fin n, MemLp
      (fun ξ => (2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) *
        (𝓕 (wholeL2Standard n ℂ f) : FrequencyL2 n) ξ) 2 volume) :
    ∃ g : WholeH1 n ℂ, hUnderlying ⊤ 1 g = f := by
  let v (j : Fin n) : FrequencyL2 n := 𝓕⁻ ((hf j).toLp _)
  have hv (j : Fin n) :
      P102.U4.distributionPartial ({j} : MultiIndex n) (regularDistribution ⊤ f) =
        regularDistribution ⊤ ((wholeL2Standard n ℂ).symm (v j)) := by
    rw [← wholeL2Standard_regular f, ← wholeL2Standard_regular
      ((wholeL2Standard n ℂ).symm (v j)), LinearIsometryEquiv.apply_symm_apply]
    apply (weakDerivative_iff_fourier j _ _).mpr
    change (𝓕 (𝓕⁻ ((hf j).toLp _)) : FrequencyL2 n) =ᵐ[volume] _
    rw [FourierTransform.fourier_fourierInv_eq]
    exact (hf j).coeFn_toLp
  obtain ⟨g, hg, _⟩ := exists_h1_of_weakDerivatives ⊤ f
    (fun j => (wholeL2Standard n ℂ).symm (v j)) hv
  exact ⟨g, hg⟩

def wholeFourierMultiplier {n : ℕ} (m : Space n → ℂ) (hm : MemLp m ∞ volume) :
    WholeL2 n ℂ →L[ℂ] WholeL2 n ℂ :=
  (wholeL2Standard n ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    fourierMultiplier m hm ∘L (wholeL2Standard n ℂ).toContinuousLinearEquiv.toContinuousLinearMap

theorem wholeFourierMultiplier_standard {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) (f : WholeL2 n ℂ) :
    wholeL2Standard n ℂ (wholeFourierMultiplier m hm f) =
      fourierMultiplier m hm (wholeL2Standard n ℂ f) :=
  (wholeL2Standard n ℂ).apply_symm_apply _

theorem wholeFourierMultiplier_norm_le {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ ξ, ‖m ξ‖ ≤ B) :
    ‖wholeFourierMultiplier m hm‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  change ‖(wholeL2Standard n ℂ).symm _‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ B * ‖wholeL2Standard n ℂ f‖ := ContinuousLinearMap.le_of_opNorm_le _
      (fourierMultiplier_norm_le m hm B hB hb) _
    _ = _ := by rw [LinearIsometryEquiv.norm_map]

theorem exists_h1_fourierMultiplier {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) (g : WholeH1 n ℂ) :
    ∃ u : WholeH1 n ℂ,
      hUnderlying ⊤ 1 u = wholeFourierMultiplier m hm (hUnderlying ⊤ 1 g) ∧
      ∀ j, hFirstDerivative u j = wholeFourierMultiplier m hm (hFirstDerivative g j) := by
  apply exists_h1_of_weakDerivatives
  intro j
  rw [← wholeL2Standard_regular, ← wholeL2Standard_regular,
    wholeFourierMultiplier_standard, wholeFourierMultiplier_standard]
  apply (weakDerivative_iff_fourier j _ _).mpr
  filter_upwards [fourierMultiplier_ae m hm (wholeL2Standard n ℂ (hFirstDerivative g j)),
    fourierMultiplier_ae m hm (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g)),
    h1_fourier_derivative g j] with ξ hv hu hg
  rw [hv, hu, hg]
  ring

def h1FourierMultiplierLinear {n : ℕ} (m : Space n → ℂ) (hm : MemLp m ∞ volume) :
    WholeH1 n ℂ →ₗ[ℂ] WholeH1 n ℂ where
  toFun g := (exists_h1_fourierMultiplier m hm g).choose
  map_add' g h := by
    apply hilbertUnderlyingInjective ⊤ 1
    change hUnderlying ⊤ 1 (exists_h1_fourierMultiplier m hm (g + h)).choose =
      hUnderlying ⊤ 1 ((exists_h1_fourierMultiplier m hm g).choose +
        (exists_h1_fourierMultiplier m hm h).choose)
    calc
      _ = wholeFourierMultiplier m hm (hUnderlying ⊤ 1 (g+h)) :=
        (exists_h1_fourierMultiplier m hm (g+h)).choose_spec.1
      _ = wholeFourierMultiplier m hm (hUnderlying ⊤ 1 g) +
          wholeFourierMultiplier m hm (hUnderlying ⊤ 1 h) := by simp only [map_add]
      _ = _ := by rw [map_add, (exists_h1_fourierMultiplier m hm g).choose_spec.1,
        (exists_h1_fourierMultiplier m hm h).choose_spec.1]
  map_smul' z g := by
    apply hilbertUnderlyingInjective ⊤ 1
    change hUnderlying ⊤ 1 (exists_h1_fourierMultiplier m hm (z • g)).choose =
      hUnderlying ⊤ 1 (z • (exists_h1_fourierMultiplier m hm g).choose)
    calc
      _ = wholeFourierMultiplier m hm (hUnderlying ⊤ 1 (z • g)) :=
        (exists_h1_fourierMultiplier m hm (z • g)).choose_spec.1
      _ = z • wholeFourierMultiplier m hm (hUnderlying ⊤ 1 g) := by simp only [map_smul]
      _ = _ := by rw [map_smul, (exists_h1_fourierMultiplier m hm g).choose_spec.1]

theorem h1FourierMultiplierLinear_underlying {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) (g : WholeH1 n ℂ) :
    hUnderlying ⊤ 1 (h1FourierMultiplierLinear m hm g) =
      wholeFourierMultiplier m hm (hUnderlying ⊤ 1 g) :=
  (exists_h1_fourierMultiplier m hm g).choose_spec.1

theorem h1FourierMultiplierLinear_derivative {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) (g : WholeH1 n ℂ) (j : Fin n) :
    hFirstDerivative (h1FourierMultiplierLinear m hm g) j =
      wholeFourierMultiplier m hm (hFirstDerivative g j) :=
  (exists_h1_fourierMultiplier m hm g).choose_spec.2 j

theorem h1FourierMultiplierLinear_bound {n : ℕ} (m : Space n → ℂ)
    (hm : MemLp m ∞ volume) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ ξ, ‖m ξ‖ ≤ B)
    (g : WholeH1 n ℂ) : ‖h1FourierMultiplierLinear m hm g‖ ≤ B * ‖g‖ := by
  have he (f : WholeL2 n ℂ) : ‖wholeFourierMultiplier m hm f‖ ^ 2 ≤ B ^ 2 * ‖f‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (ContinuousLinearMap.le_of_opNorm_le _ (wholeFourierMultiplier_norm_le m hm B hB hb) f) 2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [h1_norm_sq, h1FourierMultiplierLinear_underlying]
  simp only [h1FourierMultiplierLinear_derivative]
  calc
    _ ≤ B ^ 2 * ‖hUnderlying ⊤ 1 g‖ ^ 2 + ∑ j : Fin n, B ^ 2 * ‖hFirstDerivative g j‖ ^ 2 :=
      add_le_add (he _) (Finset.sum_le_sum fun j _ => he _)
    _ = (B * ‖g‖) ^ 2 := by rw [← Finset.mul_sum, ← mul_add, ← h1_norm_sq, mul_pow]

def h1FourierMultiplier {n : ℕ} (m : Space n → ℂ) (hm : MemLp m ∞ volume)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ ξ, ‖m ξ‖ ≤ B) :
    WholeH1 n ℂ →L[ℂ] WholeH1 n ℂ :=
  (h1FourierMultiplierLinear m hm).mkContinuous B
    (h1FourierMultiplierLinear_bound m hm B hB hb)
theorem continuous_h1_of_coordinates {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {X : Type*} [TopologicalSpace X] (u : X → WholeH1 n 𝕜)
    (h0 : Continuous (fun x => hUnderlying ⊤ 1 (u x)))
    (hD : ∀ j, Continuous (fun x => hFirstDerivative (u x) j)) : Continuous u := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x => WithLp.toLp 2 (fun α => (u x).val α))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro α
  obtain ⟨o, rfl⟩ := (firstOrderIndexEquiv n).surjective α
  cases o with
  | none => exact h0
  | some j => exact hD j

def cosineH1 (n : ℕ) (c t : ℝ) : WholeH1 n ℂ →L[ℂ] WholeH1 n ℂ :=
  h1FourierMultiplier _ (cosineSymbol_memLp n c t) 1 zero_le_one (fun ξ => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (scalarBounds t (frequency n c ξ)).2.2)

theorem cosineH1_underlying {n : ℕ} (c t : ℝ) (g : WholeH1 n ℂ) :
    hUnderlying ⊤ 1 (cosineH1 n c t g) =
      wholeFourierMultiplier _ (cosineSymbol_memLp n c t) (hUnderlying ⊤ 1 g) :=
  h1FourierMultiplierLinear_underlying _ _ _

theorem cosineH1_derivative {n : ℕ} (c t : ℝ) (g : WholeH1 n ℂ) (j : Fin n) :
    hFirstDerivative (cosineH1 n c t g) j =
      wholeFourierMultiplier _ (cosineSymbol_memLp n c t) (hFirstDerivative g j) :=
  h1FourierMultiplierLinear_derivative _ _ _ _

theorem cosineH1_norm_le (n : ℕ) (c t : ℝ) : ‖cosineH1 n c t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  apply h1FourierMultiplierLinear_bound _ _ 1 zero_le_one
  intro ξ
  simpa only [Complex.norm_real, Real.norm_eq_abs] using (scalarBounds t (frequency n c ξ)).2.2

theorem wholeCosine_continuous {n : ℕ} (c : ℝ) (f : WholeL2 n ℂ) :
    Continuous (fun t => wholeFourierMultiplier _ (cosineSymbol_memLp n c t) f) :=
  (wholeL2Standard n ℂ).symm.continuous.comp (cosineL2_continuous n c _)

theorem cosineH1_continuous {n : ℕ} (c : ℝ) (g : WholeH1 n ℂ) :
    Continuous (fun t => cosineH1 n c t g) := by
  apply continuous_h1_of_coordinates
  · simpa only [cosineH1_underlying] using wholeCosine_continuous c (hUnderlying ⊤ 1 g)
  · intro j
    simpa only [cosineH1_derivative] using wholeCosine_continuous c (hFirstDerivative g j)


theorem embeddedFourier_complex {n : ℕ} (f : WholeL2 n ℂ) :
    embeddedFourier (ContinuousLinearMap.id ℝ ℂ) f =
      (𝓕 (wholeL2Standard n ℂ f) : FrequencyL2 n) := by
  unfold embeddedFourier
  congr 1
  apply MeasureTheory.Lp.ext
  exact (ContinuousLinearMap.id ℝ ℂ).coeFn_compLp _

theorem wholeCosine_zero (n : ℕ) (c : ℝ) :
    wholeFourierMultiplier _ (cosineSymbol_memLp n c 0) =
      ContinuousLinearMap.id ℂ (WholeL2 n ℂ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (wholeL2Standard n ℂ).injective
  rw [wholeFourierMultiplier_standard]
  change cosineL2 n c 0 (wholeL2Standard n ℂ f) = wholeL2Standard n ℂ f
  rw [cosineL2_zero]
  rfl

theorem cosineH1_zero (n : ℕ) (c : ℝ) :
    cosineH1 n c 0 = ContinuousLinearMap.id ℂ (WholeH1 n ℂ) := by
  apply ContinuousLinearMap.ext
  intro g
  apply hilbertUnderlyingInjective ⊤ 1
  change hUnderlying ⊤ 1 (cosineH1 n c 0 g) = hUnderlying ⊤ 1 g
  rw [cosineH1_underlying, wholeCosine_zero]
  rfl

theorem lp2_norm_sq_integral {α E 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {μ : Measure α}
    (f : MeasureTheory.Lp E 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

theorem hGradient_norm_sq {n : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Domain n}
    (g : H 𝕜 Ω 1) : ‖hGradient g‖ ^ 2 = ∑ j : Fin n, ‖hFirstDerivative g j‖ ^ 2 := by
  rw [lp2_norm_sq_integral (𝕜 := 𝕜)]
  have he : (hGradient g : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[domainMeasure Ω]
      fun x => WithLp.toLp 2 (fun j => hFirstDerivative g j x) :=
    (MemLp.of_eval_piLp (fun j => MeasureTheory.Lp.memLp (hFirstDerivative g j))).coeFn_toLp
  calc
    _ = ∫ x, ∑ j : Fin n, ‖hFirstDerivative g j x‖ ^ 2 ∂domainMeasure Ω := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx, PiLp.norm_sq_eq_of_L2]
    _ = ∑ j : Fin n, ∫ x, ‖hFirstDerivative g j x‖ ^ 2 ∂domainMeasure Ω := by
      exact integral_finsetSum _ (fun j _ => (MeasureTheory.Lp.memLp _).norm.integrable_sq)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (lp2_norm_sq_integral (𝕜 := 𝕜) (hFirstDerivative g j)).symm

theorem h1_norm_sq_gradient {n : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Domain n}
    (g : H 𝕜 Ω 1) : ‖g‖ ^ 2 = ‖hUnderlying Ω 1 g‖ ^ 2 + ‖hGradient g‖ ^ 2 := by
  rw [h1_norm_sq, hGradient_norm_sq]

theorem radial_symbol_norm_sq {n : ℕ} (c : ℝ) (ξ : Space n) (z : ℂ) :
    ‖(frequency n c ξ : ℂ) * z‖ ^ 2 =
      c ^ 2 * ∑ j : Fin n, ‖(2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) * z‖ ^ 2 := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, mul_pow, sq_abs]
  simp only [frequency, P201Specs.Wave.frequency, mul_pow]
  have hξ := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) ξ
  simp only [Real.norm_eq_abs, sq_abs] at hξ
  rw [hξ]
  simp only [Finset.mul_sum, Finset.sum_mul]
  norm_num
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Radial angular frequency times the Fourier transform of actual H¹ data is L². -/
theorem h1_radial_memLp {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (g : WholeH1 n ℂ) :
    MemLp (fun ξ => (frequency n c ξ : ℂ) *
      (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g)) : FrequencyL2 n) ξ) 2 volume := by
  let F : FrequencyL2 n := 𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g))
  let V (ξ : Space n) : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2
    (fun j => (𝓕 (wholeL2Standard n ℂ (hFirstDerivative g j)) : FrequencyL2 n) ξ)
  have hV : MemLp V 2 volume := MemLp.of_eval_piLp (fun j => MeasureTheory.Lp.memLp _)
  have hmeas : AEStronglyMeasurable (fun ξ => (frequency n c ξ : ℂ) * F ξ) volume :=
    ((show Continuous (fun ξ : Space n => (frequency n c ξ : ℂ)) by
      unfold frequency P201Specs.Wave.frequency
      fun_prop).aestronglyMeasurable).mul
      (MeasureTheory.Lp.memLp F).aestronglyMeasurable
  apply hV.of_le_mul hmeas
  filter_upwards [ae_all_iff.mpr (fun j => h1_fourier_derivative g j)] with ξ hξ
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  rw [mul_pow, PiLp.norm_sq_eq_of_L2]
  change ‖(frequency n c ξ : ℂ) * F ξ‖ ^ 2 ≤ c ^ 2 * ∑ j : Fin n,
    ‖(𝓕 (wholeL2Standard n ℂ (hFirstDerivative g j)) : FrequencyL2 n) ξ‖ ^ 2
  simp_rw [hξ]
  exact (radial_symbol_norm_sq c ξ (F ξ)).le

/-- Exact radial Fourier norm, with the shared 2π normalization. -/
theorem h1_radial_norm_sq {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (g : WholeH1 n ℂ) :
    ‖(h1_radial_memLp c hc g).toLp _‖ ^ 2 =
      c ^ 2 * ∑ j : Fin n, ‖hFirstDerivative g j‖ ^ 2 := by
  rw [l2_norm_sq_integral]
  have he : (fun ξ => ‖((h1_radial_memLp c hc g).toLp _ : FrequencyL2 n) ξ‖ ^ 2) =ᵐ[volume]
      (fun ξ => c ^ 2 * ∑ j : Fin n,
        ‖(𝓕 (wholeL2Standard n ℂ (hFirstDerivative g j)) : FrequencyL2 n) ξ‖ ^ 2) := by
    filter_upwards [(h1_radial_memLp c hc g).coeFn_toLp,
      ae_all_iff.mpr (fun j => h1_fourier_derivative g j)] with ξ hξ hderiv
    rw [hξ, radial_symbol_norm_sq]
    simp_rw [hderiv]
  rw [integral_congr_ae he, integral_const_mul,
    integral_finsetSum _ (fun j _ => (MeasureTheory.Lp.memLp
      (𝓕 (wholeL2Standard n ℂ (hFirstDerivative g j)) : FrequencyL2 n)).norm.integrable_sq)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← l2_norm_sq_integral]
  change ‖(MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ)
    (wholeL2Standard n ℂ (hFirstDerivative g j))‖ ^ 2 = _
  rw [(MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).norm_map,
    (wholeL2Standard n ℂ).norm_map]

/-- The radial input needed for differentiating C(t) has norm bounded by c‖g‖H¹. -/
theorem h1_radial_norm_le {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (g : WholeH1 n ℂ) :
    ‖(h1_radial_memLp c hc g).toLp _‖ ≤ c * ‖g‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  rw [h1_radial_norm_sq c hc g, mul_pow, h1_norm_sq]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) (sq_nonneg c)

def radialH1LM {n : ℕ} (c : ℝ) (hc : 0 ≤ c) :
    WholeH1 n ℂ →ₗ[ℂ] FrequencyL2 n where
  toFun g := (h1_radial_memLp c hc g).toLp _
  map_add' g h := by
    have hF : (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 (g + h))) : FrequencyL2 n) =
        (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g)) : FrequencyL2 n) +
          (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 h)) : FrequencyL2 n) := by
      change (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ) _ = _
      simp only [map_add]
      rfl
    apply MeasureTheory.Lp.ext
    filter_upwards [(h1_radial_memLp c hc (g+h)).coeFn_toLp,
      (h1_radial_memLp c hc g).coeFn_toLp, (h1_radial_memLp c hc h).coeFn_toLp,
      MeasureTheory.Lp.coeFn_add ((h1_radial_memLp c hc g).toLp _)
        ((h1_radial_memLp c hc h).toLp _),
      MeasureTheory.Lp.coeFn_add
        (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g)) : FrequencyL2 n)
        (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 h)) : FrequencyL2 n)] with ξ hgh hg hh ha hfa
    change ((h1_radial_memLp c hc (g+h)).toLp _ : FrequencyL2 n) ξ = _
    rw [ha]
    simp only [Pi.add_apply]
    rw [hgh, hg, hh, hF, hfa]
    simp only [Pi.add_apply, mul_add]
  map_smul' z g := by
    have hF : (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 (z • g))) : FrequencyL2 n) =
        z • (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g)) : FrequencyL2 n) := by
      change (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ) _ = _
      simp only [map_smul]
      rfl
    apply MeasureTheory.Lp.ext
    filter_upwards [(h1_radial_memLp c hc (z • g)).coeFn_toLp,
      (h1_radial_memLp c hc g).coeFn_toLp,
      MeasureTheory.Lp.coeFn_smul z ((h1_radial_memLp c hc g).toLp _),
      MeasureTheory.Lp.coeFn_smul z
        (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g)) : FrequencyL2 n)] with ξ hzg hg ha hfa
    change ((h1_radial_memLp c hc (z • g)).toLp _ : FrequencyL2 n) ξ = _
    simp only [RingHom.id_apply]
    rw [ha]
    simp only [Pi.smul_apply]
    rw [hzg, hg, hF, hfa]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

def radialH1CLM {n : ℕ} (c : ℝ) (hc : 0 ≤ c) :
    WholeH1 n ℂ →L[ℂ] FrequencyL2 n :=
  (radialH1LM c hc).mkContinuous c (h1_radial_norm_le c hc)

theorem radialH1CLM_ae {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (g : WholeH1 n ℂ) :
    (radialH1CLM c hc g : Space n → ℂ) =ᵐ[volume]
      fun ξ => (frequency n c ξ : ℂ) *
        (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g)) : FrequencyL2 n) ξ :=
  (h1_radial_memLp c hc g).coeFn_toLp

theorem radialH1CLM_norm_le {n : ℕ} (c : ℝ) (hc : 0 ≤ c) :
    ‖radialH1CLM (n := n) c hc‖ ≤ c :=
  (radialH1CLM c hc).opNorm_le_bound hc (h1_radial_norm_le c hc)

/-- Time derivative of the cosine family, from the actual shared H¹ graph. -/
def cosineH1Derivative {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (t : ℝ) :
    WholeH1 n ℂ →L[ℂ] WholeL2 n ℂ :=
  (wholeL2Standard n ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((boundedFrequencyMultiplier _ (negativeSineSymbol_memLp n c t)).comp
        (radialH1CLM c hc)))

theorem cosineH1Derivative_fourier {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (t : ℝ)
    (g : WholeH1 n ℂ) :
    (𝓕 (wholeL2Standard n ℂ (cosineH1Derivative c hc t g)) : FrequencyL2 n) =ᵐ[volume]
      fun ξ => (cosineDerivativeSymbol t (frequency n c ξ) : ℂ) *
        (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g)) : FrequencyL2 n) ξ := by
  change ((MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ)
    (wholeL2Standard n ℂ ((wholeL2Standard n ℂ).symm
      ((MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm _))) : Space n → ℂ) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  change (boundedFrequencyMultiplier _ (negativeSineSymbol_memLp n c t)
    (radialH1CLM c hc g) : Space n → ℂ) =ᵐ[volume] _
  filter_upwards [boundedFrequencyMultiplier_ae _ (negativeSineSymbol_memLp n c t)
    (radialH1CLM c hc g), radialH1CLM_ae c hc g] with ξ hξ hr
  rw [hξ, hr]
  simp only [cosineDerivativeSymbol, P201Specs.Wave.cosineDerivativeSymbol]
  push_cast
  ring

theorem cosineH1Derivative_norm_le {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (t : ℝ) :
    ‖cosineH1Derivative (n := n) c hc t‖ ≤ c := by
  have hm : ‖boundedFrequencyMultiplier _ (negativeSineSymbol_memLp n c t)‖ ≤ 1 :=
    boundedFrequencyMultiplier_norm_le _ _ 1 zero_le_one (fun ξ => by
      simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one (t * frequency n c ξ))
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro g
  change ‖(wholeL2Standard n ℂ).symm
    ((MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm
      (boundedFrequencyMultiplier _ (negativeSineSymbol_memLp n c t) (radialH1CLM c hc g)))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖boundedFrequencyMultiplier _ (negativeSineSymbol_memLp n c t)‖ * ‖radialH1CLM c hc g‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖radialH1CLM c hc g‖ := mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    _ ≤ c * ‖g‖ := by
      simp only [one_mul]
      exact h1_radial_norm_le c hc g

theorem cosineH1Derivative_continuous {n : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (g : WholeH1 n ℂ) : Continuous (fun t => cosineH1Derivative c hc t g) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (wholeL2Standard n ℂ).symm.continuous.continuousAt.tendsto.comp
  apply (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm.continuous.continuousAt.tendsto.comp
  apply boundedFrequencyMultiplier_tendsto _ (fun s => negativeSineSymbol_memLp n c s)
    _ (negativeSineSymbol_memLp n c t) 1
  · exact Eventually.of_forall (fun s ξ => by
      simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one (s * frequency n c ξ))
  · intro ξ
    simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one (t * frequency n c ξ)
  · intro ξ
    exact ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp
      (continuous_id.mul_const (frequency n c ξ)))).neg).continuousAt.tendsto

theorem cosineWhole_hasDerivAt {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (t : ℝ)
    (g : WholeH1 n ℂ) :
    HasDerivAt (fun s => (wholeL2Standard n ℂ).symm
      (cosineL2 n c s (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g))))
      (cosineH1Derivative c hc t g) t := by
  obtain ⟨d, hd, hf⟩ := cosineL2_hasDerivAt_weighted n c t
    (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g)) (radialH1CLM c hc g) (radialH1CLM_ae c hc g)
  have he : d = wholeL2Standard n ℂ (cosineH1Derivative c hc t g) := by
    apply (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).injective
    apply MeasureTheory.Lp.ext
    exact hf.trans (cosineH1Derivative_fourier c hc t g).symm
  rw [he] at hd
  have hd' := ((wholeL2Standard n ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s => (wholeL2Standard n ℂ).symm
    (cosineL2 n c s (wholeL2Standard n ℂ (hUnderlying ⊤ 1 g))))
    ((wholeL2Standard n ℂ).symm (wholeL2Standard n ℂ (cosineH1Derivative c hc t g))) t at hd'
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hd'

theorem cosineH1Derivative_zero {n : ℕ} (c : ℝ) (hc : 0 ≤ c) :
    cosineH1Derivative (n := n) c hc 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro g
  apply (wholeL2Standard n ℂ).injective
  apply (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).injective
  have hzero : (𝓕 (wholeL2Standard n ℂ ((0 : WholeH1 n ℂ →L[ℂ] WholeL2 n ℂ) g)) : FrequencyL2 n) = 0 := by
    change (MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ) _ = _
    simp only [zero_apply, map_zero]
  change (𝓕 (wholeL2Standard n ℂ (cosineH1Derivative c hc 0 g)) : FrequencyL2 n) =
    (𝓕 (wholeL2Standard n ℂ ((0 : WholeH1 n ℂ →L[ℂ] WholeL2 n ℂ) g)) : FrequencyL2 n)
  rw [hzero]
  apply MeasureTheory.Lp.ext
  filter_upwards [cosineH1Derivative_fourier c hc 0 g,
    MeasureTheory.Lp.coeFn_zero ℂ 2 (volume : Measure (Space n))] with ξ hξ hz
  rw [hξ, hz]
  simp only [cosineDerivativeSymbol, P201Specs.Wave.cosineDerivativeSymbol,
    zero_mul, Real.sin_zero, mul_zero, Complex.ofReal_zero, Pi.zero_apply]

def coordinateSineSymbol (n : ℕ) (c t : ℝ) (j : Fin n) (ξ : Space n) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) * (sineSymbol t (frequency n c ξ) : ℂ)

lemma coordinateSineSymbol_norm (n : ℕ) (c t : ℝ) (j : Fin n) (ξ : Space n) :
    ‖coordinateSineSymbol n c t j ξ‖ =
      2 * Real.pi * |ξ j| * |sineSymbol t (frequency n c ξ)| := by
  simp [coordinateSineSymbol, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]

lemma coordinateSineSymbol_norm_sq_sum (n : ℕ) (c t : ℝ) (ξ : Space n) :
    (∑ j : Fin n, ‖coordinateSineSymbol n c t j ξ‖ ^ 2) =
      (2 * Real.pi * ‖ξ‖ * sineSymbol t (frequency n c ξ)) ^ 2 := by
  simp_rw [coordinateSineSymbol_norm, mul_pow, sq_abs]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hx := PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin n => ℝ) ξ
  simp only [Real.norm_eq_abs, sq_abs] at hx
  rw [← hx]

lemma sine_radial_bound (n : ℕ) (c t : ℝ) (hc : 0 < c) (ξ : Space n) :
    |2 * Real.pi * ‖ξ‖ * sineSymbol t (frequency n c ξ)| ≤ c⁻¹ := by
  have hb := (scalarBounds t (frequency n c ξ)).2.1
  have hc0 := hc.ne'
  have hid : frequency n c ξ * sineSymbol t (frequency n c ξ) =
      c * (2 * Real.pi * ‖ξ‖ * sineSymbol t (frequency n c ξ)) := by
    unfold frequency P201Specs.Wave.frequency
    ring
  rw [hid, abs_mul, abs_of_pos hc] at hb
  rw [inv_eq_one_div]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb)

lemma coordinateSineSymbol_joint_bound (n : ℕ) (c t : ℝ) (hc : 0 < c) (ξ : Space n) :
    (∑ j : Fin n, ‖coordinateSineSymbol n c t j ξ‖ ^ 2) ≤ c⁻¹ ^ 2 := by
  rw [coordinateSineSymbol_norm_sq_sum]
  have h := (sq_le_sq₀ (abs_nonneg _) (inv_nonneg.mpr hc.le)).mpr (sine_radial_bound n c t hc ξ)
  simpa only [sq_abs] using h

lemma coordinateSineSymbol_bound (n : ℕ) (c t : ℝ) (hc : 0 < c) (j : Fin n) (ξ : Space n) :
    ‖coordinateSineSymbol n c t j ξ‖ ≤ c⁻¹ := by
  apply (sq_le_sq₀ (norm_nonneg _) (inv_nonneg.mpr hc.le)).mp
  exact (Finset.single_le_sum (fun i _ => sq_nonneg ‖coordinateSineSymbol n c t i ξ‖)
    (Finset.mem_univ j)).trans (coordinateSineSymbol_joint_bound n c t hc ξ)

lemma coordinateSineSymbol_memLp (n : ℕ) (c t : ℝ) (hc : 0 < c) (j : Fin n) :
    MemLp (coordinateSineSymbol n c t j) ∞ volume := by
  apply memLp_top_of_bound (by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · fun_prop
    · apply Complex.continuous_ofReal.comp
      exact scalarContinuity.1.comp (show Continuous (fun ξ : Space n => (t, frequency n c ξ)) from by
        unfold frequency P201Specs.Wave.frequency
        fun_prop)) c⁻¹
  exact Eventually.of_forall (coordinateSineSymbol_bound n c t hc j)

lemma boundedFrequencyMultiplier_joint_norm_sq_bound {n : ℕ} {ι : Type*} [Fintype ι]
    (m : ι → Space n → ℂ) (hm : ∀ i, MemLp (m i) ∞ volume)
    (B : ℝ) (hb : ∀ ξ, (∑ i, ‖m i ξ‖ ^ 2) ≤ B)
    (f : FrequencyL2 n) :
    (∑ i, ‖boundedFrequencyMultiplier (m i) (hm i) f‖ ^ 2) ≤ B * ‖f‖ ^ 2 := by
  have hi (i : ι) : Integrable
      (fun ξ => ‖boundedFrequencyMultiplier (m i) (hm i) f ξ‖ ^ 2) volume :=
    (MeasureTheory.Lp.memLp _).norm.integrable_sq
  have hi' (i : ι) : Integrable (fun ξ => ‖m i ξ‖ ^ 2 * ‖f ξ‖ ^ 2) volume := by
    apply (hi i).congr
    filter_upwards [boundedFrequencyMultiplier_ae (m i) (hm i) f] with ξ hξ
    rw [hξ, norm_mul, mul_pow]
  have he (i : ι) : ‖boundedFrequencyMultiplier (m i) (hm i) f‖ ^ 2 =
      ∫ ξ, ‖m i ξ‖ ^ 2 * ‖f ξ‖ ^ 2 := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [boundedFrequencyMultiplier_ae (m i) (hm i) f] with ξ hξ
    rw [hξ, norm_mul, mul_pow]
  simp_rw [he]
  rw [← integral_finsetSum _ (fun i _ => hi' i)]
  rw [l2_norm_sq_integral, ← integral_const_mul]
  apply integral_mono
  · exact integrable_finsetSum _ (fun i _ => hi' i)
  · exact (MeasureTheory.Lp.memLp f).norm.integrable_sq.const_mul B
  · intro ξ
    dsimp only
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hb ξ) (sq_nonneg _)

lemma exists_sine_h1 {n : ℕ} (c t : ℝ) (hc : 0 < c) (f : WholeL2 n ℂ) :
    ∃ g : WholeH1 n ℂ,
      hUnderlying ⊤ 1 g = (wholeL2Standard n ℂ).symm (sineL2 n c t (wholeL2Standard n ℂ f)) ∧
      (∀ j, hFirstDerivative g j = (wholeL2Standard n ℂ).symm
        ((MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm
          (boundedFrequencyMultiplier _ (coordinateSineSymbol_memLp n c t hc j)
            (𝓕 (wholeL2Standard n ℂ f))))) ∧
      ‖g‖ ≤ Real.sqrt (t ^ 2 + c⁻¹ ^ 2) * ‖f‖ := by
  let F := MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ
  let f₀ := (wholeL2Standard n ℂ).symm (sineL2 n c t (wholeL2Standard n ℂ f))
  let v (j : Fin n) : WholeL2 n ℂ := (wholeL2Standard n ℂ).symm
    (F.symm (boundedFrequencyMultiplier _ (coordinateSineSymbol_memLp n c t hc j)
      (𝓕 (wholeL2Standard n ℂ f))))
  have hv (j : Fin n) : P102.U4.distributionPartial ({j} : MultiIndex n)
      (regularDistribution ⊤ f₀) = regularDistribution ⊤ (v j) := by
    rw [← wholeL2Standard_regular f₀, ← wholeL2Standard_regular (v j)]
    apply (weakDerivative_iff_fourier j _ _).mpr
    have hv' : (𝓕 (wholeL2Standard n ℂ (v j)) : FrequencyL2 n) =
      boundedFrequencyMultiplier _ (coordinateSineSymbol_memLp n c t hc j)
        (𝓕 (wholeL2Standard n ℂ f)) := by
      change F ((wholeL2Standard n ℂ) ((wholeL2Standard n ℂ).symm (F.symm _))) = _
      rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
    rw [hv']
    have hf' : wholeL2Standard n ℂ f₀ = sineL2 n c t (wholeL2Standard n ℂ f) :=
      LinearIsometryEquiv.apply_symm_apply _ _
    rw [hf']
    filter_upwards [boundedFrequencyMultiplier_ae _ (coordinateSineSymbol_memLp n c t hc j)
      (𝓕 (wholeL2Standard n ℂ f)),
      fourierMultiplier_ae _ (sineSymbol_memLp n c t) (wholeL2Standard n ℂ f)] with ξ hvξ hfξ
    change (𝓕 (sineL2 n c t (wholeL2Standard n ℂ f)) : FrequencyL2 n) ξ = _ at hfξ
    rw [hvξ, hfξ]
    exact mul_assoc _ _ _
  obtain ⟨g, hg, hgj⟩ := exists_h1_of_weakDerivatives ⊤ f₀ v hv
  refine ⟨g, hg, hgj, ?_⟩
  have hsum : (∑ j : Fin n, ‖v j‖ ^ 2) ≤ c⁻¹ ^ 2 * ‖f‖ ^ 2 := by
    have hh := boundedFrequencyMultiplier_joint_norm_sq_bound
      (coordinateSineSymbol n c t) (coordinateSineSymbol_memLp n c t hc)
      (c⁻¹ ^ 2) (coordinateSineSymbol_joint_bound n c t hc)
      (𝓕 (wholeL2Standard n ℂ f))
    simpa only [v, LinearIsometryEquiv.norm_map, MeasureTheory.Lp.norm_fourier_eq] using hh
  have hbase : ‖f₀‖ ≤ |t| * ‖f‖ := by
    dsimp [f₀]
    rw [LinearIsometryEquiv.norm_map]
    simpa only [LinearIsometryEquiv.norm_map] using
      ContinuousLinearMap.le_of_opNorm_le _ (sineL2_norm_le n c t) (wholeL2Standard n ℂ f)
  have hsq : ‖g‖ ^ 2 ≤ (t ^ 2 + c⁻¹ ^ 2) * ‖f‖ ^ 2 := by
    rw [h1_norm_sq, hg]
    simp_rw [hgj]
    have hh := add_le_add ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbase) hsum
    simpa only [mul_pow, sq_abs, ← add_mul] using hh
  have hh := (sq_le_sq₀ (norm_nonneg g) (by positivity : 0 ≤ Real.sqrt (t ^ 2 + c⁻¹ ^ 2) * ‖f‖)).mp
    (hsq.trans_eq (by rw [mul_pow, Real.sq_sqrt (by positivity)]))
  exact hh

def sineH1Linear (n : ℕ) (c : ℝ) (hc : 0 < c) (t : ℝ) :
    WholeL2 n ℂ →ₗ[ℂ] WholeH1 n ℂ where
  toFun f := (exists_sine_h1 c t hc f).choose
  map_add' f g := by
    apply hilbertUnderlyingInjective ⊤ 1
    change hUnderlying ⊤ 1 (exists_sine_h1 c t hc (f + g)).choose =
      hUnderlying ⊤ 1 ((exists_sine_h1 c t hc f).choose + (exists_sine_h1 c t hc g).choose)
    calc
      _ = (wholeL2Standard n ℂ).symm (sineL2 n c t (wholeL2Standard n ℂ (f + g))) :=
        (exists_sine_h1 c t hc (f + g)).choose_spec.1
      _ = (wholeL2Standard n ℂ).symm (sineL2 n c t (wholeL2Standard n ℂ f)) +
          (wholeL2Standard n ℂ).symm (sineL2 n c t (wholeL2Standard n ℂ g)) := by
        simp only [map_add]
      _ = _ := by rw [map_add, (exists_sine_h1 c t hc f).choose_spec.1,
        (exists_sine_h1 c t hc g).choose_spec.1]
  map_smul' z f := by
    apply hilbertUnderlyingInjective ⊤ 1
    change hUnderlying ⊤ 1 (exists_sine_h1 c t hc (z • f)).choose =
      hUnderlying ⊤ 1 (z • (exists_sine_h1 c t hc f).choose)
    calc
      _ = (wholeL2Standard n ℂ).symm (sineL2 n c t (wholeL2Standard n ℂ (z • f))) :=
        (exists_sine_h1 c t hc (z • f)).choose_spec.1
      _ = z • (wholeL2Standard n ℂ).symm (sineL2 n c t (wholeL2Standard n ℂ f)) := by
        simp only [map_smul]
      _ = _ := by rw [map_smul, (exists_sine_h1 c t hc f).choose_spec.1]

def sineH1 (n : ℕ) (c : ℝ) (hc : 0 < c) (t : ℝ) :
    WholeL2 n ℂ →L[ℂ] WholeH1 n ℂ :=
  (sineH1Linear n c hc t).mkContinuous (Real.sqrt (t ^ 2 + c⁻¹ ^ 2))
    (fun f => (exists_sine_h1 c t hc f).choose_spec.2.2)

theorem sineH1_underlying {n : ℕ} (c : ℝ) (hc : 0 < c) (t : ℝ) (f : WholeL2 n ℂ) :
    hUnderlying ⊤ 1 (sineH1 n c hc t f) =
      (wholeL2Standard n ℂ).symm (sineL2 n c t (wholeL2Standard n ℂ f)) :=
  (exists_sine_h1 c t hc f).choose_spec.1

theorem sineH1_derivative {n : ℕ} (c : ℝ) (hc : 0 < c) (t : ℝ) (f : WholeL2 n ℂ)
    (j : Fin n) :
    hFirstDerivative (sineH1 n c hc t f) j = (wholeL2Standard n ℂ).symm
      ((MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm
        (boundedFrequencyMultiplier _ (coordinateSineSymbol_memLp n c t hc j)
          (𝓕 (wholeL2Standard n ℂ f)))) :=
  (exists_sine_h1 c t hc f).choose_spec.2.1 j

theorem sineH1_norm_le (n : ℕ) (c : ℝ) (hc : 0 < c) (t : ℝ) :
    ‖sineH1 n c hc t‖ ≤ Real.sqrt (t ^ 2 + c⁻¹ ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  exact (exists_sine_h1 c t hc f).choose_spec.2.2

theorem sineH1_zero (n : ℕ) (c : ℝ) (hc : 0 < c) : sineH1 n c hc 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply hilbertUnderlyingInjective ⊤ 1
  rw [sineH1_underlying]
  have hs : sineL2 n c 0 = 0 := sineL2_zero n c
  simp only [hs, zero_apply, map_zero]

theorem coordinateSineMultiplier_continuous {n : ℕ} (c : ℝ) (hc : 0 < c)
    (j : Fin n) (f : FrequencyL2 n) :
    Continuous (fun t => boundedFrequencyMultiplier _ (coordinateSineSymbol_memLp n c t hc j) f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply boundedFrequencyMultiplier_tendsto
    (m := fun s => coordinateSineSymbol n c s j)
    (hm := fun s => coordinateSineSymbol_memLp n c s hc j) (B := c⁻¹)
  · exact Eventually.of_forall (fun s => coordinateSineSymbol_bound n c s hc j)
  · exact coordinateSineSymbol_bound n c t hc j
  · intro ξ
    apply Tendsto.const_mul
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((scalarDerivatives t (frequency n c ξ)).1.continuousAt.tendsto)

theorem sineH1_continuous {n : ℕ} (c : ℝ) (hc : 0 < c) (f : WholeL2 n ℂ) :
    Continuous (fun t => sineH1 n c hc t f) := by
  apply continuous_h1_of_coordinates
  · simpa only [sineH1_underlying, Function.comp_def] using
      (wholeL2Standard n ℂ).symm.continuous.comp (sineL2_continuous n c _)
  · intro j
    simp_rw [sineH1_derivative]
    exact (wholeL2Standard n ℂ).symm.continuous.comp
      ((MeasureTheory.Lp.fourierTransformₗᵢ (Space n) ℂ).symm.continuous.comp
        (coordinateSineMultiplier_continuous c hc j _))

theorem sineH1_underlying_hasDerivAt {n : ℕ} (c : ℝ) (hc : 0 < c) (t : ℝ)
    (f : WholeL2 n ℂ) :
    HasDerivAt (fun s => hUnderlying ⊤ 1 (sineH1 n c hc s f))
      ((wholeL2Standard n ℂ).symm (cosineL2 n c t (wholeL2Standard n ℂ f))) t := by
  let J := (wholeL2Standard n ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have h := J.hasFDerivAt.comp_hasDerivAt t (sineL2_hasDerivAt n c t (wholeL2Standard n ℂ f))
  convert h using 1
  · funext s
    exact sineH1_underlying c hc s f
  · rfl


def complexWaveOperators (n : ℕ) (c : ℝ) (hc : 0 < c) : WaveOperators n ℂ where
  C0 t := wholeFourierMultiplier _ (cosineSymbol_memLp n c t)
  C1 t := cosineH1 n c t
  S t := sineH1 n c hc t
  D t := cosineH1Derivative c hc.le t

theorem complexWaveFamilyLaws (n : ℕ) (c : ℝ) (hc : 0 < c) :
    WaveFamilyLaws c (ContinuousLinearMap.id ℝ ℂ) (complexWaveOperators n c hc) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t f
    simp only [embeddedFourier_complex]
    change (𝓕 (wholeL2Standard n ℂ (wholeFourierMultiplier _ (cosineSymbol_memLp n c t) f)) : FrequencyL2 n) =ᵐ[volume] _
    rw [wholeFourierMultiplier_standard]
    exact fourierMultiplier_ae _ _ _
  · intro t g
    exact cosineH1_underlying c t g
  · intro t f
    simp only [embeddedFourier_complex]
    change (𝓕 (wholeL2Standard n ℂ (hUnderlying ⊤ 1 (sineH1 n c hc t f))) : FrequencyL2 n) =ᵐ[volume] _
    rw [sineH1_underlying, LinearIsometryEquiv.apply_symm_apply]
    exact fourierMultiplier_ae _ _ _
  · intro t g
    simp only [embeddedFourier_complex]
    exact cosineH1Derivative_fourier c hc.le t g
  · intro t
    refine ⟨?_, cosineH1_norm_le n c t, sineH1_norm_le n c hc t,
      cosineH1Derivative_norm_le c hc.le t⟩
    apply wholeFourierMultiplier_norm_le _ _ 1 zero_le_one
    intro ξ
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (scalarBounds t (frequency n c ξ)).2.2
  · exact fun f => wholeCosine_continuous c f
  · exact fun g => cosineH1_continuous c g
  · exact fun f => sineH1_continuous c hc f
  · exact fun g => cosineH1Derivative_continuous c hc.le g
  · intro t g
    change HasDerivAt (fun s => hUnderlying ⊤ 1 (cosineH1 n c s g))
      (cosineH1Derivative c hc.le t g) t
    convert cosineWhole_hasDerivAt c hc.le t g using 1
    funext s
    exact cosineH1_underlying c s g
  · exact fun t f => sineH1_underlying_hasDerivAt c hc t f
  · exact wholeCosine_zero n c
  · exact cosineH1_zero n c
  · exact sineH1_zero n c hc
  · exact cosineH1Derivative_zero c hc.le

theorem complexWaveMultipliers (n : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ W : WaveOperators n ℂ, WaveFamilyLaws c (ContinuousLinearMap.id ℝ ℂ) W :=
  ⟨complexWaveOperators n c hc, complexWaveFamilyLaws n c hc⟩

end P201.Wave


open MeasureTheory Filter FourierTransform
open scoped FourierTransform
namespace P201.Wave.RealBridge
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def conjL2 : MeasureTheory.Lp (α := E) ℂ 2 volume →L[ℝ] MeasureTheory.Lp (α := E) ℂ 2 volume :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 volume

def reflectL2 : MeasureTheory.Lp (α := E) ℂ 2 volume →L[ℂ] MeasureTheory.Lp (α := E) ℂ 2 volume :=
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (LinearIsometryEquiv.neg ℝ)
    (LinearIsometryEquiv.neg ℝ (E := E)).measurePreserving).toContinuousLinearMap

def conjSchwartz (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f

def reflectSchwartz (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := E)).toContinuousLinearEquiv f

theorem conjSchwartz_fourier (f : SchwartzMap E ℂ) :
    𝓕 (conjSchwartz f) = reflectSchwartz (conjSchwartz (𝓕 f)) := by
  ext ξ
  change 𝓕 (fun x => starRingEnd ℂ (f x)) ξ = starRingEnd ℂ (𝓕 (f : E → ℂ) (-ξ))
  rw [Real.fourier_eq, Real.fourier_eq]
  change _ = Complex.conjCLE (∫ v : E, 𝐞 (-inner ℝ v (-ξ)) • f v)
  rw [← Complex.conjCLE.integral_comp_comm]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Circle.smul_def, ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]

theorem conjL2_schwartz (f : SchwartzMap E ℂ) :
    conjL2 (f.toLp 2) = (conjSchwartz f).toLp 2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [(Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLp (f.toLp 2),
    f.coeFn_toLp (p := 2), (conjSchwartz f).coeFn_toLp (p := 2)] with x h₁ h₂ h₃
  change (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp (f.toLp 2) x = _
  rw [h₁, h₂, h₃]
  rfl

theorem reflectL2_schwartz (f : SchwartzMap E ℂ) :
    reflectL2 (f.toLp 2) = (reflectSchwartz f).toLp 2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_compMeasurePreserving (f.toLp 2)
      (LinearIsometryEquiv.neg ℝ (E := E)).measurePreserving,
    ((LinearIsometryEquiv.neg ℝ (E := E)).measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (f.coeFn_toLp (p := 2))),
    (reflectSchwartz f).coeFn_toLp (p := 2)] with x h₁ h₂ h₃
  change MeasureTheory.Lp.compMeasurePreserving _ _ (f.toLp 2) x = _
  rw [h₁, h₂, h₃]
  rfl

theorem fourier_conjL2 (f : MeasureTheory.Lp (α := E) ℂ 2 volume) :
    𝓕 (conjL2 f) = reflectL2 (conjL2 (𝓕 f)) := by
  set p := fun f : MeasureTheory.Lp (α := E) ℂ 2 volume =>
    𝓕 (conjL2 f) = reflectL2 (conjL2 (𝓕 f))
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (MeasureTheory.Lp.fourierTransformₗᵢ E ℂ).continuous.comp conjL2.continuous
    · exact reflectL2.continuous.comp (conjL2.continuous.comp (MeasureTheory.Lp.fourierTransformₗᵢ E ℂ).continuous)
  intro φ
  change 𝓕 (conjL2 (φ.toLp 2)) = reflectL2 (conjL2 (𝓕 (φ.toLp 2)))
  rw [conjL2_schwartz, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq,
    conjL2_schwartz, reflectL2_schwartz, conjSchwartz_fourier]


theorem conjL2_ae (f : MeasureTheory.Lp (α := E) ℂ 2 volume) :
    (conjL2 f : E → ℂ) =ᵐ[volume] fun x => starRingEnd ℂ (f x) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLp f

theorem reflectL2_ae (f : MeasureTheory.Lp (α := E) ℂ 2 volume) :
    (reflectL2 f : E → ℂ) =ᵐ[volume] fun x => f (-x) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving f _

theorem fourier_conjL2_ae (f : MeasureTheory.Lp (α := E) ℂ 2 volume) :
    (𝓕 (conjL2 f) : MeasureTheory.Lp (α := E) ℂ 2 volume) =ᵐ[volume]
      fun x => starRingEnd ℂ ((𝓕 f : MeasureTheory.Lp (α := E) ℂ 2 volume) (-x)) := by
  rw [fourier_conjL2]
  exact (reflectL2_ae _).trans
    ((LinearIsometryEquiv.neg ℝ (E := E)).measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (conjL2_ae _))

/-- A bounded Fourier multiplier with real even symbol commutes with conjugation. -/
theorem commutes_conj_of_real_even_symbol
    (T : MeasureTheory.Lp (α := E) ℂ 2 volume →L[ℂ] MeasureTheory.Lp (α := E) ℂ 2 volume)
    (m : E → ℝ) (hm : ∀ x, m (-x) = m x)
    (hT : ∀ f : MeasureTheory.Lp (α := E) ℂ 2 volume,
      (𝓕 (T f) : MeasureTheory.Lp (α := E) ℂ 2 volume) =ᵐ[volume]
        fun x => (m x : ℂ) * (𝓕 f : MeasureTheory.Lp (α := E) ℂ 2 volume) x)
    (f : MeasureTheory.Lp (α := E) ℂ 2 volume) : conjL2 (T f) = T (conjL2 f) := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ E ℂ).injective
  apply MeasureTheory.Lp.ext
  filter_upwards [fourier_conjL2_ae (T f), hT (conjL2 f),
    fourier_conjL2_ae f,
    ((LinearIsometryEquiv.neg ℝ (E := E)).measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (hT f))] with x h₁ h₂ h₃ h₄
  change (𝓕 (conjL2 (T f)) : MeasureTheory.Lp (α := E) ℂ 2 volume) x =
    (𝓕 (T (conjL2 f)) : MeasureTheory.Lp (α := E) ℂ 2 volume) x
  change (𝓕 (T f) : MeasureTheory.Lp (α := E) ℂ 2 volume) (-x) =
    (m (-x) : ℂ) * (𝓕 f : MeasureTheory.Lp (α := E) ℂ 2 volume) (-x) at h₄
  rw [h₁, h₂, h₃, h₄, map_mul, Complex.conj_ofReal, hm]

/-- A real input remains real under any real even Fourier symbol, including
symbols whose action is only defined on a domain. -/
theorem conj_eq_of_real_even_symbol
    (m : E → ℝ) (hm : ∀ x, m (-x) = m x)
    (f d : MeasureTheory.Lp (α := E) ℂ 2 volume) (hf : conjL2 f = f)
    (hd : (𝓕 d : MeasureTheory.Lp (α := E) ℂ 2 volume) =ᵐ[volume]
      fun x => (m x : ℂ) * (𝓕 f : MeasureTheory.Lp (α := E) ℂ 2 volume) x) : conjL2 d = d := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ E ℂ).injective
  change 𝓕 (conjL2 d) = 𝓕 d
  apply MeasureTheory.Lp.ext
  have hf' := fourier_conjL2_ae f
  rw [hf] at hf'
  filter_upwards [fourier_conjL2_ae d, hd, hf',
    ((LinearIsometryEquiv.neg ℝ (E := E)).measurePreserving.quasiMeasurePreserving.ae_eq_comp hd)]
    with x hd₁ hd₂ hf₁ hd₃
  change (𝓕 d : MeasureTheory.Lp (α := E) ℂ 2 volume) (-x) =
    (m (-x) : ℂ) * (𝓕 f : MeasureTheory.Lp (α := E) ℂ 2 volume) (-x) at hd₃
  rw [hd₁, hd₂, hf₁, hd₃, map_mul, Complex.conj_ofReal, hm]

/-- Inclusion of real-valued L² functions. -/
def ofRealL2 : MeasureTheory.Lp (α := E) ℝ 2 volume →L[ℝ] MeasureTheory.Lp (α := E) ℂ 2 volume :=
  Complex.ofRealCLM.compLpL 2 volume

def reL2 : MeasureTheory.Lp (α := E) ℂ 2 volume →L[ℝ] MeasureTheory.Lp (α := E) ℝ 2 volume :=
  Complex.reCLM.compLpL 2 volume

theorem reL2_ofRealL2 (f : MeasureTheory.Lp (α := E) ℝ 2 volume) : reL2 (ofRealL2 f) = f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLp (ofRealL2 f),
    Complex.ofRealCLM.coeFn_compLp f] with x hr ho
  change Complex.reCLM.compLp (ofRealL2 f) x = _
  change ofRealL2 f x = Complex.ofRealCLM (f x) at ho
  rw [hr, ho]
  rfl

theorem ofRealL2_norm (f : MeasureTheory.Lp (α := E) ℝ 2 volume) : ‖ofRealL2 f‖ = ‖f‖ := by
  have h : ∀ᵐ x ∂volume, ‖ofRealL2 f x‖ = ‖f x‖ := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx
    change ‖Complex.ofRealCLM.compLp f x‖ = _
    rw [hx]
    exact Complex.norm_real _
  exact le_antisymm (MeasureTheory.Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.le))
    (MeasureTheory.Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.ge))

theorem conjL2_ofRealL2 (f : MeasureTheory.Lp (α := E) ℝ 2 volume) : conjL2 (ofRealL2 f) = ofRealL2 f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [conjL2_ae (ofRealL2 f), Complex.ofRealCLM.coeFn_compLp f] with x hc ho
  rw [hc]
  change starRingEnd ℂ (Complex.ofRealCLM.compLp f x) = Complex.ofRealCLM.compLp f x
  rw [ho]
  exact Complex.conj_ofReal _

theorem ofRealL2_reL2_of_conj_eq (f : MeasureTheory.Lp (α := E) ℂ 2 volume)
    (hf : conjL2 f = f) : ofRealL2 (reL2 f) = f := by
  apply MeasureTheory.Lp.ext
  have hc : (fun x => starRingEnd ℂ (f x)) =ᵐ[volume] f := by
    simpa only [hf] using (conjL2_ae f).symm
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (reL2 f),
    Complex.reCLM.coeFn_compLp f, hc] with x ho hr hc
  change Complex.ofRealCLM.compLp (reL2 f) x = _
  rw [ho]
  change ((reL2 f x : ℝ) : ℂ) = _
  change reL2 f x = Complex.reCLM (f x) at hr
  rw [hr]
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im hc
    simp only [Complex.conj_im] at h
    change 0 = (f x).im
    linarith

/-- Actual restriction of a conjugation-preserving complex operator. -/
def realRestriction (T : MeasureTheory.Lp (α := E) ℂ 2 volume →L[ℂ] MeasureTheory.Lp (α := E) ℂ 2 volume) :
    MeasureTheory.Lp (α := E) ℝ 2 volume →L[ℝ] MeasureTheory.Lp (α := E) ℝ 2 volume :=
  reL2 ∘L T.restrictScalars ℝ ∘L ofRealL2

theorem ofRealL2_realRestriction
    (T : MeasureTheory.Lp (α := E) ℂ 2 volume →L[ℂ] MeasureTheory.Lp (α := E) ℂ 2 volume)
    (hT : ∀ f, conjL2 (T f) = T (conjL2 f))
    (f : MeasureTheory.Lp (α := E) ℝ 2 volume) :
    ofRealL2 (realRestriction T f) = T (ofRealL2 f) := by
  change ofRealL2 (reL2 (T (ofRealL2 f))) = _
  apply ofRealL2_reL2_of_conj_eq
  rw [hT, conjL2_ofRealL2]

end P201.Wave.RealBridge

open MeasureTheory Set Filter
open P201 P201.Wave
open P201Specs.Wave (WholeL2 WholeH1)
namespace P201.Wave.RealBridge
variable {n : ℕ} (Ω : Domain n)

theorem testPartial_postcomp {𝕜 𝕜' : Type} [RCLike 𝕜] [RCLike 𝕜']
    (L : 𝕜 →L[ℝ] 𝕜') (j : Fin n) (φ : P102.U4.TestSpace 𝕜 Ω) :
    P102.U4.testPartialWord Ω [j] (TestFunction.postcompCLM L φ) =
      TestFunction.postcompCLM L (P102.U4.testPartialWord Ω [j] φ) := by
  ext x
  simp only [TestFunction.postcompCLM_apply, Function.comp_apply]
  simp only [P102.U4.testPartialWord_coe, P102.U4.partialWord]
  change fderiv ℝ (L ∘ φ) x (P102.U4.coordinateVector n j) =
    L (fderiv ℝ φ x (P102.U4.coordinateVector n j))
  rw [(L.hasFDerivAt.comp x
    (φ.contDiff.differentiable (by simp) x).hasFDerivAt).fderiv]
  rfl

def ofRealLp : Lp ℝ Ω 2 →L[ℝ] Lp ℂ Ω 2 :=
  Complex.ofRealCLM.compLpL 2 (domainMeasure Ω)

def reLp : Lp ℂ Ω 2 →L[ℝ] Lp ℝ Ω 2 :=
  Complex.reCLM.compLpL 2 (domainMeasure Ω)

theorem ofRealLp_ae (f : Lp ℝ Ω 2) :
    (ofRealLp Ω f : Space n → ℂ) =ᵐ[domainMeasure Ω] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLp f

theorem reLp_ae (f : Lp ℂ Ω 2) :
    (reLp Ω f : Space n → ℝ) =ᵐ[domainMeasure Ω] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLp f

theorem integrable_lp_test {𝕜 : Type} [RCLike 𝕜]
    (f : Lp 𝕜 Ω 2) (φ : P102.U4.TestSpace 𝕜 Ω) :
    Integrable (fun x => f x * φ x) (domainMeasure Ω) :=
  (MeasureTheory.Lp.memLp f).integrable_mul
    (show MemLp (⇑φ) 2 (domainMeasure Ω) from
      φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)

theorem ofRealLp_pairing_re (f : Lp ℝ Ω 2) (φ : P102.U4.TestSpace ℂ Ω) :
    (P102.U4.lpTestPairing Ω 2 φ (ofRealLp Ω f)).re =
      P102.U4.lpTestPairing Ω 2 (P102.U4.realPart Ω φ) f := by
  rw [P102.U4.lpTestPairing_eq_integral, P102.U4.lpTestPairing_eq_integral]
  change RCLike.re (∫ x, ofRealLp Ω f x * φ x ∂domainMeasure Ω) =
    ∫ x, f x * P102.U4.realPart Ω φ x ∂domainMeasure Ω
  rw [← integral_re (integrable_lp_test Ω (ofRealLp Ω f) φ)]
  apply integral_congr_ae
  filter_upwards [ofRealLp_ae Ω f] with x hx
  simp [hx, P102.U4.realPart_apply, Complex.mul_re]

theorem ofRealLp_pairing_im (f : Lp ℝ Ω 2) (φ : P102.U4.TestSpace ℂ Ω) :
    (P102.U4.lpTestPairing Ω 2 φ (ofRealLp Ω f)).im =
      P102.U4.lpTestPairing Ω 2 (P102.U4.imagPart Ω φ) f := by
  rw [P102.U4.lpTestPairing_eq_integral, P102.U4.lpTestPairing_eq_integral]
  change RCLike.im (∫ x, ofRealLp Ω f x * φ x ∂domainMeasure Ω) =
    ∫ x, f x * P102.U4.imagPart Ω φ x ∂domainMeasure Ω
  rw [← integral_im (integrable_lp_test Ω (ofRealLp Ω f) φ)]
  apply integral_congr_ae
  filter_upwards [ofRealLp_ae Ω f] with x hx
  simp [hx, P102.U4.imagPart_apply, Complex.mul_im]

theorem reLp_pairing (f : Lp ℂ Ω 2) (φ : P102.U4.TestSpace ℝ Ω) :
    P102.U4.lpTestPairing Ω 2 φ (reLp Ω f) =
      (P102.U4.lpTestPairing Ω 2 (P102.U4.complexifyTest Ω φ) f).re := by
  rw [P102.U4.lpTestPairing_eq_integral, P102.U4.lpTestPairing_eq_integral]
  change (∫ x, reLp Ω f x * φ x ∂domainMeasure Ω) =
    RCLike.re (∫ x, f x * P102.U4.complexifyTest Ω φ x ∂domainMeasure Ω)
  rw [← integral_re (integrable_lp_test Ω f (P102.U4.complexifyTest Ω φ))]
  apply integral_congr_ae
  filter_upwards [reLp_ae Ω f] with x hx
  simp [hx, P102.U4.complexifyTest_apply, Complex.mul_re]

theorem ofRealLp_weakDerivative (j : Fin n) (f v : Lp ℝ Ω 2)
    (hv : distributionDerivative ({j} : MultiIndex n) (regularDistribution Ω f) =
      regularDistribution Ω v) :
    distributionDerivative ({j} : MultiIndex n) (regularDistribution Ω (ofRealLp Ω f)) =
      regularDistribution Ω (ofRealLp Ω v) := by
  apply (P102.U4.distributionPartial_eq_regularLp_iff Ω 2 _ _ _).mpr
  intro φ
  have h := (P102.U4.distributionPartial_eq_regularLp_iff Ω 2 _ _ _).mp hv
  simp only [Multiset.card_singleton, Multiset.sort_singleton, pow_one, neg_one_mul] at h ⊢
  apply Complex.ext
  · simp only [Complex.neg_re, ofRealLp_pairing_re]
    simpa only [P102.U4.realPart, testPartial_postcomp] using h (P102.U4.realPart Ω φ)
  · simp only [Complex.neg_im, ofRealLp_pairing_im]
    simpa only [P102.U4.imagPart, testPartial_postcomp] using h (P102.U4.imagPart Ω φ)

theorem reLp_weakDerivative (j : Fin n) (f v : Lp ℂ Ω 2)
    (hv : distributionDerivative ({j} : MultiIndex n) (regularDistribution Ω f) =
      regularDistribution Ω v) :
    distributionDerivative ({j} : MultiIndex n) (regularDistribution Ω (reLp Ω f)) =
      regularDistribution Ω (reLp Ω v) := by
  apply (P102.U4.distributionPartial_eq_regularLp_iff Ω 2 _ _ _).mpr
  intro φ
  have h := (P102.U4.distributionPartial_eq_regularLp_iff Ω 2 _ _ _).mp hv
    (P102.U4.complexifyTest Ω φ)
  simp only [Multiset.card_singleton, Multiset.sort_singleton, pow_one, neg_one_mul] at h ⊢
  rw [reLp_pairing, reLp_pairing]
  unfold P102.U4.complexifyTest at h ⊢
  rw [testPartial_postcomp Ω Complex.ofRealCLM] at h
  exact congrArg Complex.re h

end P201.Wave.RealBridge

open MeasureTheory Set Filter
open P201 P201.Wave
open P201Specs.Wave (WholeL2 WholeH1)
namespace P201.Wave.RealBridge
variable {n : ℕ} (Ω : Domain n)

lemma ofRealLp_norm (f : Lp ℝ Ω 2) : ‖ofRealLp Ω f‖ = ‖f‖ := by
  have h : ∀ᵐ x ∂domainMeasure Ω, ‖ofRealLp Ω f x‖ = ‖f x‖ := by
    filter_upwards [ofRealLp_ae Ω f] with x hx
    rw [hx]
    exact Complex.norm_real _
  exact le_antisymm (MeasureTheory.Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.le))
    (MeasureTheory.Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.ge))

lemma reLp_norm_le (f : Lp ℂ Ω 2) : ‖reLp Ω f‖ ≤ ‖f‖ := by
  apply MeasureTheory.Lp.norm_le_norm_of_ae_le
  filter_upwards [reLp_ae Ω f] with x hx
  rw [hx, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

lemma reLp_ofRealLp (f : Lp ℝ Ω 2) : reLp Ω (ofRealLp Ω f) = f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [reLp_ae Ω (ofRealLp Ω f), ofRealLp_ae Ω f] with x hr ho
  rw [hr, ho]
  rfl

lemma exists_ofRealH1 (g : H ℝ Ω 1) :
    ∃ u : H ℂ Ω 1,
      hUnderlying Ω 1 u = ofRealLp Ω (hUnderlying Ω 1 g) ∧
      ∀ j, hFirstDerivative u j = ofRealLp Ω (hFirstDerivative g j) := by
  apply exists_h1_of_weakDerivatives
  intro j
  apply ofRealLp_weakDerivative
  exact hilbertDerivativeDistribution Ω 1 g ⟨{j}, by simp⟩

lemma exists_reH1 (g : H ℂ Ω 1) :
    ∃ u : H ℝ Ω 1,
      hUnderlying Ω 1 u = reLp Ω (hUnderlying Ω 1 g) ∧
      ∀ j, hFirstDerivative u j = reLp Ω (hFirstDerivative g j) := by
  apply exists_h1_of_weakDerivatives
  intro j
  apply reLp_weakDerivative
  exact hilbertDerivativeDistribution Ω 1 g ⟨{j}, by simp⟩

def ofRealH1Value (g : H ℝ Ω 1) : H ℂ Ω 1 := (exists_ofRealH1 Ω g).choose

def reH1Value (g : H ℂ Ω 1) : H ℝ Ω 1 := (exists_reH1 Ω g).choose

lemma ofRealH1Value_underlying (g : H ℝ Ω 1) :
    hUnderlying Ω 1 (ofRealH1Value Ω g) = ofRealLp Ω (hUnderlying Ω 1 g) :=
  (exists_ofRealH1 Ω g).choose_spec.1

lemma ofRealH1Value_derivative (g : H ℝ Ω 1) (j : Fin n) :
    hFirstDerivative (ofRealH1Value Ω g) j = ofRealLp Ω (hFirstDerivative g j) :=
  (exists_ofRealH1 Ω g).choose_spec.2 j

lemma reH1Value_underlying (g : H ℂ Ω 1) :
    hUnderlying Ω 1 (reH1Value Ω g) = reLp Ω (hUnderlying Ω 1 g) :=
  (exists_reH1 Ω g).choose_spec.1

lemma reH1Value_derivative (g : H ℂ Ω 1) (j : Fin n) :
    hFirstDerivative (reH1Value Ω g) j = reLp Ω (hFirstDerivative g j) :=
  (exists_reH1 Ω g).choose_spec.2 j

lemma hUnderlying_map_real_smul (z : ℝ) (g : H ℂ Ω 1) :
    hUnderlying Ω 1 (z • g) = z • hUnderlying Ω 1 g :=
  ((hUnderlying Ω 1).restrictScalars ℝ).map_smul z g

def ofRealH1Linear : H ℝ Ω 1 →ₗ[ℝ] H ℂ Ω 1 where
  toFun := ofRealH1Value Ω
  map_add' g h := by
    apply hilbertUnderlyingInjective Ω 1
    change hUnderlying Ω 1 (ofRealH1Value Ω (g + h)) =
      hUnderlying Ω 1 (ofRealH1Value Ω g + ofRealH1Value Ω h)
    rw [map_add, ofRealH1Value_underlying, ofRealH1Value_underlying, ofRealH1Value_underlying]
    simp only [map_add]
  map_smul' z g := by
    apply hilbertUnderlyingInjective Ω 1
    change hUnderlying Ω 1 (ofRealH1Value Ω (z • g)) =
      hUnderlying Ω 1 (z • ofRealH1Value Ω g)
    rw [ofRealH1Value_underlying]
    simp only [map_smul, hUnderlying_map_real_smul, ofRealH1Value_underlying]

def reH1Linear : H ℂ Ω 1 →ₗ[ℝ] H ℝ Ω 1 where
  toFun := reH1Value Ω
  map_add' g h := by
    apply hilbertUnderlyingInjective Ω 1
    change hUnderlying Ω 1 (reH1Value Ω (g + h)) =
      hUnderlying Ω 1 (reH1Value Ω g + reH1Value Ω h)
    rw [map_add, reH1Value_underlying, reH1Value_underlying, reH1Value_underlying]
    simp only [map_add]
  map_smul' z g := by
    apply hilbertUnderlyingInjective Ω 1
    change hUnderlying Ω 1 (reH1Value Ω (z • g)) =
      hUnderlying Ω 1 (z • reH1Value Ω g)
    rw [reH1Value_underlying]
    simp only [map_smul, hUnderlying_map_real_smul, reH1Value_underlying]

lemma ofRealH1Value_norm (g : H ℝ Ω 1) : ‖ofRealH1Value Ω g‖ = ‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [h1_norm_sq, ofRealH1Value_underlying, ofRealLp_norm, h1_norm_sq]
  simp only [ofRealH1Value_derivative, ofRealLp_norm]

lemma reH1Value_norm_le (g : H ℂ Ω 1) : ‖reH1Value Ω g‖ ≤ ‖g‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [h1_norm_sq, reH1Value_underlying, h1_norm_sq]
  simp only [reH1Value_derivative]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (reLp_norm_le Ω _) 2)
    (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (reLp_norm_le Ω _) 2)

def ofRealH1 : H ℝ Ω 1 →L[ℝ] H ℂ Ω 1 :=
  (ofRealH1Linear Ω).mkContinuous 1 (fun g => by
    change ‖ofRealH1Value Ω g‖ ≤ 1 * ‖g‖
    rw [ofRealH1Value_norm, one_mul])

def reH1 : H ℂ Ω 1 →L[ℝ] H ℝ Ω 1 :=
  (reH1Linear Ω).mkContinuous 1 (fun g => by
    change ‖reH1Value Ω g‖ ≤ 1 * ‖g‖
    simpa only [one_mul] using reH1Value_norm_le Ω g)

lemma ofRealH1_underlying (g : H ℝ Ω 1) :
    hUnderlying Ω 1 (ofRealH1 Ω g) = ofRealLp Ω (hUnderlying Ω 1 g) :=
  ofRealH1Value_underlying Ω g

lemma ofRealH1_derivative (g : H ℝ Ω 1) (j : Fin n) :
    hFirstDerivative (ofRealH1 Ω g) j = ofRealLp Ω (hFirstDerivative g j) :=
  ofRealH1Value_derivative Ω g j

lemma reH1_underlying (g : H ℂ Ω 1) :
    hUnderlying Ω 1 (reH1 Ω g) = reLp Ω (hUnderlying Ω 1 g) :=
  reH1Value_underlying Ω g

lemma reH1_derivative (g : H ℂ Ω 1) (j : Fin n) :
    hFirstDerivative (reH1 Ω g) j = reLp Ω (hFirstDerivative g j) :=
  reH1Value_derivative Ω g j

lemma ofRealH1_norm (g : H ℝ Ω 1) : ‖ofRealH1 Ω g‖ = ‖g‖ := ofRealH1Value_norm Ω g

lemma reH1_norm_le (g : H ℂ Ω 1) : ‖reH1 Ω g‖ ≤ ‖g‖ := reH1Value_norm_le Ω g

lemma reH1_ofRealH1 (g : H ℝ Ω 1) : reH1 Ω (ofRealH1 Ω g) = g := by
  apply hilbertUnderlyingInjective Ω 1
  change hUnderlying Ω 1 (reH1 Ω (ofRealH1 Ω g)) = hUnderlying Ω 1 g
  rw [reH1_underlying, ofRealH1_underlying, reLp_ofRealLp]

lemma ofRealH1_injective : Function.Injective (ofRealH1 Ω) := by
  intro g h he
  have hh := congrArg (reH1 Ω) he
  simpa only [reH1_ofRealH1] using hh

lemma ofRealLp_injective : Function.Injective (ofRealLp Ω) := by
  intro g h he
  have hh := congrArg (reLp Ω) he
  simpa only [reLp_ofRealLp] using hh

lemma ofRealH1_reH1_of_underlying (g : H ℂ Ω 1)
    (hg : ofRealLp Ω (reLp Ω (hUnderlying Ω 1 g)) = hUnderlying Ω 1 g) :
    ofRealH1 Ω (reH1 Ω g) = g := by
  apply hilbertUnderlyingInjective Ω 1
  change hUnderlying Ω 1 (ofRealH1 Ω (reH1 Ω g)) = hUnderlying Ω 1 g
  rw [ofRealH1_underlying, reH1_underlying, hg]

end P201.Wave.RealBridge


open MeasureTheory Filter
open scoped FourierTransform
namespace P201.Wave.RealBridge

section Transfers
variable {XR XC YR YC : Type*}
  [NormedAddCommGroup XR] [NormedSpace ℝ XR]
  [NormedAddCommGroup XC] [NormedSpace ℝ XC]
  [NormedAddCommGroup YR] [NormedSpace ℝ YR]
  [NormedAddCommGroup YC] [NormedSpace ℝ YC]

/-- Restrict a real-linear operator along an inclusion and a projection. -/
def projectedOperator (ι : XR →L[ℝ] XC) (p : YC →L[ℝ] YR)
    (T : XC →L[ℝ] YC) : XR →L[ℝ] YR := p.comp (T.comp ι)

@[simp] theorem projectedOperator_apply (ι : XR →L[ℝ] XC) (p : YC →L[ℝ] YR)
    (T : XC →L[ℝ] YC) (x : XR) : projectedOperator ι p T x = p (T (ι x)) := rfl

theorem projectedOperator_norm_le (ι : XR →L[ℝ] XC) (p : YC →L[ℝ] YR)
    (hι : ∀ x, ‖ι x‖ ≤ ‖x‖) (hp : ∀ y, ‖p y‖ ≤ ‖y‖) (T : XC →L[ℝ] YC) :
    ‖projectedOperator ι p T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖projectedOperator ι p T x‖ ≤ ‖T (ι x)‖ := hp _
    _ ≤ ‖T‖ * ‖ι x‖ := T.le_opNorm _
    _ ≤ ‖T‖ * ‖x‖ := mul_le_mul_of_nonneg_left (hι x) (norm_nonneg _)

theorem projectedOperator_continuous (ι : XR →L[ℝ] XC) (p : YC →L[ℝ] YR)
    (T : ℝ → XC →L[ℝ] YC) (hT : ∀ x, Continuous (fun t => T t x)) (x : XR) :
    Continuous (fun t => projectedOperator ι p (T t) x) :=
  p.continuous.comp (hT (ι x))

theorem projectedOperator_hasDerivAt (ι : XR →L[ℝ] XC) (p : YC →L[ℝ] YR)
    (T : ℝ → XC →L[ℝ] YC) (D : XC →L[ℝ] YC) (t : ℝ)
    (hT : ∀ x, HasDerivAt (fun s => T s x) (D x) t) (x : XR) :
    HasDerivAt (fun s => projectedOperator ι p (T s) x)
      (projectedOperator ι p D x) t :=
  p.hasFDerivAt.comp_hasDerivAt t (hT (ι x))

@[simp] theorem projectedOperator_zero (ι : XR →L[ℝ] XC) (p : YC →L[ℝ] YR) :
    projectedOperator ι p (0 : XC →L[ℝ] YC) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [projectedOperator_apply, zero_apply, map_zero]

end Transfers

section StandardL2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem reL2_norm_le (f : MeasureTheory.Lp (α := E) ℂ 2 volume) : ‖reL2 f‖ ≤ ‖f‖ := by
  apply MeasureTheory.Lp.norm_le_norm_of_ae_le
  filter_upwards [Complex.reCLM.coeFn_compLp f] with x hx
  change ‖Complex.reCLM.compLp f x‖ ≤ ‖f x‖
  rw [hx]
  exact Complex.abs_re_le_norm (f x)

theorem realRestriction_norm_le
    (T : MeasureTheory.Lp (α := E) ℂ 2 volume →L[ℂ] MeasureTheory.Lp (α := E) ℂ 2 volume) :
    ‖realRestriction T‖ ≤ ‖T‖ := by
  change ‖projectedOperator ofRealL2 reL2 (T.restrictScalars ℝ)‖ ≤ _
  have h := projectedOperator_norm_le ofRealL2 reL2
    (fun f => (ofRealL2_norm f).le) reL2_norm_le (T.restrictScalars ℝ)
  exact h.trans (le_of_eq T.norm_restrictScalars)

theorem realRestriction_continuous
    (T : ℝ → MeasureTheory.Lp (α := E) ℂ 2 volume →L[ℂ] MeasureTheory.Lp (α := E) ℂ 2 volume)
    (hT : ∀ f, Continuous (fun t => T t f)) (f : MeasureTheory.Lp (α := E) ℝ 2 volume) :
    Continuous (fun t => realRestriction (T t) f) :=
  projectedOperator_continuous ofRealL2 reL2 (fun t => (T t).restrictScalars ℝ) hT f

theorem realRestriction_hasDerivAt
    (T : ℝ → MeasureTheory.Lp (α := E) ℂ 2 volume →L[ℂ] MeasureTheory.Lp (α := E) ℂ 2 volume)
    (D : MeasureTheory.Lp (α := E) ℂ 2 volume →L[ℂ] MeasureTheory.Lp (α := E) ℂ 2 volume) (t : ℝ)
    (hT : ∀ f, HasDerivAt (fun s => T s f) (D f) t) (f : MeasureTheory.Lp (α := E) ℝ 2 volume) :
    HasDerivAt (fun s => realRestriction (T s) f) (realRestriction D f) t :=
  projectedOperator_hasDerivAt ofRealL2 reL2 (fun s => (T s).restrictScalars ℝ)
    (D.restrictScalars ℝ) t hT f

end StandardL2
end P201.Wave.RealBridge

open MeasureTheory Set Filter
open scoped FourierTransform ENNReal
open P201 P201.Wave
open P201Specs.Wave (WholeL2 WholeH1 FrequencyL2 wholeL2Standard)
namespace P201.Wave.RealBridge

lemma wholeL2Standard_ofRealLp {n : ℕ} (f : WholeL2 n ℝ) :
    wholeL2Standard n ℂ (ofRealLp ⊤ f) = ofRealL2 (wholeL2Standard n ℝ f) := by
  apply MeasureTheory.Lp.ext
  have ho : (ofRealLp ⊤ f : Space n → ℂ) =ᵐ[volume] fun x => (f x : ℂ) := by
    simpa only [domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
      Measure.restrict_univ] using ofRealLp_ae ⊤ f
  filter_upwards [wholeL2Standard_ae (ofRealLp ⊤ f), ho,
    Complex.ofRealCLM.coeFn_compLp (wholeL2Standard n ℝ f), wholeL2Standard_ae f]
    with x hs ho hc hf
  change _ = Complex.ofRealCLM.compLp (wholeL2Standard n ℝ f) x
  rw [hs, ho, hc, hf]
  rfl

lemma wholeL2Standard_reLp {n : ℕ} (f : WholeL2 n ℂ) :
    wholeL2Standard n ℝ (reLp ⊤ f) = reL2 (wholeL2Standard n ℂ f) := by
  apply MeasureTheory.Lp.ext
  have hr : (reLp ⊤ f : Space n → ℝ) =ᵐ[volume] fun x => (f x).re := by
    simpa only [domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
      Measure.restrict_univ] using reLp_ae ⊤ f
  filter_upwards [wholeL2Standard_ae (reLp ⊤ f), hr,
    Complex.reCLM.coeFn_compLp (wholeL2Standard n ℂ f), wholeL2Standard_ae f]
    with x hs hr hc hf
  change _ = Complex.reCLM.compLp (wholeL2Standard n ℂ f) x
  rw [hs, hr, hc, hf]
  rfl

lemma embeddedFourier_real {n : ℕ} (f : WholeL2 n ℝ) :
    P201Specs.Wave.embeddedFourier Complex.ofRealCLM f =
      P201Specs.Wave.embeddedFourier (ContinuousLinearMap.id ℝ ℂ) (ofRealLp ⊤ f) := by
  rw [embeddedFourier_complex, wholeL2Standard_ofRealLp]
  rfl

/-- Reality under real even Fourier symbols on the actual whole-space L² interface. -/
theorem whole_reality_of_real_even_symbol {n : ℕ}
    (m : Space n → ℝ) (hm : ∀ ξ, m (-ξ) = m ξ)
    (f : WholeL2 n ℝ) (d : WholeL2 n ℂ)
    (hd : (𝓕 (wholeL2Standard n ℂ d) : FrequencyL2 n) =ᵐ[volume]
      fun ξ => (m ξ : ℂ) * (𝓕 (wholeL2Standard n ℂ (ofRealLp ⊤ f)) : FrequencyL2 n) ξ) :
    ofRealLp ⊤ (reLp ⊤ d) = d := by
  apply (wholeL2Standard n ℂ).injective
  rw [wholeL2Standard_ofRealLp, wholeL2Standard_reLp]
  apply ofRealL2_reL2_of_conj_eq
  apply conj_eq_of_real_even_symbol m hm (ofRealL2 (wholeL2Standard n ℝ f))
    (wholeL2Standard n ℂ d) (conjL2_ofRealL2 _)
  simpa only [wholeL2Standard_ofRealLp] using hd

theorem wholeFourierMultiplier_reality {n : ℕ}
    (m : Space n → ℝ) (hm : MemLp (fun ξ => (m ξ : ℂ)) ∞ volume)
    (heven : ∀ ξ, m (-ξ) = m ξ) (f : WholeL2 n ℝ) :
    ofRealLp ⊤ (reLp ⊤ (wholeFourierMultiplier _ hm (ofRealLp ⊤ f))) =
      wholeFourierMultiplier _ hm (ofRealLp ⊤ f) := by
  apply whole_reality_of_real_even_symbol m heven f
  rw [wholeFourierMultiplier_standard]
  exact fourierMultiplier_ae _ _ _

lemma frequency_neg (n : ℕ) (c : ℝ) (ξ : Space n) :
    frequency n c (-ξ) = frequency n c ξ := by
  simp only [frequency, P201Specs.Wave.frequency, norm_neg]

lemma wholeCosine_reality {n : ℕ} (c t : ℝ) (f : WholeL2 n ℝ) :
    ofRealLp ⊤ (reLp ⊤ (wholeFourierMultiplier _ (cosineSymbol_memLp n c t) (ofRealLp ⊤ f))) =
      wholeFourierMultiplier _ (cosineSymbol_memLp n c t) (ofRealLp ⊤ f) := by
  apply wholeFourierMultiplier_reality (fun ξ => cosineSymbol t (frequency n c ξ))
  intro ξ
  rw [frequency_neg]

lemma sineH1_underlying_reality {n : ℕ} (c : ℝ) (hc : 0 < c) (t : ℝ)
    (f : WholeL2 n ℝ) :
    ofRealLp ⊤ (reLp ⊤ (hUnderlying ⊤ 1 (sineH1 n c hc t (ofRealLp ⊤ f)))) =
      hUnderlying ⊤ 1 (sineH1 n c hc t (ofRealLp ⊤ f)) := by
  apply whole_reality_of_real_even_symbol (fun ξ => sineSymbol t (frequency n c ξ))
    (fun ξ => by rw [frequency_neg]) f
  rw [sineH1_underlying, LinearIsometryEquiv.apply_symm_apply]
  exact fourierMultiplier_ae _ _ _

lemma cosineH1Derivative_reality {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (t : ℝ)
    (g : WholeH1 n ℝ) :
    ofRealLp ⊤ (reLp ⊤ (cosineH1Derivative c hc t (ofRealH1 ⊤ g))) =
      cosineH1Derivative c hc t (ofRealH1 ⊤ g) := by
  apply whole_reality_of_real_even_symbol
    (fun ξ => cosineDerivativeSymbol t (frequency n c ξ))
    (fun ξ => by rw [frequency_neg]) (hUnderlying ⊤ 1 g)
  simpa only [ofRealH1_underlying] using
    cosineH1Derivative_fourier c hc t (ofRealH1 ⊤ g)

lemma ofRealH1_reH1_of_underlying_real {n : ℕ} (g : WholeH1 n ℂ)
    (hg : ofRealLp ⊤ (reLp ⊤ (hUnderlying ⊤ 1 g)) = hUnderlying ⊤ 1 g) :
    ofRealH1 ⊤ (reH1 ⊤ g) = g := by
  apply hilbertUnderlyingInjective ⊤ 1
  rw [ofRealH1_underlying, reH1_underlying, hg]

lemma cosineH1_reality {n : ℕ} (c t : ℝ) (g : WholeH1 n ℝ) :
    ofRealH1 ⊤ (reH1 ⊤ (cosineH1 n c t (ofRealH1 ⊤ g))) =
      cosineH1 n c t (ofRealH1 ⊤ g) := by
  apply ofRealH1_reH1_of_underlying_real
  rw [cosineH1_underlying, ofRealH1_underlying]
  exact wholeCosine_reality c t (hUnderlying ⊤ 1 g)

lemma sineH1_reality {n : ℕ} (c : ℝ) (hc : 0 < c) (t : ℝ) (f : WholeL2 n ℝ) :
    ofRealH1 ⊤ (reH1 ⊤ (sineH1 n c hc t (ofRealLp ⊤ f))) =
      sineH1 n c hc t (ofRealLp ⊤ f) := by
  apply ofRealH1_reH1_of_underlying_real
  exact sineH1_underlying_reality c hc t f

end P201.Wave.RealBridge

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform
namespace P201.Wave
open P201Specs.Wave (FrequencyL2 WholeL2 WholeH1 wholeL2Standard embeddedFourier WaveOperators WaveFamilyLaws)
open RealBridge

def realWaveOperators {n : ℕ} (W : WaveOperators n ℂ) : WaveOperators n ℝ where
  C0 t := projectedOperator (ofRealLp ⊤) (reLp ⊤) ((W.C0 t).restrictScalars ℝ)
  C1 t := projectedOperator (ofRealH1 ⊤) (reH1 ⊤) ((W.C1 t).restrictScalars ℝ)
  S t := projectedOperator (ofRealLp ⊤) (reH1 ⊤) ((W.S t).restrictScalars ℝ)
  D t := projectedOperator (ofRealH1 ⊤) (reLp ⊤) ((W.D t).restrictScalars ℝ)

set_option maxHeartbeats 800000 in
theorem realWaveFamilyLaws {n : ℕ} (c : ℝ) (W : WaveOperators n ℂ)
    (hW : WaveFamilyLaws c (ContinuousLinearMap.id ℝ ℂ) W)
    (hE : ∀ f : WholeL2 n ℝ, embeddedFourier Complex.ofRealCLM f =
      embeddedFourier (ContinuousLinearMap.id ℝ ℂ) (ofRealLp ⊤ f))
    (hC : ∀ t (f : WholeL2 n ℝ),
      ofRealLp ⊤ (reLp ⊤ (W.C0 t (ofRealLp ⊤ f))) = W.C0 t (ofRealLp ⊤ f))
    (hS : ∀ t (f : WholeL2 n ℝ),
      ofRealLp ⊤ (reLp ⊤ (hUnderlying ⊤ 1 (W.S t (ofRealLp ⊤ f)))) =
        hUnderlying ⊤ 1 (W.S t (ofRealLp ⊤ f)))
    (hD : ∀ t (g : WholeH1 n ℝ),
      ofRealLp ⊤ (reLp ⊤ (W.D t (ofRealH1 ⊤ g))) = W.D t (ofRealH1 ⊤ g)) :
    WaveFamilyLaws c Complex.ofRealCLM (realWaveOperators W) := by
  rcases hW with ⟨hC0, hC1, hSF, hDF, hB, hC0cont, hC1cont, hScont, hDcont,
    hCderiv, hSderiv, hC0zero, hC1zero, hSzero, hDzero⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t f
    rw [hE]
    change (embeddedFourier (ContinuousLinearMap.id ℝ ℂ)
      (ofRealLp ⊤ (reLp ⊤ (W.C0 t (ofRealLp ⊤ f)))) : Space n → ℂ) =ᵐ[volume] _
    rw [hC, hE]
    exact hC0 t (ofRealLp ⊤ f)
  · intro t g
    change hUnderlying ⊤ 1 (reH1 ⊤ (W.C1 t (ofRealH1 ⊤ g))) =
      reLp ⊤ (W.C0 t (ofRealLp ⊤ (hUnderlying ⊤ 1 g)))
    rw [reH1_underlying, hC1, ofRealH1_underlying]
  · intro t f
    rw [hE]
    change (embeddedFourier (ContinuousLinearMap.id ℝ ℂ)
      (ofRealLp ⊤ (hUnderlying ⊤ 1 (reH1 ⊤ (W.S t (ofRealLp ⊤ f))))) : Space n → ℂ) =ᵐ[volume] _
    rw [reH1_underlying, hS, hE]
    exact hSF t (ofRealLp ⊤ f)
  · intro t g
    rw [hE]
    change (embeddedFourier (ContinuousLinearMap.id ℝ ℂ)
      (ofRealLp ⊤ (reLp ⊤ (W.D t (ofRealH1 ⊤ g)))) : Space n → ℂ) =ᵐ[volume] _
    rw [hD, hE, ← ofRealH1_underlying]
    exact hDF t (ofRealH1 ⊤ g)
  · intro t
    have h0 := projectedOperator_norm_le (ofRealLp (n := n) ⊤) (reLp ⊤)
      (fun f => (ofRealLp_norm ⊤ f).le) (reLp_norm_le ⊤) ((W.C0 t).restrictScalars ℝ)
    have h1 := projectedOperator_norm_le (ofRealH1 (n := n) ⊤) (reH1 ⊤)
      (fun g => (ofRealH1_norm ⊤ g).le) (reH1_norm_le ⊤) ((W.C1 t).restrictScalars ℝ)
    have hs := projectedOperator_norm_le (ofRealLp (n := n) ⊤) (reH1 ⊤)
      (fun f => (ofRealLp_norm ⊤ f).le) (reH1_norm_le ⊤) ((W.S t).restrictScalars ℝ)
    have hd := projectedOperator_norm_le (ofRealH1 (n := n) ⊤) (reLp ⊤)
      (fun g => (ofRealH1_norm ⊤ g).le) (reLp_norm_le ⊤) ((W.D t).restrictScalars ℝ)
    rw [ContinuousLinearMap.norm_restrictScalars] at h0 h1 hs hd
    exact ⟨h0.trans (hB t).1, h1.trans (hB t).2.1,
      hs.trans (hB t).2.2.1, hd.trans (hB t).2.2.2⟩
  · intro f
    exact (reLp ⊤).continuous.comp (hC0cont (ofRealLp ⊤ f))
  · intro g
    exact (reH1 ⊤).continuous.comp (hC1cont (ofRealH1 ⊤ g))
  · intro f
    exact (reH1 ⊤).continuous.comp (hScont (ofRealLp ⊤ f))
  · intro g
    exact (reLp ⊤).continuous.comp (hDcont (ofRealH1 ⊤ g))
  · intro t g
    have h := (reLp ⊤).hasFDerivAt.comp_hasDerivAt t (hCderiv t (ofRealH1 ⊤ g))
    convert h using 1
    · funext s
      exact reH1_underlying ⊤ _
    · rfl
  · intro t f
    have h := (reLp ⊤).hasFDerivAt.comp_hasDerivAt t (hSderiv t (ofRealLp ⊤ f))
    convert h using 1
    · funext s
      exact reH1_underlying ⊤ _
    · rfl
  · apply ContinuousLinearMap.ext
    intro f
    change reLp ⊤ (W.C0 0 (ofRealLp ⊤ f)) = f
    rw [hC0zero]
    exact reLp_ofRealLp ⊤ f
  · apply ContinuousLinearMap.ext
    intro g
    change reH1 ⊤ (W.C1 0 (ofRealH1 ⊤ g)) = g
    rw [hC1zero]
    exact reH1_ofRealH1 ⊤ g
  · apply ContinuousLinearMap.ext
    intro f
    change reH1 ⊤ (W.S 0 (ofRealLp ⊤ f)) = 0
    rw [hSzero, zero_apply, map_zero]
  · apply ContinuousLinearMap.ext
    intro g
    change reLp ⊤ (W.D 0 (ofRealH1 ⊤ g)) = 0
    rw [hDzero, zero_apply, map_zero]
end P201.Wave

namespace P201.Wave
open P201Specs.Wave (WaveOperators WaveFamilyLaws)

/-- The real family is the actual restriction of the complex Fourier family. -/
theorem realWaveMultipliers (n : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ W : WaveOperators n ℝ, WaveFamilyLaws c Complex.ofRealCLM W := by
  refine ⟨realWaveOperators (complexWaveOperators n c hc), ?_⟩
  apply realWaveFamilyLaws c _ (complexWaveFamilyLaws n c hc)
  · exact RealBridge.embeddedFourier_real
  · exact fun t f => RealBridge.wholeCosine_reality c t f
  · exact fun t f => RealBridge.sineH1_underlying_reality c hc t f
  · exact fun t g => RealBridge.cosineH1Derivative_reality c hc.le t g

/-- Complete wave multiplier theorem on the shared inhomogeneous H¹ space,
with the manuscript's Fourier phase, for both complex and real scalar data. -/
theorem waveMultipliers : P201Specs.Wave.waveMultipliersStatement := by
  intro n _ c hc
  exact ⟨complexWaveMultipliers n c hc, realWaveMultipliers n c hc⟩

end P201.Wave
