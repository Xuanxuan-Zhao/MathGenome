import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachGeometry.ClarksonLargeExponent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Interpolation.RieszThorin
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalitiesPow

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
universe u
namespace ExpandedFA.BanachGeometry
namespace Clarkson
open ExpandedFA.Interpolation.RieszThorinSpec

private abbrev Two := Fin 2
private abbrev cm : Measure Two := Measure.count

private lemma finite_memLp (h : Two → ℂ) (r : ℝ≥0∞) : MemLp h r cm :=
  eLpNorm_count_lt_top_of_lt (fun _ => enorm_lt_top)

private lemma finite_norm (h : Two → ℂ) {r : ℝ} (hr : 0 < r) :
    (eLpNorm h (ENNReal.ofReal r) cm).toReal =
      (‖h 0‖ ^ r + ‖h 1‖ ^ r) ^ r⁻¹ := by
  rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal
    (by positivity) ENNReal.ofReal_ne_top (finite_memLp h 1).aestronglyMeasurable]
  simp [ENNReal.toReal_ofReal hr.le, integral_count, Fin.sum_univ_two]

private def hadamard (h : Two → ℂ) : Two → ℂ := ![h 0 + h 1, h 0 - h 1]

private def countEval : (Two →ₘ[cm] ℂ) →ₗ[ℂ] (Two → ℂ) where
  toFun h := h
  map_add' f g := funext (Measure.ae_count_iff.mp (AEEqFun.coeFn_add f g))
  map_smul' c f := funext (Measure.ae_count_iff.mp (AEEqFun.coeFn_smul c f))

private def countMk : (Two → ℂ) →ₗ[ℂ] (Two →ₘ[cm] ℂ) where
  toFun h := AEEqFun.mk h (finite_memLp h 1).aestronglyMeasurable
  map_add' f g := by
    apply AEEqFun.ext
    exact (AEEqFun.coeFn_mk _ _).trans
      (((AEEqFun.coeFn_mk _ _).add (AEEqFun.coeFn_mk _ _)).symm.trans
        (AEEqFun.coeFn_add _ _).symm)
  map_smul' c f := by
    apply AEEqFun.ext
    exact (AEEqFun.coeFn_mk _ _).trans
      (((AEEqFun.coeFn_mk _ _).const_smul c).symm.trans
        (AEEqFun.coeFn_smul _ _).symm)

private def hadamardLinear : (Two → ℂ) →ₗ[ℂ] (Two → ℂ) where
  toFun := hadamard
  map_add' f g := by ext i; fin_cases i <;> simp [hadamard] <;> ring
  map_smul' c f := by ext i; fin_cases i <;> simp [hadamard, mul_add, mul_sub]

private def hadamardSum : SumSpace cm 1 2 →ₗ[ℂ] (Two →ₘ[cm] ℂ) :=
  countMk.comp (hadamardLinear.comp (countEval.comp (SumSpace cm 1 2).subtype))

private lemma hadamardSum_apply (f : SumSpace cm 1 2) :
    (hadamardSum f : Two → ℂ) = hadamard (f : Two →ₘ[cm] ℂ) := by
  exact funext (Measure.ae_count_iff.mp (AEEqFun.coeFn_mk _ _))

private lemma finite_enorm (h : Two → ℂ) {r : ℝ} (hr : 0 < r) :
    eLpNorm h (ENNReal.ofReal r) cm =
      ENNReal.ofReal ((‖h 0‖ ^ r + ‖h 1‖ ^ r) ^ r⁻¹) := by
  rw [← finite_norm h hr, ENNReal.ofReal_toReal (finite_memLp h _).ne]

private lemma endpoint_one : EndpointBound hadamardSum 1 ∞ 1 := by
  intro f _hf
  have hm := finite_memLp (hadamardSum f) ∞
  refine ⟨hm, ?_⟩
  rw [hadamardSum_apply, eLpNorm_exponent_top (finite_memLp _ 1).aestronglyMeasurable]
  have he : eLpNorm (f : Two →ₘ[cm] ℂ) 1 cm =
      ENNReal.ofReal (‖(f : Two →ₘ[cm] ℂ) 0‖ + ‖(f : Two →ₘ[cm] ℂ) 1‖) := by
    simpa using finite_enorm (f : Two →ₘ[cm] ℂ) (r := 1) (by norm_num)
  rw [he, ENNReal.ofReal_one, one_mul]
  apply eLpNormEssSup_le_of_ae_bound
  apply Measure.ae_count_iff.mpr
  intro i
  fin_cases i
  · exact norm_add_le _ _
  · exact norm_sub_le _ _

private lemma endpoint_two : EndpointBound hadamardSum 2 2 ((2 : ℝ) ^ (1 / 2 : ℝ)) := by
  intro f _hf
  refine ⟨finite_memLp _ _, ?_⟩
  rw [hadamardSum_apply]
  have he (h : Two → ℂ) : eLpNorm h 2 cm =
      ENNReal.ofReal ((‖h 0‖ ^ (2 : ℝ) + ‖h 1‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
    simpa using finite_enorm h (r := 2) (by norm_num)
  rw [he, he, ← ENNReal.ofReal_mul (by positivity)]
  apply le_of_eq
  congr 1
  have hpar := parallelogram_law_with_norm ℂ
    ((f : Two →ₘ[cm] ℂ) 0) ((f : Two →ₘ[cm] ℂ) 1)
  simp only [hadamard, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.rpow_two]
  rw [hpar, Real.mul_rpow (by norm_num) (by positivity)]

private lemma interp_params {p : ℝ} (hp : 2 < p) :
    Interpolates 1 2 (ENNReal.ofReal (p / (p - 1))) (2 / p) ∧
    Interpolates ∞ 2 (ENNReal.ofReal p) (2 / p) := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < p - 1 := by linarith
  have hq : 0 < p / (p - 1) := div_pos hp0 hd
  have ht : 0 ≤ 2 / p := by positivity
  have h1t : 0 ≤ 1 - 2 / p := by rw [sub_nonneg, div_le_one hp0]; linarith
  have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  constructor
  · unfold Interpolates
    rw [← ENNReal.ofReal_inv_of_pos hq, inv_one, mul_one, h2,
      ← ENNReal.ofReal_mul ht, ← ENNReal.ofReal_add h1t (by positivity)]
    congr 1
    field_simp
    ring
  · unfold Interpolates
    rw [← ENNReal.ofReal_inv_of_pos hp0, ENNReal.inv_top, mul_zero, zero_add, h2,
      ← ENNReal.ofReal_mul ht]
    congr 1
    ring

/-- The Hadamard matrix maps ℓ^q₂ to ℓ^p₂ with norm at most 2^(1/p).
The endpoint bounds above use the triangle and parallelogram identities. -/
theorem complex_two_point {p : ℝ} (hp : 2 < p) (a b : ℂ) :
    ‖a + b‖ ^ p + ‖a - b‖ ^ p ≤
      2 * (‖a‖ ^ (p / (p - 1)) + ‖b‖ ^ (p / (p - 1))) ^ (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p / (p - 1) := div_pos hp0 (by linarith)
  have hq1 : 1 ≤ p / (p - 1) := (le_div_iff₀ (by linarith : 0 < p - 1)).mpr (by linarith)
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal (by linarith : (1:ℝ) ≤ p)⟩
  have : Fact (1 ≤ ENNReal.ofReal (p / (p - 1))) := ⟨by simpa using ENNReal.ofReal_le_ofReal hq1⟩
  let h : Two → ℂ := ![a, b]
  let f := (finite_memLp h (ENNReal.ofReal (p / (p - 1)))).toLp h
  obtain ⟨hf, _hout, hb⟩ := ExpandedFA.Interpolation.riesz_thorin cm cm 1 2 ∞ 2
    (ENNReal.ofReal (p / (p - 1))) (ENNReal.ofReal p) (2 / p) 1
    ((2 : ℝ) ^ (1 / 2 : ℝ)) (by positivity) ((div_lt_one hp0).mpr hp)
    (by norm_num) (by positivity) (interp_params hp).1 (interp_params hp).2
    hadamardSum endpoint_one endpoint_two f
  have he : (f : Two → ℂ) = h :=
    funext (Measure.ae_count_iff.mp (MemLp.coeFn_toLp _))
  rw [hadamardSum_apply] at hb
  change (eLpNorm (hadamard (f : Two → ℂ)) (ENNReal.ofReal p) cm).toReal ≤ _ at hb
  rw [he, finite_norm _ hp0, Lp.norm_toLp, finite_norm _ hq0] at hb
  simp only [h, hadamard, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.one_rpow, one_mul] at hb
  have hb' := Real.rpow_le_rpow (by positivity) hb hp0.le
  rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hp0.ne', Real.rpow_one,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)] at hb'
  have hc : (1 / 2 : ℝ) * (2 / p * p) = 1 := by field_simp
  have he : (p / (p - 1))⁻¹ * p = p - 1 := by field_simp
  simpa only [hc, he, Real.rpow_one] using hb'

/-- Every real or complex scalar field embeds isometrically in ℂ. -/
def scalarEmbedding (𝕜 : Type*) [RCLike 𝕜] : 𝕜 →ₗᵢ[ℝ] ℂ where
  toFun z := ⟨RCLike.re z, RCLike.im z⟩
  map_add' z w := by apply Complex.ext <;> simp
  map_smul' c z := by apply Complex.ext <;> simp [RCLike.smul_re, RCLike.smul_im]
  norm_map' z := by
    rw [Complex.norm_def, ← RCLike.sqrt_normSq_eq_norm]
    congr 1

/-- Scalar two-point Clarkson estimate, including p=2. -/
theorem two_point {𝕜 : Type*} [RCLike 𝕜] {p : ℝ} (hp : 2 ≤ p) (a b : 𝕜) :
    ‖a + b‖ ^ p + ‖a - b‖ ^ p ≤
      2 * (‖a‖ ^ (p / (p - 1)) + ‖b‖ ^ (p / (p - 1))) ^ (p - 1) := by
  have he (z : 𝕜) : ‖scalarEmbedding 𝕜 z‖ = ‖z‖ := (scalarEmbedding 𝕜).norm_map z
  suffices h : ‖scalarEmbedding 𝕜 a + scalarEmbedding 𝕜 b‖ ^ p +
      ‖scalarEmbedding 𝕜 a - scalarEmbedding 𝕜 b‖ ^ p ≤
      2 * (‖scalarEmbedding 𝕜 a‖ ^ (p / (p - 1)) +
        ‖scalarEmbedding 𝕜 b‖ ^ (p / (p - 1))) ^ (p - 1) by
    simpa only [← map_add, ← map_sub, he] using h
  rcases eq_or_lt_of_le hp with h | h
  · subst p
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, div_one, Real.rpow_one,
      Real.rpow_two] using (parallelogram_law_with_norm ℂ
        (scalarEmbedding 𝕜 a) (scalarEmbedding 𝕜 b)).le
  · exact complex_two_point h _ _

lemma two_point_enorm {𝕜 : Type*} [RCLike 𝕜] {p : ℝ} (hp : 2 ≤ p) (a b : 𝕜) :
    ‖a + b‖ₑ ^ p + ‖a - b‖ₑ ^ p ≤
      2 * (‖a‖ₑ ^ (p / (p - 1)) + ‖b‖ₑ ^ (p / (p - 1))) ^ (p - 1) := by
  have hp0 : 0 ≤ p := by linarith
  have hr0 : 0 ≤ p - 1 := by linarith
  have hq0 : 0 ≤ p / (p - 1) := div_nonneg hp0 hr0
  have h := ENNReal.ofReal_le_ofReal (two_point hp a b)
  have hn (x : 𝕜) (r : ℝ) (hr : 0 ≤ r) :
      ENNReal.ofReal (‖x‖ ^ r) = ‖x‖ₑ ^ r := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg x) hr, ofReal_norm]
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hr0,
    ENNReal.ofReal_add (by positivity) (by positivity),
    hn (a + b) p hp0, hn (a - b) p hp0,
    hn a _ hq0, hn b _ hq0] at h
  simpa only [ENNReal.ofReal_ofNat] using h


lemma integral_power_norm {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    {f : X → E} (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = (eLpNorm f p μ) ^ p.toReal := by
  rw [eLpNorm_eq_eLpNorm' hp0 hpt hf]
  exact lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hpt)

/-- Minkowski in exponent p-1, applied to the q-th powers of the moduli. -/
theorem integrated_mixed {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 2 ≤ p.toReal) (hpt : p ≠ ∞) (f g : Lp 𝕜 p μ) :
    (eLpNorm (f + g) p μ) ^ p.toReal + (eLpNorm (f - g) p μ) ^ p.toReal ≤
      2 * ((eLpNorm f p μ) ^ (p.toReal / (p.toReal - 1)) +
        (eLpNorm g p μ) ^ (p.toReal / (p.toReal - 1))) ^ (p.toReal - 1) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) (Fact.out : 1 ≤ p))
  let P := p.toReal
  let R := P - 1
  let Q := P / R
  have hR : 1 ≤ R := by dsimp [R, P]; linarith
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hQR : Q * R = P := div_mul_cancel₀ _ hR0.ne'
  have hPQ : P * (1 / R) = Q := by dsimp [Q]; ring
  have hfi : (∫⁻ x, (‖f x‖ₑ ^ Q) ^ R ∂μ) = (eLpNorm f p μ) ^ P := by
    simp_rw [← ENNReal.rpow_mul, hQR]
    exact integral_power_norm hp0 hpt (Lp.aestronglyMeasurable f)
  have hgi : (∫⁻ x, (‖g x‖ₑ ^ Q) ^ R ∂μ) = (eLpNorm g p μ) ^ P := by
    simp_rw [← ENNReal.rpow_mul, hQR]
    exact integral_power_norm hp0 hpt (Lp.aestronglyMeasurable g)
  have hm := ENNReal.lintegral_Lp_add_le
    ((Lp.aestronglyMeasurable f).enorm.pow_const Q)
    ((Lp.aestronglyMeasurable g).enorm.pow_const Q) hR
  simp only [Pi.add_apply] at hm
  rw [hfi, hgi, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hPQ] at hm
  have hm' := ENNReal.rpow_le_rpow hm hR0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hR0.ne', ENNReal.rpow_one] at hm'
  have hs : ∀ᵐ x ∂μ,
      ‖(f + g) x‖ₑ ^ P + ‖(f - g) x‖ₑ ^ P ≤
      2 * (‖f x‖ₑ ^ Q + ‖g x‖ₑ ^ Q) ^ R := by
    filter_upwards [Lp.coeFn_add f g, Lp.coeFn_sub f g] with x hx hy
    rw [hx, hy]
    exact two_point_enorm hp (f x) (g x)
  calc
    _ = ∫⁻ x, ‖(f + g) x‖ₑ ^ P + ‖(f - g) x‖ₑ ^ P ∂μ := by
      rw [lintegral_add_left' ((Lp.aestronglyMeasurable (f + g)).enorm.pow_const P),
        integral_power_norm hp0 hpt (Lp.aestronglyMeasurable (f + g)),
        integral_power_norm hp0 hpt (Lp.aestronglyMeasurable (f - g))]
    _ ≤ ∫⁻ x, 2 * (‖f x‖ₑ ^ Q + ‖g x‖ₑ ^ Q) ^ R ∂μ := lintegral_mono_ae hs
    _ = 2 * ∫⁻ x, (‖f x‖ₑ ^ Q + ‖g x‖ₑ ^ Q) ^ R ∂μ := by
      rw [lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ _ := mul_le_mul' le_rfl hm'

/-- The second inequality is the ordinary two-point convex power estimate. -/
theorem convexity_refinement {P : ℝ} (hP : 2 ≤ P) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (a ^ (P / (P - 1)) + b ^ (P / (P - 1))) ^ (P / (P / (P - 1))) ≤
      (2 : ℝ) ^ (P - 1) * (a ^ P + b ^ P) := by
  have hP0 : 0 < P := by linarith
  have hR0 : 0 < P - 1 := by linarith
  have hPR : P / (P / (P - 1)) = P - 1 := by field_simp
  have hQR : P / (P - 1) * (P - 1) = P := div_mul_cancel₀ _ hR0.ne'
  have h : (a ^ (P / (P - 1)) + b ^ (P / (P - 1))) ^ (P - 1) ≤
      (2 : ℝ) ^ ((P - 1) - 1) *
        ((a ^ (P / (P - 1))) ^ (P - 1) + (b ^ (P / (P - 1))) ^ (P - 1)) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
      (⟨a ^ (P / (P - 1)), by positivity⟩ : ℝ≥0)
      (⟨b ^ (P / (P - 1)), by positivity⟩ : ℝ≥0) (by linarith : 1 ≤ P - 1)
  rw [← Real.rpow_mul ha, ← Real.rpow_mul hb, hQR] at h
  have hc : (2 : ℝ) * 2 ^ ((P - 1) - 1) = 2 ^ (P - 1) := by
    calc
      _ = (2 : ℝ) ^ (1 : ℝ) * 2 ^ ((P - 1) - 1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  rw [hPR]
  calc
    _ ≤ 2 * (2 ^ ((P - 1) - 1) * (a ^ P + b ^ P)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by rw [← mul_assoc, hc]

/-- The mixed Clarkson bound on the actual Lᵖ quotient. -/
theorem lp_mixed {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 2 ≤ p.toReal) (hpt : p ≠ ∞) (f g : Lp 𝕜 p μ) :
    ‖f + g‖ ^ p.toReal + ‖f - g‖ ^ p.toReal ≤
      2 * (‖f‖ ^ (p.toReal / (p.toReal - 1)) +
        ‖g‖ ^ (p.toReal / (p.toReal - 1))) ^ (p.toReal / (p.toReal / (p.toReal - 1))) := by
  have hr0 : 0 ≤ p.toReal - 1 := by linarith
  have hq0 : 0 ≤ p.toReal / (p.toReal - 1) := div_nonneg ENNReal.toReal_nonneg hr0
  have hb := integrated_mixed hp hpt f g
  have hfin : 2 * (eLpNorm f p μ ^ (p.toReal / (p.toReal - 1)) +
      eLpNorm g p μ ^ (p.toReal / (p.toReal - 1))) ^ (p.toReal - 1) ≠ ∞ := by
    finiteness
  have hb' := ENNReal.toReal_mono hfin hb
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hb'
  simp only [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ← Lp.norm_def] at hb'
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hb'
  simp only [← ENNReal.toReal_rpow, ← Lp.norm_def] at hb'
  have hPR : p.toReal / (p.toReal / (p.toReal - 1)) = p.toReal - 1 := by
    have hp0 : 0 < p.toReal := by linarith
    have hr0 : 0 < p.toReal - 1 := by linarith
    field_simp
  simpa only [hPR] using hb'

end Clarkson
/-- Both exact large-exponent bounds from the source, over arbitrary measures. -/
theorem clarkson_large_exponent :
    ClarksonLargeExponentSpec.ClarksonLargeExponent.{u} := by
  intro X _ μ 𝕜 _ p _ hp hpt f g
  exact ⟨Clarkson.lp_mixed hp hpt f g,
    Clarkson.convexity_refinement hp (norm_nonneg f) (norm_nonneg g)⟩

end ExpandedFA.BanachGeometry
