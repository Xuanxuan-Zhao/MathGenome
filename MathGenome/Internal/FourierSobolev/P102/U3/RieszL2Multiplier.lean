import MathGenome.Internal.FourierSobolev.Specs.P102.U3.RieszL2Multiplier
import MathGenome.Internal.FourierSobolev.P102.U3.Plancherel
import MathGenome.Internal.FourierSobolev.P102.U3.Gaussian
import MathGenome.Internal.FourierSobolev.P102.U3.FourierConvolution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped FourierTransform ContDiff Pointwise SchwartzMap

namespace P102.U3.Riesz
open P102.Specs.U3 (Euclidean)
open P102.Specs.U3.Riesz (L2 F2 IsMultiplier symbolAtOrigin)

def constant : ℕ → ℝ := P102.Specs.U3.Riesz.constantValue

def kernel : (d : ℕ) → Fin d → Euclidean d → ℝ := P102.Specs.U3.Riesz.kernelValue

def symbol : (d : ℕ) → Fin d → Euclidean d → ℂ := P102.Specs.U3.Riesz.symbolValue

theorem constant_pos (d : ℕ) : 0 < constant d := by
  apply div_pos
  · apply Real.Gamma_pos_of_pos
    positivity
  · exact Real.rpow_pos_of_pos Real.pi_pos _

theorem kernel_odd {d : ℕ} (j : Fin d) (x : Euclidean d) :
    kernel d j (-x) = -kernel d j x := by
  simp [kernel, P102.Specs.U3.Riesz.kernelValue, neg_div]

theorem kernel_smooth : P102.Specs.U3.Riesz.smoothStatement := by
  intro d _ j x hx
  have hx' : x ≠ 0 := by simpa using hx
  exact ((contDiffAt_const.mul (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).contDiff.contDiffAt).div
    ((contDiffAt_norm ℝ hx').pow (d + 1)) (pow_ne_zero _ (norm_ne_zero_iff.mpr hx'))).contDiffWithinAt

theorem symbol_norm_le_one {d : ℕ} (j : Fin d) (ξ : Euclidean d) : ‖symbol d j ξ‖ ≤ 1 := by
  by_cases hξ : ξ = 0
  · simp [symbol, P102.Specs.U3.Riesz.symbolValue, hξ]
  · have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    simpa [symbol, P102.Specs.U3.Riesz.symbolValue, norm_mul,
      Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg ξ)] using
      (div_le_one hnorm).mpr (PiLp.norm_apply_le ξ j)

theorem symbol_measurable {d : ℕ} (j : Fin d) : Measurable (symbol d j) := by
  unfold symbol P102.Specs.U3.Riesz.symbolValue
  fun_prop

theorem symbol_memLp_top {d : ℕ} (j : Fin d) : MemLp (symbol d j) (⊤ : ENNReal) volume :=
  memLp_top_of_bound (symbol_measurable j).aestronglyMeasurable 1
    (Eventually.of_forall (symbol_norm_le_one j))

/-- Pointwise multiplication by the bounded measurable symbol on frequency L². -/
def frequencyMul {d : ℕ} (j : Fin d) : L2 d →L[ℂ] L2 d :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume (⊤ : ENNReal) 2 2 ((symbol_memLp_top j).toLp _)

theorem frequencyMul_ae {d : ℕ} (j : Fin d) (f : L2 d) :
    (frequencyMul j f : Euclidean d → ℂ) =ᵐ[volume] fun ξ => symbol d j ξ * f ξ := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((symbol_memLp_top j).toLp _) f, (symbol_memLp_top j).coeFn_toLp] with ξ hξ hm
  simpa [frequencyMul, hm] using hξ

theorem frequencyMul_norm_le {d : ℕ} (j : Fin d) (f : L2 d) :
    ‖frequencyMul j f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [frequencyMul_ae j f] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (symbol_norm_le_one j ξ)

/-- Conjugation by the shared canonical Plancherel transform. -/
def rieszL2 {d : ℕ} (j : Fin d) : L2 d →L[ℂ] L2 d :=
  (F2 d).symm.toContinuousLinearEquiv.toContinuousLinearMap
    ∘L frequencyMul j ∘L
    (F2 d).toContinuousLinearEquiv.toContinuousLinearMap

theorem rieszL2_frequency {d : ℕ} (j : Fin d) (f : L2 d) :
    F2 d (rieszL2 j f) = frequencyMul j (F2 d f) := by
  exact (F2 d).apply_symm_apply _

theorem rieszL2_norm_le {d : ℕ} (j : Fin d) : ‖rieszL2 j‖ ≤ 1 := by
  apply (rieszL2 j).opNorm_le_bound zero_le_one
  intro f
  simpa [rieszL2] using frequencyMul_norm_le j (F2 d f)


open P102.Specs.U3.Riesz (constantValue kernelValue symbolValue line)

theorem kernel_homogeneous : P102.Specs.U3.Riesz.homogeneousStatement := by
  intro d _ j r hr x
  by_cases hx : x = 0
  · simp [kernelValue, hx]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    simp only [kernelValue, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow,
      PiLp.smul_apply, smul_eq_mul, zpow_neg, zpow_natCast]
    rw [pow_succ]
    field_simp

abbrev Sphere (d : ℕ) := Metric.sphere (0 : Euclidean d) 1

def sphereNeg (d : ℕ) : Sphere d ≃ₜ Sphere d where
  toFun θ := ⟨-θ.val, by simpa using θ.property⟩
  invFun θ := ⟨-θ.val, by simpa using θ.property⟩
  left_inv θ := by ext; simp
  right_inv θ := by ext; simp
  continuous_toFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _

lemma sphereNeg_measurePreserving (d : ℕ) :
    MeasurePreserving (sphereNeg d) (volume : Measure (Euclidean d)).toSphere
      (volume : Measure (Euclidean d)).toSphere := by
  refine ⟨(sphereNeg d).continuous.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereNeg d).continuous.measurable hs]
  rw [Measure.toSphere_apply' _ ((sphereNeg d).continuous.measurable hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have he : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereNeg d ⁻¹' s)) =
      Neg.neg ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext z
    constructor
    · rintro ⟨r, hr, y, ⟨θ, hθ, rfl⟩, rfl⟩
      exact ⟨r, hr, -θ.val, ⟨sphereNeg d θ, hθ, rfl⟩, by simp⟩
    · rintro ⟨r, hr, y, ⟨θ, hθ, rfl⟩, hz⟩
      refine ⟨r, hr, -θ.val, ⟨sphereNeg d θ, ?_, rfl⟩, ?_⟩
      · simpa [sphereNeg] using hθ
      · simpa using congrArg Neg.neg hz
  rw [he, Measure.measure_preimage_neg]

lemma kernel_sphere_integrable (d : ℕ) (j : Fin d) :
    Integrable (fun θ : Sphere d => kernel d j θ.val)
      (volume : Measure (Euclidean d)).toSphere := by
  have he (θ : Sphere d) : kernel d j θ.val = constant d * θ.val j := by
    have hn : ‖θ.val‖ = 1 := by simpa using θ.property
    simp [kernel, P102.Specs.U3.Riesz.kernelValue, hn, constant]
  simp_rw [he]
  have hc : Continuous (fun θ : Sphere d => constant d * θ.val j) := by fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma kernel_sphere_zero (d : ℕ) (j : Fin d) :
    (∫ θ : Sphere d, kernel d j θ.val ∂(volume : Measure (Euclidean d)).toSphere) = 0 := by
  have h := (sphereNeg_measurePreserving d).integral_comp
    (sphereNeg d).measurableEmbedding (fun θ : Sphere d => kernel d j θ.val)
  have he (θ : Sphere d) : kernel d j (sphereNeg d θ).val = -kernel d j θ.val :=
    kernel_odd j θ.val
  simp_rw [he] at h
  rw [integral_neg] at h
  linarith
theorem kernel_sphere_mean : P102.Specs.U3.Riesz.sphereMeanStatement := by
  intro d _ j
  exact ⟨kernel_sphere_integrable d j, kernel_sphere_zero d j⟩

theorem line_norm (x : ℝ) : ‖line x‖ = |x| := by
  simp [line, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
theorem constant_one : constantValue 1 = 1 / Real.pi := by
  norm_num [constantValue]
theorem kernel_one (x : ℝ) : kernelValue 1 0 (line x) = 1 / (Real.pi * x) := by
  have hc : constantValue 1 = 1 / Real.pi := by norm_num [constantValue]
  have hn : ‖line x‖ = |x| := by simp [line, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  rw [kernelValue, hc, hn]
  change (1 / Real.pi) * x / |x| ^ 2 = _
  rw [sq_abs]
  by_cases hx : x = 0
  · simp [hx]
  · field_simp
theorem symbol_one (x : ℝ) : symbolValue 1 0 (line x) = -Complex.I * (Real.sign x : ℂ) := by
  have hn : ‖line x‖ = |x| := by simp [line, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  rw [symbolValue, hn]
  congr 2
  change x / |x| = Real.sign x
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [abs_of_neg h, Real.sign_of_neg h]
    simp [h.ne]
  · simp
  · rw [abs_of_pos h, Real.sign_of_pos h, div_self h.ne']

theorem one_dimensional : P102.Specs.U3.Riesz.oneDimensionalStatement :=
  ⟨constant_one, kernel_one, symbol_one⟩

theorem kernel_derivative_bound : P102.Specs.U3.Riesz.derivativeBoundStatement := by
  intro d _
  have hc := constant_pos d
  refine ⟨constant d * ((d : ℝ) + 2), by positivity, ?_⟩
  intro j x hx
  let p : Euclidean d →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin d => ℝ) j
  let N : ℝ := ‖x‖
  let D : Euclidean d →L[ℝ] ℝ := fderiv ℝ (fun y : Euclidean d => ‖y‖) x
  have hN : 0 < N := norm_pos_iff.mpr hx
  have hD : HasFDerivAt (fun y : Euclidean d => ‖y‖) D x :=
    ((contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 norm x).differentiableAt (by norm_num)).hasFDerivAt
  have hDnorm : ‖D‖ ≤ 1 := by
    exact norm_fderiv_le_of_lipschitz ℝ (x₀ := x) lipschitzWith_one_norm
  have hpnorm : ‖p‖ ≤ 1 := by
    apply p.opNorm_le_bound zero_le_one
    intro y
    simpa [p] using PiLp.norm_apply_le y j
  have hpow := hD.pow (d + 1)
  have hinv := (hasDerivAt_inv (pow_ne_zero (d + 1) hN.ne')).comp_hasFDerivAt x hpow
  have hprod := ((p.hasFDerivAt).mul hinv).const_mul (constant d)
  simp only [Pi.mul_apply, Function.comp_apply] at hprod
  have heq : (fun y : Euclidean d => constant d * (p y * (‖y‖ ^ (d + 1))⁻¹)) =
      P102.Specs.U3.Riesz.kernelValue d j := by
    ext y
    simp [p, P102.Specs.U3.Riesz.kernelValue, constant, div_eq_mul_inv, mul_assoc]
  change ‖fderiv ℝ (P102.Specs.U3.Riesz.kernelValue d j) x‖ ≤ _
  rw [← heq, hprod.fderiv]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (constant_pos d).le]
  change constant d * ‖p x • -((N ^ (d + 1)) ^ 2)⁻¹ •
      (((d + 1 : ℕ) : ℝ) * N ^ d) • D + (N ^ (d + 1))⁻¹ • p‖ ≤
    constant d * ((d : ℝ) + 2) / N ^ (d + 1)
  have hpx : |p x| ≤ N := PiLp.norm_apply_le x j
  calc
    _ ≤ constant d * (‖p x • -((N ^ (d + 1)) ^ 2)⁻¹ •
        (((d + 1 : ℕ) : ℝ) * N ^ d) • D‖ + ‖(N ^ (d + 1))⁻¹ • p‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hc.le
    _ = constant d * (|p x| * ((N ^ (d + 1)) ^ 2)⁻¹ *
        (((d + 1 : ℕ) : ℝ) * N ^ d) * ‖D‖ + (N ^ (d + 1))⁻¹ * ‖p‖) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_inv, abs_mul, abs_pow,
        abs_of_pos hN, abs_of_nonneg (show (0 : ℝ) ≤ (d + 1 : ℕ) from Nat.cast_nonneg _)]
      ring
    _ ≤ constant d * (N * ((N ^ (d + 1)) ^ 2)⁻¹ *
        (((d + 1 : ℕ) : ℝ) * N ^ d) * 1 + (N ^ (d + 1))⁻¹ * 1) := by
      gcongr
    _ = constant d * ((d : ℝ) + 2) / N ^ (d + 1) := by
      rw [pow_succ]
      push_cast
      field_simp
      ring

theorem symbol_origin_ae {d : ℕ} (j : Fin d) (a : ℂ) :
    symbolAtOrigin j a =ᵐ[volume] symbol d j := by
  let : Nonempty (Fin d) := ⟨j⟩
  filter_upwards [volume.ae_ne (0 : Euclidean d)] with ξ hξ
  simp [symbolAtOrigin, hξ, symbol]
theorem multiplier_exists : P102.Specs.U3.Riesz.multiplierStatement := by
  intro d _ j a
  refine ⟨rieszL2 j, rieszL2_norm_le j, ?_⟩
  intro f
  rw [rieszL2_frequency]
  let : Nonempty (Fin d) := ⟨j⟩
  filter_upwards [frequencyMul_ae j (F2 d f), volume.ae_ne (0 : Euclidean d)] with ξ hξ hne
  simpa [symbolAtOrigin, hne, symbol] using hξ
theorem multiplier_unique : P102.Specs.U3.Riesz.uniquenessStatement := by
  intro d _ j a b R S hR hS
  let : Nonempty (Fin d) := ⟨j⟩
  apply ContinuousLinearMap.ext
  intro f
  apply (F2 d).injective
  apply Lp.ext
  filter_upwards [hR f, hS f, volume.ae_ne (0 : Euclidean d)] with ξ hRξ hSξ hne
  rw [hRξ, hSξ]
  simp [symbolAtOrigin, hne]


lemma inverse_gamma_integral {q A : ℝ} (hq : 0 < q) (hA : 0 < A) :
    (∫ t : ℝ in Ioi 0, t ^ (-q - 1) * Real.exp (-A / t)) =
      (1 / A) ^ q * Real.Gamma q := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hq hA]
  rw [← integral_comp_rpow_Ioi (fun u : ℝ => u ^ (q - 1) * Real.exp (-(A * u)))
    (p := -1) (by norm_num)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht' : 0 < t := ht
  simp only [abs_neg, abs_one, one_mul, smul_eq_mul]
  rw [← Real.rpow_mul ht'.le]
  have he : -A / t = -(A * t ^ (-1 : ℝ)) := by rw [Real.rpow_neg_one]; ring
  rw [he]
  rw [← mul_assoc, ← Real.rpow_add ht']
  congr 2
  ring

lemma physical_integral (d : ℕ) {x : P102.Specs.U3.Euclidean d} (hx : x ≠ 0) :
    (∫ t : ℝ in Ioi 0, t ^ (-((d : ℝ) + 3) / 2) *
      Real.exp (-Real.pi * ‖x‖ ^ 2 / t)) =
      P102.U3.Riesz.constant d / ‖x‖ ^ (d + 1) := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h := inverse_gamma_integral (q := ((d : ℝ) + 1) / 2)
    (A := Real.pi * ‖x‖ ^ 2) (by positivity) (by positivity)
  have he : -(((d : ℝ) + 1) / 2) - 1 = -((d : ℝ) + 3) / 2 := by ring
  simp only [he, ← neg_mul] at h
  rw [h]
  unfold P102.U3.Riesz.constant P102.Specs.U3.Riesz.constantValue
  rw [one_div, Real.inv_rpow (by positivity), Real.mul_rpow Real.pi_pos.le (by positivity)]
  rw [← Real.rpow_natCast (‖x‖) (2 : ℕ), ← Real.rpow_mul hxnorm.le]
  have he' : (2 : ℝ) * (((d : ℝ) + 1) / 2) = (d + 1 : ℕ) := by push_cast; ring
  norm_num only [Nat.cast_ofNat]
  rw [he', Real.rpow_natCast]
  field_simp

lemma frequency_integral {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, t ^ (-(1 / 2 : ℝ)) * Real.exp (-Real.pi * t * r ^ 2)) = 1 / r := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 / 2 : ℝ))
    (r := Real.pi * r ^ 2) (by norm_num) (by positivity)
  have he : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by norm_num
  simp only [he] at h
  have he' (t : ℝ) : -(Real.pi * r ^ 2 * t) = -Real.pi * t * r ^ 2 := by ring
  simp only [he'] at h
  rw [h, Real.Gamma_one_half_eq]
  rw [one_div, Real.inv_rpow (by positivity), Real.mul_rpow Real.pi_pos.le (by positivity)]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  field_simp

lemma kernel_size {d : ℕ} (j : Fin d) (z : Euclidean d) :
    ‖kernel d j z‖ ≤ constant d / ‖z‖ ^ d := by
  have hc := constant_pos d
  by_cases hz : z = 0
  · simp only [hz, kernel, P102.Specs.U3.Riesz.kernelValue, PiLp.zero_apply, mul_zero,
      zero_div, norm_zero]
    positivity
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    calc
      _ = constant d * |z j| / ‖z‖ ^ (d + 1) := by
        change |constant d * z j / ‖z‖ ^ (d + 1)| = _
        rw [abs_div, abs_mul, abs_of_pos hc, abs_pow, abs_of_pos hn]
      _ ≤ constant d * ‖z‖ / ‖z‖ ^ (d + 1) := by
        gcongr
        exact PiLp.norm_apply_le z j
      _ = _ := by rw [pow_succ]; field_simp

lemma kernel_mul_norm_size {d : ℕ} (j : Fin d) (z : Euclidean d) :
    ‖kernel d j z‖ * ‖z‖ ≤ constant d * ‖z‖ ^ (-((d : ℝ) - 1)) := by
  have hc := constant_pos d
  by_cases hz : z = 0
  · simp only [hz, norm_zero, mul_zero]
    positivity
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    calc
      _ ≤ (constant d / ‖z‖ ^ d) * ‖z‖ := mul_le_mul_of_nonneg_right (kernel_size j z) hn.le
      _ = _ := by
        have he : -((d : ℝ) - 1) = 1 - (d : ℝ) := by ring
        rw [he, Real.rpow_sub hn, Real.rpow_one, Real.rpow_natCast]
        ring

lemma kernel_measurable {d : ℕ} (j : Fin d) : Measurable (kernel d j) := by
  unfold kernel P102.Specs.U3.Riesz.kernelValue
  fun_prop

/-- Globally absolutely convergent odd-part formula for a compact smooth input. -/
def oddIntegrand {d : ℕ} (j : Fin d) (f : Euclidean d → ℂ) (x z : Euclidean d) : ℂ :=
  (kernel d j z : ℂ) * (f (x - z) - f (x + z)) / 2

lemma oddIntegrand_integrable {d : ℕ} (hd : 1 ≤ d) (j : Fin d)
    {f : Euclidean d → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (x : Euclidean d) : Integrable (oddIntegrand j f x) := by
  obtain ⟨L, hL⟩ := hf.lipschitzWith_of_hasCompactSupport hfc (by simp)
  have hbound (z : Euclidean d) :
      ‖oddIntegrand j f x z‖ ≤ (constant d * L) * ‖z‖ ^ (-((d : ℝ) - 1)) := by
    have hdiff : ‖f (x - z) - f (x + z)‖ ≤ (L : ℝ) * (2 * ‖z‖) := by
      have hb := hL.norm_sub_le (x - z) (x + z)
      have he : x - z - (x + z) = (-2 : ℝ) • z := by module
      simpa only [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using hb
    calc
      _ = ‖kernel d j z‖ * ‖f (x - z) - f (x + z)‖ / 2 := by
        simp [oddIntegrand]
      _ ≤ ‖kernel d j z‖ * ((L : ℝ) * (2 * ‖z‖)) / 2 := by gcongr
      _ = (‖kernel d j z‖ * ‖z‖) * L := by ring
      _ ≤ (constant d * ‖z‖ ^ (-((d : ℝ) - 1))) * L :=
        mul_le_mul_of_nonneg_right (kernel_mul_norm_size j z) L.coe_nonneg
      _ = _ := by ring
  have hm : Measurable (oddIntegrand j f x) := by
    unfold oddIntegrand
    exact (((kernel_measurable j).complex_ofReal.mul
      ((hf.continuous.measurable.comp (by fun_prop)).sub
        (hf.continuous.measurable.comp (by fun_prop)))).div_const 2)
  have hlocal : LocallyIntegrable (oddIntegrand j f x) volume := by
    apply locallyIntegrable_of_norm_le_rpow
      (by simpa using hd) (α := (d : ℝ) - 1) (C := constant d * L)
    · simp only [finrank_euclideanSpace, Fintype.card_fin]
      linarith
    · exact Eventually.of_forall hbound
    · exact hm.aestronglyMeasurable
  have hc1 : HasCompactSupport (fun z : Euclidean d => f (x - z)) := by
    simpa [Function.comp_def] using hfc.comp_homeomorph (Homeomorph.subLeft x)
  have hc2 : HasCompactSupport (fun z : Euclidean d => f (x + z)) := by
    simpa [Function.comp_def] using hfc.comp_homeomorph (Homeomorph.addLeft x)
  have hc : HasCompactSupport (oddIntegrand j f x) := by
    have h := ((hc1.sub hc2).mul_left (f := fun z : Euclidean d => (kernel d j z : ℂ))).mul_right
      (f' := fun _ : Euclidean d => (2 : ℂ)⁻¹)
    change HasCompactSupport (fun z : Euclidean d =>
      (kernel d j z : ℂ) * (f (x - z) - f (x + z)) * (2 : ℂ)⁻¹) at h
    change HasCompactSupport (fun z : Euclidean d =>
      (kernel d j z : ℂ) * (f (x - z) - f (x + z)) / 2)
    simp only [div_eq_mul_inv]
    exact h
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).mp
    (hlocal.integrableOn_isCompact hc)

lemma truncation_integrable {d : ℕ} (j : Fin d) {f : Euclidean d → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε)
    (x : Euclidean d) : IntegrableOn (fun z => (kernel d j z : ℂ) * f (x - z))
      {z : Euclidean d | ε < ‖z‖} := by
  have hc := constant_pos d
  have hcf : HasCompactSupport (fun z : Euclidean d => f (x - z)) := by
    simpa [Function.comp_def] using hfc.comp_homeomorph (Homeomorph.subLeft x)
  have hi : Integrable (fun z : Euclidean d => f (x - z)) :=
    (hf.comp (by fun_prop)).integrable_of_hasCompactSupport hcf
  apply hi.restrict.bdd_mul ((kernel_measurable j).complex_ofReal.aestronglyMeasurable.restrict)
    (c := constant d / ε ^ d)
  filter_upwards [self_mem_ae_restrict (show MeasurableSet {z : Euclidean d | ε < ‖z‖} by measurability)]
    with z hz
  simp only [Complex.norm_real]
  exact (kernel_size j z).trans (div_le_div_of_nonneg_left hc.le (pow_pos hε d)
    (pow_le_pow_left₀ hε.le hz.le d))

lemma truncation_odd {d : ℕ} (j : Fin d) {f : Euclidean d → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε)
    (x : Euclidean d) :
    P102.Specs.U3.Riesz.truncation j ε f x =
      ∫ z in {z : Euclidean d | ε < ‖z‖}, oddIntegrand j f x z := by
  let u : Euclidean d → ℂ := fun z => (kernel d j z : ℂ) * f (x - z)
  let s : Set (Euclidean d) := {z | ε < ‖z‖}
  have hi : IntegrableOn u s := truncation_integrable j hf hfc hε x
  have hs : Neg.neg ⁻¹' s = s := by ext z; simp [s]
  have hp := Measure.measurePreserving_neg (volume : Measure (Euclidean d))
  have hni : IntegrableOn (fun z => u (-z)) s := by
    have h := (hp.integrableOn_comp_preimage (MeasurableEquiv.neg _).measurableEmbedding).mpr hi
    simpa [hs, Function.comp_def] using h
  have hne := hp.setIntegral_preimage_emb (MeasurableEquiv.neg _).measurableEmbedding u s
  change (∫ z in Neg.neg ⁻¹' s, u (-z)) = _ at hne
  rw [hs] at hne
  have he (z : Euclidean d) : oddIntegrand j f x z = (u z + u (-z)) / 2 := by
    simp [oddIntegrand, u, kernel_odd, sub_neg_eq_add]
    ring
  simp_rw [he]
  rw [integral_div, integral_add hi hni, hne]
  change (∫ z in s, u z) = ((∫ z in s, u z) + ∫ z in s, u z) / 2
  ring

lemma principalValue_limit {d : ℕ} (hd : 1 ≤ d) (j : Fin d)
    {f : Euclidean d → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (x : Euclidean d) :
    Tendsto (fun ε => P102.Specs.U3.Riesz.truncation j ε f x) (𝓝[>] 0)
      (𝓝 (∫ z, oddIntegrand j f x z)) := by
  let : Nonempty (Fin d) := ⟨j⟩
  have hi := oddIntegrand_integrable hd j hf hfc x
  have hlim : Tendsto (fun ε : ℝ => ∫ z in {z : Euclidean d | ε < ‖z‖}, oddIntegrand j f x z)
      (𝓝[>] 0) (𝓝 (∫ z, oddIntegrand j f x z)) := by
    have hind (ε : ℝ) : (∫ z in {z : Euclidean d | ε < ‖z‖}, oddIntegrand j f x z) =
        ∫ z, {z : Euclidean d | ε < ‖z‖}.indicator (oddIntegrand j f x) z :=
      (integral_indicator (by measurability)).symm
    simp_rw [hind]
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖oddIntegrand j f x z‖)
    · exact Eventually.of_forall fun ε => hi.aestronglyMeasurable.indicator (by measurability)
    · exact Eventually.of_forall fun ε => Eventually.of_forall fun z =>
        norm_indicator_le_norm_self _ _
    · exact hi.norm
    · filter_upwards [volume.ae_ne (0 : Euclidean d)] with z hz
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      apply tendsto_const_nhds.congr'
      filter_upwards [((tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const hzpos)]
        with ε hε
      change ε < ‖z‖ at hε
      simp [hε]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (truncation_odd j hf.continuous hfc hε x).symm

/-- The actual everywhere-defined ordinary principal value on smooth compact inputs.
The absolute odd-part formula also totalizes a value for other functions. -/
def principalValue : (d : ℕ) → Fin d → (Euclidean d → ℂ) → Euclidean d → ℂ :=
  fun _ j f x => ∫ z, oddIntegrand j f x z

theorem principal_value_exists : P102.Specs.U3.Riesz.principalValueExistsStatement := by
  intro d hd j f hf hfc
  refine ⟨hf.continuous.memLp_of_hasCompactSupport hfc, ?_, ?_⟩
  · intro ε hε x
    exact truncation_integrable j hf.continuous hfc hε x
  · intro x
    exact principalValue_limit hd j hf hfc x

def heatInterval (n : ℕ) : Set ℝ := Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)
lemma heatInterval_mono : Monotone heatInterval := by
  intro n m hnm
  apply Icc_subset_Icc
  · gcongr
  · exact_mod_cast Nat.add_le_add_right hnm 1
lemma heatInterval_subset (n : ℕ) : heatInterval n ⊆ Ioi (0 : ℝ) := by
  intro t ht
  exact lt_of_lt_of_le (by positivity) ht.1
lemma heatInterval_iUnion : (⋃ n, heatInterval n) = Ioi (0 : ℝ) := by
  apply Subset.antisymm
  · exact iUnion_subset heatInterval_subset
  · intro t ht
    obtain ⟨n, hn⟩ := exists_nat_gt (max t t⁻¹)
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩
    · have hn' : t⁻¹ < (n : ℝ) + 1 := by linarith [le_max_right t t⁻¹]
      exact (one_div_le (by positivity) ht).mpr (by simpa [one_div] using hn'.le)
    · linarith [le_max_left t t⁻¹]

lemma physical_integrable (d : ℕ) {x : Euclidean d} (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ (-((d : ℝ) + 3) / 2) *
      Real.exp (-Real.pi * ‖x‖ ^ 2 / t)) (Ioi 0) := by
  by_contra hi
  have h := physical_integral d hx
  rw [integral_undef hi] at h
  have hp : 0 < constant d / ‖x‖ ^ (d + 1) := by
    exact div_pos (constant_pos d) (pow_pos (norm_pos_iff.mpr hx) _)
  linarith

def heatKernel {d : ℕ} (j : Fin d) (n : ℕ) (x : Euclidean d) : ℝ :=
  x j * ∫ t : ℝ in heatInterval n, t ^ (-((d : ℝ) + 3) / 2) *
    Real.exp (-Real.pi * ‖x‖ ^ 2 / t)

lemma heatKernel_tendsto {d : ℕ} (j : Fin d) (x : Euclidean d) :
    Tendsto (fun n => heatKernel j n x) atTop (𝓝 (kernel d j x)) := by
  by_cases hx : x = 0
  · subst x
    simp [heatKernel, kernel, P102.Specs.U3.Riesz.kernelValue]
  · have ht := tendsto_setIntegral_of_monotone (s := heatInterval) (fun _ => measurableSet_Icc)
      heatInterval_mono
      (show IntegrableOn _ (⋃ n, heatInterval n) from
        heatInterval_iUnion ▸ physical_integrable d hx)
    rw [heatInterval_iUnion, physical_integral d hx] at ht
    have hl := (tendsto_const_nhds (x := x j)).mul ht
    simpa [heatKernel, kernel, P102.Specs.U3.Riesz.kernelValue,
      div_eq_mul_inv, constant, mul_comm, mul_left_comm, mul_assoc] using hl

lemma heatKernel_bound {d : ℕ} (j : Fin d) (n : ℕ) (x : Euclidean d) :
    |heatKernel j n x| ≤ |kernel d j x| := by
  by_cases hx : x = 0
  · simp [hx, heatKernel, kernel, P102.Specs.U3.Riesz.kernelValue]
  · have hnonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ (-((d : ℝ) + 3) / 2) *
        Real.exp (-Real.pi * ‖x‖ ^ 2 / t) := by
      intro t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
    have hpos : 0 ≤ ∫ t in heatInterval n, t ^ (-((d : ℝ) + 3) / 2) *
        Real.exp (-Real.pi * ‖x‖ ^ 2 / t) :=
      setIntegral_nonneg measurableSet_Icc (fun t ht => hnonneg t (heatInterval_subset n ht))
    have hfull := setIntegral_mono_set (physical_integrable d hx)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hnonneg))
      (Eventually.of_forall (heatInterval_subset n))
    rw [physical_integral d hx] at hfull
    unfold heatKernel
    rw [abs_mul, abs_of_nonneg hpos]
    apply (mul_le_mul_of_nonneg_left hfull (abs_nonneg (x j))).trans_eq
    have hc := constant_pos d
    change |x j| * (constant d / ‖x‖ ^ (d + 1)) = |constant d * x j / ‖x‖ ^ (d + 1)|
    rw [abs_div, abs_mul, abs_of_pos hc, abs_pow, abs_of_nonneg (norm_nonneg x)]
    ring

lemma heatKernel_measurable {d : ℕ} (j : Fin d) (n : ℕ) : Measurable (heatKernel j n) := by
  have hm : Measurable (fun p : Euclidean d × ℝ =>
      p.2 ^ (-((d : ℝ) + 3) / 2) * Real.exp (-Real.pi * ‖p.1‖ ^ 2 / p.2)) := by fun_prop
  have hi := hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (heatInterval n))
  exact (by fun_prop : Measurable (fun z : Euclidean d => z j)).mul hi.measurable

def heatOddIntegrand {d : ℕ} (j : Fin d) (n : ℕ) (f : Euclidean d → ℂ)
    (x z : Euclidean d) : ℂ :=
  (heatKernel j n z : ℂ) * (f (x - z) - f (x + z)) / 2

lemma heatOddIntegrand_norm_le {d : ℕ} (j : Fin d) (n : ℕ) (f : Euclidean d → ℂ)
    (x z : Euclidean d) : ‖heatOddIntegrand j n f x z‖ ≤ ‖oddIntegrand j f x z‖ := by
  simp only [heatOddIntegrand, oddIntegrand, norm_div, norm_mul, Complex.norm_real]
  gcongr
  exact heatKernel_bound j n z

lemma heatOddIntegrand_integrable {d : ℕ} (hd : 1 ≤ d) (j : Fin d) (n : ℕ)
    {f : Euclidean d → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (x : Euclidean d) : Integrable (heatOddIntegrand j n f x) := by
  apply (oddIntegrand_integrable hd j hf hfc x).norm.mono'
  · have hm : Measurable (heatOddIntegrand j n f x) := by
      unfold heatOddIntegrand
      exact ((heatKernel_measurable j n).complex_ofReal.mul
        ((hf.continuous.measurable.comp (by fun_prop)).sub
          (hf.continuous.measurable.comp (by fun_prop)))).div_const 2
    exact hm.aestronglyMeasurable
  · exact Eventually.of_forall (heatOddIntegrand_norm_le j n f x)

lemma heatOddIntegral_tendsto {d : ℕ} (hd : 1 ≤ d) (j : Fin d)
    {f : Euclidean d → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (x : Euclidean d) : Tendsto (fun n => ∫ z, heatOddIntegrand j n f x z) atTop
      (𝓝 (principalValue d j f x)) := by
  apply tendsto_integral_of_dominated_convergence (fun z => ‖oddIntegrand j f x z‖)
  · intro n
    exact (heatOddIntegrand_integrable hd j n hf hfc x).aestronglyMeasurable
  · exact (oddIntegrand_integrable hd j hf hfc x).norm
  · exact fun n => Eventually.of_forall (heatOddIntegrand_norm_le j n f x)
  · apply Eventually.of_forall
    intro z
    have hl := ((Complex.continuous_ofReal.tendsto _).comp (heatKernel_tendsto j z)).mul_const
      ((f (x - z) - f (x + z)) / 2)
    simpa [heatOddIntegrand, oddIntegrand, div_eq_mul_inv, mul_assoc] using hl

lemma frequency_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) *
      Real.exp (-Real.pi * t * r ^ 2)) (Ioi 0) := by
  by_contra hi
  have h := frequency_integral hr
  rw [integral_undef hi] at h
  have hp : 0 < 1 / r := one_div_pos.mpr hr
  linarith

def heatSymbol {d : ℕ} (j : Fin d) (n : ℕ) (ξ : Euclidean d) : ℂ :=
  -Complex.I * (ξ j : ℂ) * ((∫ t : ℝ in heatInterval n, t ^ (-(1 / 2 : ℝ)) *
    Real.exp (-Real.pi * t * ‖ξ‖ ^ 2)) : ℝ)

lemma heatSymbol_measurable {d : ℕ} (j : Fin d) (n : ℕ) : Measurable (heatSymbol j n) := by
  have hm : Measurable (fun p : Euclidean d × ℝ =>
      p.2 ^ (-(1 / 2 : ℝ)) * Real.exp (-Real.pi * p.2 * ‖p.1‖ ^ 2)) := by fun_prop
  have hi := hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (heatInterval n))
  exact (measurable_const.mul ((by fun_prop : Measurable (fun ξ : Euclidean d => ξ j)).complex_ofReal)).mul
    hi.measurable.complex_ofReal

lemma heatSymbol_tendsto {d : ℕ} (j : Fin d) (ξ : Euclidean d) :
    Tendsto (fun n => heatSymbol j n ξ) atTop (𝓝 (symbol d j ξ)) := by
  by_cases hξ : ξ = 0
  · simp [hξ, heatSymbol, symbol, P102.Specs.U3.Riesz.symbolValue]
  · have ht := tendsto_setIntegral_of_monotone (s := heatInterval) (fun _ => measurableSet_Icc)
      heatInterval_mono
      (show IntegrableOn _ (⋃ n, heatInterval n) from
        heatInterval_iUnion ▸ frequency_integrable (norm_pos_iff.mpr hξ))
    rw [heatInterval_iUnion, frequency_integral (norm_pos_iff.mpr hξ)] at ht
    have hl := (tendsto_const_nhds (x := -Complex.I * (ξ j : ℂ))).mul
      (Complex.continuous_ofReal.tendsto _ |>.comp ht)
    simpa [heatSymbol, symbol, P102.Specs.U3.Riesz.symbolValue, Complex.ofReal_div,
      Complex.ofReal_one, div_eq_mul_inv, mul_assoc] using hl

lemma heatSymbol_norm_le {d : ℕ} (j : Fin d) (n : ℕ) (ξ : Euclidean d) : ‖heatSymbol j n ξ‖ ≤ 1 := by
  by_cases hξ : ξ = 0
  · simp [hξ, heatSymbol]
  · have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hnonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ (-(1 / 2 : ℝ)) *
        Real.exp (-Real.pi * t * ‖ξ‖ ^ 2) := by
      intro t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
    have hpos : 0 ≤ ∫ t in heatInterval n, t ^ (-(1 / 2 : ℝ)) *
        Real.exp (-Real.pi * t * ‖ξ‖ ^ 2) :=
      setIntegral_nonneg measurableSet_Icc (fun t ht => hnonneg t (heatInterval_subset n ht))
    have hfull := setIntegral_mono_set (frequency_integrable hr)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hnonneg))
      (Eventually.of_forall (heatInterval_subset n))
    rw [frequency_integral hr] at hfull
    calc
      _ = |ξ j| * (∫ t in heatInterval n, t ^ (-(1 / 2 : ℝ)) *
          Real.exp (-Real.pi * t * ‖ξ‖ ^ 2)) := by
        simp only [heatSymbol, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
        rw [abs_of_nonneg hpos]
      _ ≤ |ξ j| * (1 / ‖ξ‖) := mul_le_mul_of_nonneg_left hfull (abs_nonneg _)
      _ ≤ ‖ξ‖ * (1 / ‖ξ‖) := by
        gcongr
        exact PiLp.norm_apply_le ξ j
      _ = 1 := by field_simp


lemma heatKernel_odd {d : ℕ} (j : Fin d) (n : ℕ) (x : Euclidean d) :
    heatKernel j n (-x) = -heatKernel j n x := by
  simp [heatKernel]

def heatConvolution {d : ℕ} (j : Fin d) (n : ℕ) (f : Euclidean d → ℂ)
    (x : Euclidean d) : ℂ := ∫ z, (heatKernel j n z : ℂ) * f (x - z)

lemma heatConvolution_eq_odd {d : ℕ} (j : Fin d) (n : ℕ)
    (hK : Integrable (fun z : Euclidean d => (heatKernel j n z : ℂ)))
    {f : Euclidean d → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : Euclidean d) :
    heatConvolution j n f x = ∫ z, heatOddIntegrand j n f x z := by
  let u : Euclidean d → ℂ := fun z => (heatKernel j n z : ℂ) * f (x - z)
  have hb := (hfc.norm.isCompact_range hf.norm).bddAbove
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable u := hK.mul_bdd
    (hf.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun z => hC ⟨x-z, rfl⟩)
  have hp := Measure.measurePreserving_neg (volume : Measure (Euclidean d))
  have hni : Integrable (fun z => u (-z)) := hi.comp_neg
  have hne := hp.integral_comp (MeasurableEquiv.neg _).measurableEmbedding u
  have he (z : Euclidean d) : heatOddIntegrand j n f x z = (u z + u (-z)) / 2 := by
    simp [heatOddIntegrand, u, heatKernel_odd, sub_neg_eq_add]
    ring
  simp_rw [he]
  rw [integral_div, integral_add hi hni, hne]
  change (∫ z, u z) = ((∫ z, u z) + ∫ z, u z) / 2
  ring


lemma heatSymbol_memLp_top {d : ℕ} (j : Fin d) (n : ℕ) :
    MemLp (heatSymbol j n) (⊤ : ENNReal) volume :=
  memLp_top_of_bound (heatSymbol_measurable j n).aestronglyMeasurable 1
    (Eventually.of_forall (heatSymbol_norm_le j n))

def heatFrequencyMul {d : ℕ} (j : Fin d) (n : ℕ) : L2 d →L[ℂ] L2 d :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume (⊤ : ENNReal) 2 2
    ((heatSymbol_memLp_top j n).toLp _)

lemma heatFrequencyMul_ae {d : ℕ} (j : Fin d) (n : ℕ) (f : L2 d) :
    (heatFrequencyMul j n f : Euclidean d → ℂ) =ᵐ[volume]
      fun ξ => heatSymbol j n ξ * f ξ := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((heatSymbol_memLp_top j n).toLp _) f, (heatSymbol_memLp_top j n).coeFn_toLp]
    with ξ hξ hm
  simpa [heatFrequencyMul, hm] using hξ

lemma l2_norm_sq_integral {d : ℕ} (f : L2 d) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

lemma heatFrequencyMul_tendsto {d : ℕ} (j : Fin d) (f : L2 d) :
    Tendsto (fun n => heatFrequencyMul j n f) atTop (𝓝 (frequencyMul j f)) := by
  have hlim : Tendsto (fun n => ∫ ξ, ‖heatSymbol j n ξ * f ξ - symbol d j ξ * f ξ‖ ^ 2)
      atTop (𝓝 0) := by
    have hb : Integrable (fun ξ => (2 * ‖f ξ‖) ^ 2) :=
      ((Lp.memLp f).norm.const_mul 2).integrable_sq
    have h := tendsto_integral_of_dominated_convergence (fun ξ => (2 * ‖f ξ‖) ^ 2)
      (μ := volume) (F := fun n ξ => ‖heatSymbol j n ξ * f ξ - symbol d j ξ * f ξ‖ ^ 2)
      (f := fun _ => (0 : ℝ))
    simp only [integral_zero] at h
    apply h
    · intro n
      exact ((((heatSymbol_measurable j n).aestronglyMeasurable.mul
        (Lp.memLp f).aestronglyMeasurable).sub
        ((symbol_measurable j).aestronglyMeasurable.mul
          (Lp.memLp f).aestronglyMeasurable)).norm.pow 2)
    · exact hb
    · intro n
      apply Eventually.of_forall
      intro ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      calc
        ‖heatSymbol j n ξ * f ξ - symbol d j ξ * f ξ‖
          ≤ ‖heatSymbol j n ξ * f ξ‖ + ‖symbol d j ξ * f ξ‖ := norm_sub_le _ _
        _ ≤ 1 * ‖f ξ‖ + 1 * ‖f ξ‖ := by
          simp only [norm_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right (heatSymbol_norm_le j n ξ) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (symbol_norm_le_one j ξ) (norm_nonneg _))
        _ = 2 * ‖f ξ‖ := by ring
    · apply Eventually.of_forall
      intro ξ
      have ht := ((heatSymbol_tendsto j ξ).mul_const (f ξ)).sub_const (symbol d j ξ * f ξ)
      simpa using ht.norm.pow 2
  have hsq (n : ℕ) : ‖heatFrequencyMul j n f - frequencyMul j f‖ ^ 2 =
      ∫ ξ, ‖heatSymbol j n ξ * f ξ - symbol d j ξ * f ξ‖ ^ 2 := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (heatFrequencyMul j n f) (frequencyMul j f),
      heatFrequencyMul_ae j n f, frequencyMul_ae j f] with ξ hs hh hr
    simp only [hs, Pi.sub_apply, hh, hr]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  simp only [Real.sqrt_zero] at hsqrt
  convert hsqrt using 1
  ext n
  rw [Function.comp_apply, ← hsq, Real.sqrt_sq (norm_nonneg _)]

def heatRieszL2 {d : ℕ} (j : Fin d) (n : ℕ) : L2 d →L[ℂ] L2 d :=
  (F2 d).symm.toContinuousLinearEquiv.toContinuousLinearMap
    ∘L heatFrequencyMul j n ∘L
    (F2 d).toContinuousLinearEquiv.toContinuousLinearMap

lemma heatRieszL2_frequency {d : ℕ} (j : Fin d) (n : ℕ) (f : L2 d) :
    F2 d (heatRieszL2 j n f) = heatFrequencyMul j n (F2 d f) := by
  exact (F2 d).apply_symm_apply _

lemma heatRieszL2_tendsto {d : ℕ} (j : Fin d) (f : L2 d) :
    Tendsto (fun n => heatRieszL2 j n f) atTop (𝓝 (rieszL2 j f)) := by
  exact (F2 d).symm.continuous.continuousAt.tendsto.comp
    (heatFrequencyMul_tendsto j (F2 d f))

lemma heatRieszL2_ae_subsequence {d : ℕ} (j : Fin d) (f : L2 d) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂volume, Tendsto (fun n => (heatRieszL2 j (ns n) f : Euclidean d → ℂ) x)
        atTop (𝓝 ((rieszL2 j f : Euclidean d → ℂ) x)) := by
  exact (tendstoInMeasure_of_tendsto_Lp (heatRieszL2_tendsto j f)).exists_seq_tendsto_ae

lemma principalValue_eq_rieszL2_of_heat {d : ℕ} (hd : 1 ≤ d) (j : Fin d)
    {f : Euclidean d → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hf2 : MemLp f 2 volume)
    (hfinite : ∀ n, (heatRieszL2 j n (hf2.toLp f) : Euclidean d → ℂ) =ᵐ[volume]
      fun x => ∫ z, heatOddIntegrand j n f x z) :
    ∃ hg : MemLp (principalValue d j f) 2 volume,
      hg.toLp (principalValue d j f) = rieszL2 j (hf2.toLp f) := by
  obtain ⟨ns, hns, hlim⟩ := heatRieszL2_ae_subsequence j (hf2.toLp f)
  have hae : (rieszL2 j (hf2.toLp f) : Euclidean d → ℂ) =ᵐ[volume]
      principalValue d j f := by
    filter_upwards [hlim, ae_all_iff.mpr hfinite] with x hx hfx
    have hphys := (heatOddIntegral_tendsto hd j hf hfc x).comp hns.tendsto_atTop
    have hsame : (fun n => (heatRieszL2 j (ns n) (hf2.toLp f) : Euclidean d → ℂ) x) =
        (fun n => ∫ z, heatOddIntegrand j (ns n) f x z) := by
      funext n
      exact hfx (ns n)
    rw [hsame] at hx
    exact tendsto_nhds_unique hx hphys
  have hg : MemLp (principalValue d j f) 2 volume :=
    (Lp.memLp (rieszL2 j (hf2.toLp f))).ae_eq hae
  refine ⟨hg, Lp.ext (hg.coeFn_toLp.trans hae.symm)⟩



 theorem convolution_L2_fourier {d : ℕ}
    (k f m : Euclidean d → ℂ) (hk : Integrable k)
    (hf : MemLp f 2 volume) (hf1 : Integrable f)
    (hkF : 𝓕 k = m) :
    ∃ hc : MemLp (fun x => ∫ z, k z * f (x-z)) 2 volume,
      (F2 d (hc.toLp _) : Euclidean d → ℂ) =ᵐ[volume]
        fun ξ => m ξ * (F2 d (hf.toLp f) : Euclidean d → ℂ) ξ := by
  let c : Euclidean d → ℂ := fun x => ∫ z, k z * f (x-z)
  have hYoung := P102.U2.Young.young volume (p := 2) (q := 1) (r := 2)
    (by norm_num) (by norm_num) (by norm_num) (by simp [add_comm])
    hf (memLp_one_iff_integrable.mpr hk)
  have hc : MemLp c 2 volume := by
    convert hYoung.2.1 using 1
    funext x
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => mul_comm _ _)
  have hc1 : Integrable c := by
    exact hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf1
  have hcF : (F2 d (hc.toLp c) : Euclidean d → ℂ) =ᵐ[volume] 𝓕 c :=
    P102.U3.Plancherel.integral_compatibility c hc hc1
  have hfF : (F2 d (hf.toLp f) : Euclidean d → ℂ) =ᵐ[volume] 𝓕 f :=
    P102.U3.Plancherel.integral_compatibility f hf hf1
  refine ⟨hc, ?_⟩
  filter_upwards [hcF, hfF] with ξ hcξ hfξ
  rw [hcξ, hfξ]
  change 𝓕 (MeasureTheory.convolution k f (ContinuousLinearMap.mul ℂ ℂ) volume) ξ = _
  rw [Real.fourier_mul_convolution_eq hk hf1, hkF]


 theorem identify_Lp_limit_of_pointwise
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ENNReal} [Fact (1 ≤ p)]
    (u : ℕ → α → E) (hu : ∀ n, MemLp (u n) p μ)
    (v : Lp E p μ) (g : α → E)
    (hLp : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 v))
    (hpoint : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (g x))) :
    ∃ hg : MemLp g p μ, hg.toLp g = v := by
  have hmeasure : TendstoInMeasure μ u atTop v :=
    (tendstoInMeasure_of_tendsto_Lp hLp).congr_left
      (fun n => (hu n).coeFn_toLp)
  obtain ⟨ns, hns, hsub⟩ := hmeasure.exists_seq_tendsto_ae
  have heq : g =ᵐ[μ] (v : α → E) := by
    filter_upwards [hsub] with x hx
    exact tendsto_nhds_unique ((hpoint x).comp hns.tendsto_atTop) hx
  have hg : MemLp g p μ := (Lp.memLp v).ae_eq heq.symm
  refine ⟨hg, ?_⟩
  apply Lp.ext
  exact hg.coeFn_toLp.trans heq




lemma heatConvolution_L2 {d : ℕ} (j : Fin d) (n : ℕ)
    (hK : Integrable (fun z : Euclidean d => (heatKernel j n z : ℂ)))
    (hF : 𝓕 (fun z : Euclidean d => (heatKernel j n z : ℂ)) = heatSymbol j n)
    {f : Euclidean d → ℂ} (hf2 : MemLp f 2 volume) (hf1 : Integrable f) :
    ∃ hc : MemLp (heatConvolution j n f) 2 volume,
      hc.toLp _ = heatRieszL2 j n (hf2.toLp f) := by
  obtain ⟨hc, hcf⟩ := convolution_L2_fourier (fun z => (heatKernel j n z : ℂ)) f
    (heatSymbol j n) hK hf2 hf1 hF
  refine ⟨hc, ?_⟩
  apply (F2 d).injective
  rw [heatRieszL2_frequency]
  apply Lp.ext
  exact hcf.trans (heatFrequencyMul_ae j n (F2 d (hf2.toLp f))).symm

lemma principal_value_of_heat_fourier
    (hK : ∀ {d : ℕ} (j : Fin d) n, Integrable (fun z : Euclidean d => (heatKernel j n z : ℂ)))
    (hF : ∀ {d : ℕ} (j : Fin d) n,
      𝓕 (fun z : Euclidean d => (heatKernel j n z : ℂ)) = heatSymbol j n) :
    P102.Specs.U3.Riesz.principalValueStatement := by
  intro d hd j a R hR f hf hfc
  obtain ⟨hf2, htr, hlim⟩ := principal_value_exists d hd j f hf hfc
  refine ⟨htr, principalValue d j f, hf2, ?_⟩
  have hf1 : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hc (n : ℕ) := (heatConvolution_L2 j n (hK j n) (hF j n) hf2 hf1).choose
  have hceq (n : ℕ) : (hc n).toLp _ = heatRieszL2 j n (hf2.toLp f) :=
    (heatConvolution_L2 j n (hK j n) (hF j n) hf2 hf1).choose_spec
  have hlp : Tendsto (fun n => (hc n).toLp _) atTop (𝓝 (rieszL2 j (hf2.toLp f))) := by
    simp_rw [hceq]
    exact heatRieszL2_tendsto j _
  have hpoint (x : Euclidean d) :
      Tendsto (fun n => heatConvolution j n f x) atTop (𝓝 (principalValue d j f x)) := by
    simp_rw [heatConvolution_eq_odd j _ (hK j _) hf.continuous hfc]
    exact heatOddIntegral_tendsto hd j hf hfc x
  obtain ⟨hg, hgeq⟩ := identify_Lp_limit_of_pointwise (fun n => heatConvolution j n f)
    hc (rieszL2 j (hf2.toLp f)) (principalValue d j f) hlp hpoint
  refine ⟨hg, hlim, ?_⟩
  rw [hgeq]
  have hRc : IsMultiplier j a (rieszL2 j) := by
    intro u
    rw [rieszL2_frequency]
    filter_upwards [frequencyMul_ae j (F2 d u), symbol_origin_ae j a] with ξ hξ ha
    rw [hξ, ha]
  exact congrArg (fun S : L2 d →L[ℂ] L2 d => S (hf2.toLp f))
    (multiplier_unique d hd j a a (rieszL2 j) R hRc hR)


/-! Finite heat-kernel normalization and the Fourier interchange. -/

lemma gaussian_coordinate_fderiv {d : ℕ} (j : Fin d) {t : ℝ} (_ht : 0 < t)
    (x : Euclidean d) :
    fderiv ℝ (P102.U3.gaussianComplex d t) x (coordinateVector j) =
      ((-2 * Real.pi / t * x j : ℝ) : ℂ) * P102.U3.gaussianComplex d t x := by
  let A : ℝ := t ^ (-(d : ℝ) / 2)
  let B : ℝ := -Real.pi / t
  have he : P102.U3.gaussianComplex d t =
      fun y : Euclidean d => ((A * Real.exp (B * ‖y‖ ^ 2) : ℝ) : ℂ) := by
    ext y
    simp only [P102.U3.gaussianComplex, P102.Specs.U3.gaussianComplexValue,
      P102.Specs.U3.gaussianValue, A, B]
    congr 3; ring
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul B).exp.const_mul A)
  have hh := (Complex.ofRealCLM.hasFDerivAt).comp x h
  rw [he]
  change (fderiv ℝ (Complex.ofRealCLM ∘ (fun y : Euclidean d => A * Real.exp (B * ‖y‖ ^ 2))) x)
      (coordinateVector j) = _
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    smul_apply, smul_eq_mul, innerSL_apply_apply,
    coordinateVector, EuclideanSpace.inner_basisFun_real]
  dsimp [B]
  push_cast
  ring

lemma gaussian_coordinate_fourier {d : ℕ} (j : Fin d) {t : ℝ} (ht : 0 < t)
    (ξ : Euclidean d) :
    𝓕 (fun x : Euclidean d => (x j : ℂ) * P102.U3.gaussianComplex d t x) ξ =
      -Complex.I * (t * ξ j : ℝ) * (Real.exp (-Real.pi * t * ‖ξ‖ ^ 2) : ℂ) := by
  obtain ⟨φ, hφ⟩ := P102.U3.gaussian_schwartz d ht
  have hdφ : LineDeriv.lineDerivOp (coordinateVector j) φ =
      ((-2 * Real.pi / t : ℝ) : ℂ) • coordinateMul j φ := by
    ext x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_apply, coordinateMul_apply,
      hφ, gaussian_coordinate_fderiv j ht]
    simp only [smul_eq_mul]
    push_cast
    ring
  have hf := congrArg (fun f : Test d => f ξ) (SchwartzMap.fourier_lineDerivOp_eq φ (coordinateVector j))
  rw [hdφ, FourierTransform.fourier_smul] at hf
  have hgf : (𝓕 φ) ξ = (Real.exp (-Real.pi * t * ‖ξ‖ ^ 2) : ℂ) := by
    change 𝓕 (φ : Euclidean d → ℂ) ξ = _
    rw [Real.fourier_eq', hφ]
    simpa only [smul_eq_mul] using P102.U3.gaussian_fourier d ht ξ
  simp only [smul_apply, smul_eq_mul] at hf
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)] at hf
  simp only [coordinateVector, EuclideanSpace.inner_basisFun_real, Complex.real_smul] at hf
  rw [hgf] at hf
  rw [← hφ]
  rw [show (fun x : Euclidean d => (x j : ℂ) * φ x) =
      (coordinateMul j φ : Euclidean d → ℂ) by ext x; simp]
  change (𝓕 (coordinateMul j φ)) ξ = _
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast at hf ⊢
  apply mul_left_cancel₀ (show (-2 * (Real.pi : ℂ) / t) ≠ 0 by simp [hpC, htC])
  rw [hf]
  field_simp

lemma heatSlice_fourier {d : ℕ} (j : Fin d) {t : ℝ} (ht : 0 < t)
    (ξ : Euclidean d) :
    𝓕 (fun x : Euclidean d => ((x j * t ^ (-((d : ℝ) + 3) / 2) *
      Real.exp (-Real.pi * ‖x‖ ^ 2 / t) : ℝ) : ℂ)) ξ =
      -Complex.I * (ξ j : ℂ) * ((t ^ (-(1 / 2 : ℝ)) *
        Real.exp (-Real.pi * t * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
  have he : (fun x : Euclidean d => ((x j * t ^ (-((d : ℝ) + 3) / 2) *
      Real.exp (-Real.pi * ‖x‖ ^ 2 / t) : ℝ) : ℂ)) =
      fun x => ((t ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((x j : ℂ) * P102.U3.gaussianComplex d t x) := by
    ext x
    simp only [P102.U3.gaussianComplex, P102.Specs.U3.gaussianComplexValue,
      P102.Specs.U3.gaussianValue, ← Complex.ofReal_mul]
    congr 1
    have hp : t ^ (-((d : ℝ) + 3) / 2) =
        t ^ (-(3 / 2 : ℝ)) * t ^ (-(d : ℝ) / 2) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    rw [hp]
    ring
  rw [he, Real.fourier_eq']
  simp only [smul_eq_mul]
  simp_rw [mul_left_comm (Complex.exp _) ((t ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)]
  rw [integral_const_mul]
  have hf := gaussian_coordinate_fourier j ht ξ
  rw [Real.fourier_eq'] at hf
  simp only [smul_eq_mul] at hf
  rw [hf]
  have he2 : t ^ (-(3 / 2 : ℝ)) * t = t ^ (-(1 / 2 : ℝ)) := by
    conv_lhs => rhs; rw [← Real.rpow_one t]
    rw [← Real.rpow_add ht]
    congr 1
    norm_num
  push_cast
  calc
    _ = -Complex.I * (ξ j : ℂ) * (((t ^ (-(3 / 2 : ℝ)) * t : ℝ) : ℂ) *
        (Real.exp (-Real.pi * t * ‖ξ‖ ^ 2) : ℂ)) := by push_cast; ring
    _ = _ := by rw [he2]; push_cast; ring

lemma heatKernel_integral_form {d : ℕ} (j : Fin d) (n : ℕ) (x : Euclidean d) :
    (heatKernel j n x : ℂ) = ∫ t in heatInterval n,
      ((x j * t ^ (-((d : ℝ) + 3) / 2) * Real.exp (-Real.pi * ‖x‖ ^ 2 / t) : ℝ) : ℂ) := by
  rw [integral_complex_ofReal]
  congr 1
  simp only [heatKernel, mul_assoc]
  rw [integral_const_mul]

lemma heatSymbol_integral_form {d : ℕ} (j : Fin d) (n : ℕ) (ξ : Euclidean d) :
    heatSymbol j n ξ = ∫ t in heatInterval n,
      -Complex.I * (ξ j : ℂ) * ((t ^ (-(1 / 2 : ℝ)) *
        Real.exp (-Real.pi * t * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
  rw [integral_const_mul, integral_complex_ofReal]
  rfl


lemma coordinate_exp_integrable {d : ℕ} (j : Fin d) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Euclidean d => |x j| * Real.exp (-Real.pi * ‖x‖ ^ 2 / b)) := by
  obtain ⟨φ, hφ⟩ := P102.U3.gaussian_schwartz d hb
  let B : ℝ := b ^ (-(d : ℝ) / 2)
  have hB : B ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  have hn (x : Euclidean d) :
      ‖coordinateMul j φ x‖ = B * (|x j| * Real.exp (-Real.pi * ‖x‖ ^ 2 / b)) := by
    rw [coordinateMul_apply, hφ]
    simp only [P102.U3.gaussianComplex, P102.Specs.U3.gaussianComplexValue,
      P102.Specs.U3.gaussianValue, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hb _), abs_of_pos (Real.exp_pos _)]
    dsimp [B]
    ring
  have hi := ((coordinateMul j φ).integrable (μ := (volume : Measure (Euclidean d)))).norm.const_mul B⁻¹
  convert hi using 1
  funext x
  rw [hn]
  field_simp

lemma joint_heat_integrable {d : ℕ} (j : Fin d) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun p : ℝ × Euclidean d =>
      ((p.2 j * p.1 ^ (-((d : ℝ) + 3) / 2) *
        Real.exp (-Real.pi * ‖p.2‖ ^ 2 / p.1) : ℝ) : ℂ))
      ((volume.restrict (Icc a b)).prod volume) := by
  let q : ℝ := -((d : ℝ) + 3) / 2
  have hq : q ≤ 0 := by dsimp [q]; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  let A : ℝ := a ^ q
  have hA : 0 ≤ A := Real.rpow_nonneg ha.le _
  have hm := (coordinate_exp_integrable j hb).const_mul A
  have hdom : Integrable (fun p : ℝ × Euclidean d =>
      A * (|p.2 j| * Real.exp (-Real.pi * ‖p.2‖ ^ 2 / b)))
      ((volume.restrict (Icc a b)).prod volume) :=
    hm.comp_snd _
  apply hdom.mono'
  · have hm' : Measurable (fun p : ℝ × Euclidean d =>
        ((p.2 j * p.1 ^ q * Real.exp (-Real.pi * ‖p.2‖ ^ 2 / p.1) : ℝ) : ℂ)) := by
      fun_prop
    exact hm'.aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with p hp
    have ht : 0 < p.1 := ha.trans_le hp.1
    have hpow : p.1 ^ q ≤ A := Real.rpow_le_rpow_of_nonpos ha hp.1 hq
    have hexp : Real.exp (-Real.pi * ‖p.2‖ ^ 2 / p.1) ≤
        Real.exp (-Real.pi * ‖p.2‖ ^ 2 / b) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff₀ ht hb).2
      have hn : -Real.pi * ‖p.2‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)
      exact mul_le_mul_of_nonpos_left hp.2 hn
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos ht _), abs_of_pos (Real.exp_pos _)]
    calc
      |p.2 j| * p.1 ^ q * Real.exp (-Real.pi * ‖p.2‖ ^ 2 / p.1)
          ≤ |p.2 j| * A * Real.exp (-Real.pi * ‖p.2‖ ^ 2 / b) := by gcongr
      _ = _ := by ring

lemma heat_joint_integrable {d : ℕ} (j : Fin d) (n : ℕ) :
    Integrable (fun p : ℝ × Euclidean d =>
      ((p.2 j * p.1 ^ (-((d : ℝ) + 3) / 2) *
        Real.exp (-Real.pi * ‖p.2‖ ^ 2 / p.1) : ℝ) : ℂ))
      ((volume.restrict (heatInterval n)).prod volume) := by
  simpa only [heatInterval] using
    (joint_heat_integrable j
      (show 0 < 1 / ((n : ℝ) + 1) by positivity)
      (show 0 < (n : ℝ) + 1 by positivity))


lemma fourier_integral_parameter {d : ℕ} (s : Set ℝ)
    (q : ℝ → Euclidean d → ℂ)
    (hq : Integrable (fun p : ℝ × Euclidean d => q p.1 p.2)
      ((volume.restrict s).prod volume)) (ξ : Euclidean d) :
    𝓕 (fun x => ∫ t in s, q t x) ξ = ∫ t in s, 𝓕 (q t) ξ := by
  let κ : Euclidean d → ℂ := fun x =>
    Complex.exp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I)
  have hκ : Continuous κ := by fun_prop
  have hnκ (x : Euclidean d) : ‖κ x‖ = 1 := by
    simp [κ, Complex.norm_exp]
  have hqi : Integrable (fun p : ℝ × Euclidean d => κ p.2 * q p.1 p.2)
      ((volume.restrict s).prod volume) := by
    apply hq.bdd_mul (hκ.comp continuous_snd).aestronglyMeasurable (c := 1)
    exact Eventually.of_forall fun p => (hnκ p.2).le
  calc
    _ = ∫ x, κ x * ∫ t in s, q t x := by
      rw [Real.fourier_eq']
      rfl
    _ = ∫ x, ∫ t in s, κ x * q t x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => (integral_const_mul (κ x) _).symm
    _ = ∫ t in s, ∫ x, κ x * q t x :=
      (integral_integral_swap hqi).symm
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      change (∫ x, κ x * q t x) = 𝓕 (q t) ξ
      rw [Real.fourier_eq']
      rfl

lemma heatKernel_complex_integrable {d : ℕ} (j : Fin d) (n : ℕ) :
    Integrable (fun x : Euclidean d => (heatKernel j n x : ℂ)) := by
  have hi := (heat_joint_integrable j n).integral_prod_right
  simpa only [← heatKernel_integral_form] using hi

lemma heatKernel_fourier {d : ℕ} (j : Fin d) (n : ℕ) :
    𝓕 (fun x : Euclidean d => (heatKernel j n x : ℂ)) = heatSymbol j n := by
  ext ξ
  rw [heatSymbol_integral_form]
  have he : (fun x : Euclidean d => (heatKernel j n x : ℂ)) =
      fun x => ∫ t in heatInterval n,
        ((x j * t ^ (-((d : ℝ) + 3) / 2) * Real.exp (-Real.pi * ‖x‖ ^ 2 / t) : ℝ) : ℂ) := by
    ext x
    exact heatKernel_integral_form j n x
  rw [he, fourier_integral_parameter _ _ (heat_joint_integrable j n)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (show MeasurableSet (heatInterval n) from measurableSet_Icc)] with t ht
  exact heatSlice_fourier j (heatInterval_subset n ht) ξ


/-- The ordinary physical principal value is the canonical L² Riesz multiplier. -/
theorem principal_value_identification : P102.Specs.U3.Riesz.principalValueStatement :=
  principal_value_of_heat_fourier heatKernel_complex_integrable heatKernel_fourier

end P102.U3.Riesz
