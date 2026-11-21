import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyCompactTransfer
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyLowpass
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.TaylorIntegral

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ContDiff Convolution Topology

namespace ExpandedFA.PartIV.HardyCompactTransfer
open ExpandedFA.Fourier HardyMaximalSpec HardyLowpassSpec HardyCompactTransferSpec

/-- An individual summand is bounded by the literal pointwise Peetre supremum.
The finite-value hypothesis is essential when passing to real values. -/
lemma lowpass_le_peetre {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (f : Euclidean d → 𝕜) (x : Euclidean d)
    (hP : peetre η f x < ⊤) (j : ℤ) (y : Euclidean d) :
    ‖convolve (dilate ((2 : ℝ) ^ (-j)) η) f y‖ ≤
      (peetre η f x).toReal * (1 + (2 : ℝ) ^ j * ‖x - y‖) ^ peetreExponent d := by
  have hden : 0 < (1 + (2 : ℝ) ^ j * ‖x - y‖) ^ peetreExponent d := by
    positivity
  have hs : ENNReal.ofReal
      (‖convolve (dilate ((2 : ℝ) ^ (-j)) η) f y‖ /
        (1 + (2 : ℝ) ^ j * ‖x - y‖) ^ peetreExponent d) ≤ peetre η f x :=
    le_iSup_of_le j (le_iSup_of_le y le_rfl)
  have hr := (ENNReal.ofReal_le_iff_le_toReal hP.ne).mp hs
  exact (div_le_iff₀ hden).mp hr

/-- Taking the grand supremum uses the same constant for all tests. -/
theorem grand_from_estimate : GrandFromEstimate := by
  intro 𝕜 _ d N η C hC h f hf x
  by_cases hP : peetre η f x = ⊤
  · simp [hP, ne_of_gt (ENNReal.ofReal_pos.mpr hC)]
  · have hPf : peetre η f x < ⊤ := lt_top_iff_ne_top.mpr hP
    apply iSup_le
    intro t
    apply iSup_le
    intro ψ
    have hb := h f hf x hPf ψ t.val t.property x
    simp only [sub_self, norm_zero, zero_div, add_zero, one_pow, mul_one] at hb
    calc
      ENNReal.ofReal ‖convolve (dilate t.val ψ.val) f x‖ ≤
          ENNReal.ofReal (C * (peetre η f x).toReal) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal C * peetre η f x := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hP]

lemma transfer_estimate_mono {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    (η : Schwartz 𝕜 d) {C D : ℝ} (hCD : C ≤ D)
    (h : TransferEstimate η N C) : TransferEstimate η N D := by
  intro f hf x hP ψ t ht z
  exact (h f hf x hP ψ t ht z).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD ENNReal.toReal_nonneg) (by positivity))

theorem grand_from_compact : GrandFromCompact := by
  intro h 𝕜 _ d hd N hN η R hη
  obtain ⟨C, hC, hb⟩ := h hd N hN η R hη
  refine ⟨C + 1, by positivity, ?_⟩
  exact grand_from_estimate η (C + 1) (by positivity)
    (transfer_estimate_mono η (by linarith) hb)

/-- Coordinate derivatives behave literally under real scalar multiplication. -/
lemma coordinatePartial_const_smul {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (v : Fin k → Fin d) (ψ : Euclidean d → 𝕜) (hψ : ContDiff ℝ ∞ ψ)
    (c : ℝ) (x : Euclidean d) :
    coordinatePartial v (fun y => c • ψ y) x = c • coordinatePartial v ψ x := by
  unfold coordinatePartial
  rw [iteratedFDeriv_const_smul_apply' (hψ.of_le (by simp)).contDiffAt]
  rfl

lemma coordinatePartial_comp_smul {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (v : Fin k → Fin d) (ψ : Euclidean d → 𝕜) (hψ : ContDiff ℝ ∞ ψ)
    (s : ℝ) (x : Euclidean d) :
    coordinatePartial v (fun y => ψ (s • y)) x =
      s ^ k • coordinatePartial v ψ (s • x) := by
  unfold coordinatePartial
  rw [iteratedFDeriv_comp_const_smul s (hψ.of_le (by simp))]
  rfl

/-- Normalize a test with a common support radius and derivative bound.
Taking s ≥ 1 and K ≥ B s^N also covers B = 0 without dividing by zero. -/
lemma normalize_uniform_test {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {a B s K : ℝ} (ψ : Euclidean d → 𝕜) (hψ : IsUniformTest N a B ψ)
    (hs : 1 ≤ s) (has : a ≤ s) (hK : 0 < K) (hBK : B * s ^ N ≤ K) :
    IsTest N (fun y => K⁻¹ • ψ (s • y)) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hcomp : ContDiff ℝ ∞ (fun y => ψ (s • y)) := by
    exact hψ.1.comp (contDiff_id.const_smul s)
  refine ⟨hcomp.const_smul _, ?_, ?_⟩
  · intro y hy
    have hy' : s • y ∈ tsupport ψ :=
      tsupport_comp_subset_preimage (f := fun y : Euclidean d => s • y) ψ (by fun_prop)
        (tsupport_smul_subset_right (fun _ => K⁻¹) (fun y => ψ (s • y)) hy)
    have hnorm : s * ‖y‖ < a := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hs0] using hψ.2.1 hy'
    rw [Metric.mem_ball, dist_zero_right]
    nlinarith
  · intro k hk v y
    rw [coordinatePartial_const_smul v _ hcomp,
      coordinatePartial_comp_smul v ψ hψ.1]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK),
      abs_of_pos (pow_pos hs0 k)]
    have hpow : s ^ k ≤ s ^ N := pow_le_pow_right₀ hs hk
    have hbound : s ^ k * ‖coordinatePartial v ψ (s • y)‖ ≤ K := calc
      s ^ k * ‖coordinatePartial v ψ (s • y)‖ ≤
          s ^ N * ‖coordinatePartial v ψ (s • y)‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ s ^ N * B := mul_le_mul_of_nonneg_left (hψ.2.2 k hk v _) (by positivity)
      _ ≤ K := by simpa only [mul_comm] using hBK
    calc
      K⁻¹ * (s ^ k * ‖coordinatePartial v ψ (s • y)‖) ≤ K⁻¹ * K :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 1 := inv_mul_cancel₀ hK.ne'

/-- Scaling a normalized test changes its physical convolution scale to st. -/
lemma dilate_normalized_test {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (ψ : Euclidean d → 𝕜) {s K t : ℝ} (hs : 0 < s) (hK : 0 < K) :
    dilate t ψ = fun y => (K * s ^ d) •
      dilate (s * t) (fun w => K⁻¹ • ψ (s • w)) y := by
  funext y
  simp only [dilate, mul_inv_rev, mul_pow, smul_smul]
  congr 1
  · field_simp
  · congr 1
    rw [mul_left_comm, mul_inv_cancel₀ hs.ne', mul_one]

lemma convolve_real_smul_left {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u f : Euclidean d → 𝕜) (c : ℝ) (z : Euclidean d) :
    convolve (fun y => c • u y) f z = c • convolve u f z := by
  unfold convolve
  simp only [convolution_def, ContinuousLinearMap.mul_apply', smul_mul_assoc,
    integral_smul]

/-- All fixed bounded families follow from the unit test estimate by a
single normalization, so the constant is independent of the family index. -/
theorem uniform_from_compact : UniformFromCompact := by
  intro h 𝕜 _ d hd N hN η R hη a B ha hB
  obtain ⟨C₀, hC₀, hb⟩ := h hd N hN η R hη
  let s : ℝ := max a 1
  let K : ℝ := (B + 1) * s ^ N
  have hs : 1 ≤ s := le_max_right _ _
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hK : 0 < K := by dsimp [K]; positivity
  have hBK : B * s ^ N ≤ K := by dsimp [K]; nlinarith [pow_pos hs0 N]
  refine ⟨(K * s ^ d) * C₀, by positivity, ?_⟩
  intro f hf x hP ψ hψ t ht z
  let θ : Tests 𝕜 d N :=
    ⟨fun y => K⁻¹ • ψ (s • y),
      normalize_uniform_test ψ hψ hs (le_max_left _ _) hK hBK⟩
  have hθ := hb f hf x hP θ (s * t) (mul_pos hs0 ht) z
  rw [dilate_normalized_test ψ hs0 hK, convolve_real_smul_left]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hK (pow_pos hs0 d))]
  have hscale : 1 + ‖x - z‖ / (s * t) ≤ 1 + ‖x - z‖ / t := by
    gcongr
    nlinarith
  calc
    (K * s ^ d) * ‖convolve (dilate (s * t) θ.val) f z‖ ≤
        (K * s ^ d) *
          (C₀ * (peetre η f x).toReal *
            (1 + ‖x - z‖ / (s * t)) ^ peetreExponent d) :=
      mul_le_mul_of_nonneg_left hθ (by positivity)
    _ ≤ (K * s ^ d) *
          (C₀ * (peetre η f x).toReal *
            (1 + ‖x - z‖ / t) ^ peetreExponent d) := by gcongr
    _ = ((K * s ^ d) * C₀) * (peetre η f x).toReal *
          (1 + ‖x - z‖ / t) ^ peetreExponent d := by ring


/-- Insert the pointwise Peetre estimate under any integrable weighted kernel.
The majorant also justifies the convolution estimate for representatives. -/
lemma convolve_lowpass_le_weighted_integral {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (f u : Euclidean d → 𝕜) (x z : Euclidean d)
    (hP : peetre η f x < ⊤) (j : ℤ)
    (hu : Integrable (weightedIntegrand u j x z)) :
    ‖convolve u (convolve (dyadicLowpass η j) f) z‖ ≤
      (peetre η f x).toReal * ∫ w, weightedIntegrand u j x z w := by
  have hbound (w : Euclidean d) :
      ‖u w * convolve (dyadicLowpass η j) f (z - w)‖ ≤
        (peetre η f x).toReal * weightedIntegrand u j x z w := by
    rw [norm_mul]
    have h := lowpass_le_peetre η f x hP j (z - w)
    change ‖u w‖ * ‖convolve (dyadicLowpass η j) f (z - w)‖ ≤ _
    calc
      _ ≤ ‖u w‖ * ((peetre η f x).toReal *
          (1 + (2 : ℝ) ^ j * ‖x - (z - w)‖) ^ peetreExponent d) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by unfold weightedIntegrand; ring
  have h := norm_integral_le_of_norm_le (hu.const_mul (peetre η f x).toReal)
    (Filter.Eventually.of_forall hbound)
  simpa only [convolve, convolution_def, ContinuousLinearMap.mul_apply',
    integral_const_mul] using h

/-- The geometric estimate is uniform in the number of reconstructed bands. -/
lemma norm_limit_le_three_mul {𝕜 : Type} [RCLike 𝕜]
    {a v : 𝕜} (b : ℕ → 𝕜) {L : ℝ} (hL : 0 ≤ L)
    (ha : ‖a‖ ≤ L) (hb : ∀ k, ‖b k‖ ≤ L * (1 / 2 : ℝ) ^ k)
    (hv : Tendsto (fun m : ℕ => a + ∑ k ∈ Finset.range m, b k) atTop (𝓝 v)) :
    ‖v‖ ≤ 3 * L := by
  apply le_of_tendsto hv.norm
  apply Filter.Eventually.of_forall
  intro m
  calc
    ‖a + ∑ k ∈ Finset.range m, b k‖ ≤ ‖a‖ + ‖∑ k ∈ Finset.range m, b k‖ := norm_add_le _ _
    _ ≤ L + ∑ k ∈ Finset.range m, ‖b k‖ := add_le_add ha (norm_sum_le _ _)
    _ ≤ L + ∑ k ∈ Finset.range m, L * (1 / 2 : ℝ) ^ k := by
      gcongr with k hk
      exact hb k
    _ = L + L * ∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
    _ ≤ L + L * 2 := by gcongr; exact sum_geometric_two_le m
    _ = 3 * L := by ring

/-- Assemble the original estimate from the two explicit analytic obligations.
The analytic inputs are established below. -/
theorem compact_from_analytic_inputs : CompactFromAnalyticInputs := by
  intro hkernel hreconstruction 𝕜 _ d hd N hN η R hη
  obtain ⟨D, hD, hk⟩ := hkernel hd N hN η R hη
  refine ⟨3 * D, by positivity, ?_⟩
  intro f hf x hP ψ t ht z
  obtain ⟨n, hn, hnt⟩ := exists_mem_Ico_zpow ht (by norm_num : (1 : ℝ) < 2)
  let j : ℤ := -n
  have hj : (2 : ℝ) ^ (-j) ≤ t := by simpa only [j, neg_neg] using hn
  have hjt : t < 2 * (2 : ℝ) ^ (-j) := by
    simpa only [j, neg_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm]
      using hnt
  obtain ⟨hlo, hhi⟩ := hk ψ t ht j hj hjt x z
  have hlow : ‖convolve (dilate t ψ.val) (convolve (dyadicLowpass η j) f) z‖ ≤
      D * (peetre η f x).toReal * (1 + ‖x - z‖ / t) ^ peetreExponent d := by
    calc
      _ ≤ (peetre η f x).toReal *
          ∫ w, weightedIntegrand (dilate t ψ.val) j x z w :=
        convolve_lowpass_le_weighted_integral η f _ x z hP j hlo.1
      _ ≤ (peetre η f x).toReal *
          (D * (1 + ‖x - z‖ / t) ^ peetreExponent d) :=
        mul_le_mul_of_nonneg_left hlo.2 ENNReal.toReal_nonneg
      _ = _ := by ring
  have hhigh (k : ℕ) :
      ‖convolve
          (convolve (dilate t ψ.val) (dyadicDifference η (j + (k : ℤ) + 1)))
          (convolve (dyadicLowpass η (j + (k : ℤ) + 2)) f) z‖ ≤
        (D * (peetre η f x).toReal * (1 + ‖x - z‖ / t) ^ peetreExponent d) *
          (1 / 2 : ℝ) ^ k := by
    calc
      _ ≤ (peetre η f x).toReal *
          ∫ w, weightedIntegrand
            (convolve (dilate t ψ.val) (dyadicDifference η (j + (k : ℤ) + 1)))
            (j + (k : ℤ) + 2) x z w :=
        convolve_lowpass_le_weighted_integral η f _ x z hP _ (hhi k).1
      _ ≤ (peetre η f x).toReal *
          (D * (1 + ‖x - z‖ / t) ^ peetreExponent d * (1 / 2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (hhi k).2 ENNReal.toReal_nonneg
      _ = _ := by ring
  have h := norm_limit_le_three_mul _ (by positivity) hlow hhigh
    (hreconstruction hd η R hη N ψ t ht f hf j z)
  convert h using 1; ring


lemma scalarFourier_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) : scalarFourier η 0 = RCLike.map 𝕜 ℂ (∫ x, η x) := by
  simp only [scalarFourier, integralFourier, inner_zero_right, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_mul]
  exact (RCLike.map 𝕜 ℂ).integral_comp_comm (η.integrable (μ := volume))

lemma toComplex_injective {𝕜 : Type} [RCLike 𝕜] :
    Function.Injective (RCLike.map 𝕜 ℂ) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h : RCLike.map 𝕜 ℂ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hn : ‖(RCLike.re (a - b) : ℂ) + (RCLike.im (a - b) : ℂ) * Complex.I‖ = 0 :=
    by simpa only [RCLike.map_apply, RCLike.I_to_complex,
      RCLike.ofReal_eq_complex_ofReal, norm_zero] using congrArg norm h
  rwa [RCLike.norm_to_complex] at hn

lemma lowpass_integral_one {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) {R : ℝ} (hη : IsLowpass η R) : ∫ x, η x = 1 := by
  apply toComplex_injective
  have hzero : (0 : Euclidean d) ∈ Metric.ball 0 (1 / R) := by
    rw [Metric.mem_ball, dist_self]
    exact one_div_pos.mpr hη.1
  rw [← scalarFourier_zero η]
  simpa [RCLike.map_apply] using hη.2.2.2.2 0 hzero

lemma integral_dilate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Euclidean d → 𝕜) {s : ℝ} (hs : 0 < s) : ∫ x, dilate s f x = ∫ x, f x := by
  simp only [dilate, integral_smul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume f hs.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero d hs.ne'), one_smul]

/-- Moving the dilation from a mass-normalized kernel to the translation
parameter gives the majorant used in L¹ approximate identity convergence. -/
lemma dilation_translation_majorant {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (f : Euclidean d → 𝕜) {s : ℝ} (hs : 0 < s) :
    (∫ y, ‖dilate s η y‖ * ∫ x, ‖f x - f (x - y)‖) =
      ∫ y, ‖η y‖ * ∫ x, ‖f x - f (x - s • y)‖ := by
  have heq (y : Euclidean d) :
      ‖dilate s η y‖ * (∫ x, ‖f x - f (x - y)‖) =
      (s ^ d)⁻¹ • (fun w => ‖η w‖ * ∫ x, ‖f x - f (x - s • w)‖) (s⁻¹ • y) := by
    simp only [dilate, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (s ^ d)⁻¹),
      smul_smul, mul_inv_cancel₀ hs.ne', one_smul, smul_eq_mul]
    ring
  simp_rw [heq]
  rw [integral_smul]
  change (s ^ d)⁻¹ • (∫ y, (fun w : Euclidean d =>
    ‖η w‖ * ∫ x, ‖f x - f (x - s • w)‖) (s⁻¹ • y)) = _
  rw [Measure.integral_comp_inv_smul_of_nonneg volume
    (fun w : Euclidean d => ‖η w‖ * ∫ x, ‖f x - f (x - s • w)‖) hs.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero d hs.ne'), one_smul]

/-- Schwartz lowpasses are approximate identities in L¹ even though their
values need not be nonnegative. Only integrability and mass one enter here. -/
lemma lowpass_l1_approximation {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (hη : ∫ x, η x = 1)
    (f : Euclidean d → 𝕜) (hf : Integrable f) :
    Tendsto (fun s : ℝ => ∫ x, ‖f x - convolve (dilate s η) f x‖)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
  have hmajor := HardyLowpass.slow_translation_integral_tendsto_zero η f η.integrable hf
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _)
    ?_ hmajor
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : 0 < s := hs
  have hmass : (∫ y, dilate s η y) = 1 := by rw [integral_dilate η hs0, hη]
  have h := HardyLowpass.integral_norm_defect_le (dilate s η) f
    (HardyLowpass.dilate_schwartz_integrable s hs0 η) hf (by rw [hmass]; exact one_ne_zero)
  simpa only [hmass, inv_one, one_mul, norm_one,
    dilation_translation_majorant η f hs0] using h

/-- A pointwise bounded convolution kernel acts boundedly on L¹. -/
lemma norm_convolve_le_integral_norm {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u f : Euclidean d → 𝕜) (hf : Integrable f) {B : ℝ}
    (hB : ∀ y, ‖u y‖ ≤ B) (z : Euclidean d) :
    ‖convolve u f z‖ ≤ B * ∫ w, ‖f w‖ := by
  rw [HardyLowpass.convolve_comm u f]
  have h : ∀ᵐ w : Euclidean d ∂volume,
      ‖f w * u (z - w)‖ ≤ B * ‖f w‖ := by
    filter_upwards [] with w
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hb := norm_integral_le_of_norm_le (hf.norm.const_mul B) h
  simpa only [convolve, convolution_def, ContinuousLinearMap.mul_apply', integral_const_mul]
    using hb

lemma convolution_exists_bounded_left {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u f : Euclidean d → 𝕜) (hu : AEStronglyMeasurable u) (hf : Integrable f)
    (hb : BddAbove (Set.range fun y => ‖u y‖)) (z : Euclidean d) :
    ConvolutionExistsAt u f z (ContinuousLinearMap.mul 𝕜 𝕜) volume := by
  have hb' : BddAbove ((fun y => ‖u y‖) '' ((fun y => z - y) ⁻¹' Set.univ)) := by
    simpa only [Set.preimage_univ, Set.image_univ] using hb
  have he : ConvolutionExistsAt f u z (ContinuousLinearMap.mul 𝕜 𝕜) volume :=
    hb'.convolutionExistsAt (ContinuousLinearMap.mul 𝕜 𝕜)
      MeasurableSet.univ (Set.subset_univ _) hf.integrableOn hu
  apply (convolutionExistsAt_flip (f := u) (g := f)
    (L := ContinuousLinearMap.mul 𝕜 𝕜)).mp
  simpa only [ContinuousLinearMap.flip_mul] using he

lemma convolve_sub_right {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u f g : Euclidean d → 𝕜) (hu : AEStronglyMeasurable u)
    (hf : Integrable f) (hg : Integrable g)
    (hb : BddAbove (Set.range fun y => ‖u y‖)) (z : Euclidean d) :
    convolve u (f - g) z = convolve u f z - convolve u g z := by
  have hef := convolution_exists_bounded_left u f hu hf hb z
  have heg := convolution_exists_bounded_left u g hu hg hb z
  change Integrable (fun w => u w * f (z - w)) at hef
  change Integrable (fun w => u w * g (z - w)) at heg
  simp only [convolve, convolution_def, ContinuousLinearMap.mul_apply', Pi.sub_apply, mul_sub]
  exact integral_sub hef heg

/-- L¹ convergence implies convergence after convolution against any bounded
measurable kernel, at every spatial point. -/
lemma bounded_convolution_lowpass_tendsto {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (hη : ∫ x, η x = 1)
    (u f : Euclidean d → 𝕜) (hu : AEStronglyMeasurable u) (hf : Integrable f)
    (hb : BddAbove (Set.range fun y => ‖u y‖)) (z : Euclidean d) :
    Tendsto (fun s : ℝ => convolve u (convolve (dilate s η) f) z)
      (𝓝[>] 0) (𝓝 (convolve u f z)) := by
  obtain ⟨B, hB⟩ := hb
  have hB' (y : Euclidean d) : ‖u y‖ ≤ B := hB (Set.mem_range_self y)
  have hmajor := (lowpass_l1_approximation η hη f hf).const_mul B
  rw [mul_zero] at hmajor
  have hnorm : Tendsto (fun s : ℝ => ‖convolve u f z -
      convolve u (convolve (dilate s η) f) z‖) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hmajor
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hηs := HardyLowpass.dilate_schwartz_integrable s hs η
    have hconv : Integrable (convolve (dilate s η) f) :=
      hηs.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) hf
    rw [← convolve_sub_right u f _ hu hf hconv ⟨B, hB⟩ z]
    exact norm_convolve_le_integral_norm u _ (hf.sub hconv) hB' z
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using hnorm


/-- Complexification retains the actual scalar values and Schwartz topology. -/
def complexifySchwartz {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) : Schwartz ℂ d :=
  SchwartzMap.postcompCLM (RCLike.map 𝕜 ℂ) η

lemma complexifySchwartz_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (x : Euclidean d) :
    complexifySchwartz η x = RCLike.map 𝕜 ℂ (η x) := rfl

lemma toComplex_mul {𝕜 : Type} [RCLike 𝕜] (a b : 𝕜) :
    RCLike.map 𝕜 ℂ (a * b) = RCLike.map 𝕜 ℂ a * RCLike.map 𝕜 ℂ b := by
  apply Complex.ext <;> simp [RCLike.map_apply, RCLike.mul_re, RCLike.mul_im]

lemma toComplex_convolve {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u v : Schwartz 𝕜 d) (x : Euclidean d) :
    RCLike.map 𝕜 ℂ (convolve u v x) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        (complexifySchwartz u) (complexifySchwartz v) x := by
  have hb : BddAbove (Set.range fun y => ‖u y‖) :=
    ⟨SchwartzMap.seminorm ℝ 0 0 u, by
      rintro _ ⟨y, rfl⟩; exact SchwartzMap.norm_le_seminorm ℝ u y⟩
  have he := convolution_exists_bounded_left u v u.continuous.aestronglyMeasurable
    v.integrable hb x
  rw [SchwartzMap.convolution_apply]
  change RCLike.map 𝕜 ℂ (∫ y, u y * v (x - y)) =
    ∫ y, RCLike.map 𝕜 ℂ (u y) * RCLike.map 𝕜 ℂ (v (x - y))
  change Integrable (fun y => u y * v (x - y)) at he
  rw [← (RCLike.map 𝕜 ℂ).integral_comp_comm he]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => toComplex_mul _ _)

lemma complexifySchwartz_injective {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    Function.Injective (complexifySchwartz (𝕜 := 𝕜) (d := d)) := by
  intro u v huv
  ext x
  apply toComplex_injective
  exact congrArg (fun g : Schwartz ℂ d => g x) huv

lemma scalarFourier_eq_complexify {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) : scalarFourier η = schwartzFourier (complexifySchwartz η) := by
  funext ξ
  exact (ExpandedFA.Fourier.schwartz_integral d (complexifySchwartz η) ξ).symm

/-- The lowpass at half the physical scale reproduces the original lowpass.
This proves the Fourier-support step for both manuscript scalar fields. -/
lemma lowpass_reproduces_finer {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) {R s r : ℝ} (hη : IsLowpass η R) (hs : 0 < s)
    (hr : 0 < r) (hrs : 2 * r ≤ s) :
    convolve (dilate s η) (dilate r η) = dilate s η := by
  let a : Schwartz 𝕜 d := HardyLowpass.dilateSchwartz s hs η
  let b : Schwartz 𝕜 d := HardyLowpass.dilateSchwartz r hr η
  have he : SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (complexifySchwartz a) (complexifySchwartz b) = complexifySchwartz a := by
    apply (FourierTransform.fourierCLE ℂ (Schwartz ℂ d)).injective
    ext ξ
    change schwartzFourier
        (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
          (complexifySchwartz a) (complexifySchwartz b)) ξ =
      schwartzFourier (complexifySchwartz a) ξ
    rw [ExpandedFA.Fourier.Inversion.fourier_convolution,
      ← scalarFourier_eq_complexify a, ← scalarFourier_eq_complexify b]
    change scalarFourier (dilate s η) ξ * scalarFourier (dilate r η) ξ =
      scalarFourier (dilate s η) ξ
    rw [HardyLowpass.scalarFourier_dilate s hs,
      HardyLowpass.scalarFourier_dilate r hr]
    by_cases hz : scalarFourier η (s • ξ) = 0
    · simp [hz]
    · have hnorm : s * ‖ξ‖ < 2 / R := by
        have hmem := hη.2.2.2.1 (subset_tsupport (scalarFourier η) hz)
        simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hs] using hmem
      have hsmall : r • ξ ∈ Metric.ball 0 (1 / R) := by
        simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr]
        have hc := mul_le_mul_of_nonneg_right hrs (norm_nonneg ξ)
        calc
          r * ‖ξ‖ ≤ (s * ‖ξ‖) / 2 := by linarith
          _ < (2 / R) / 2 := div_lt_div_of_pos_right hnorm (by norm_num)
          _ = 1 / R := by ring
      rw [hη.2.2.2.2 _ hsmall, mul_one]
  funext x
  apply toComplex_injective
  change RCLike.map 𝕜 ℂ (convolve a b x) = RCLike.map 𝕜 ℂ (a x)
  rw [toComplex_convolve]
  exact congrArg (fun g : Schwartz ℂ d => g x) he


lemma dyadic_lowpass_reproduces {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) {R : ℝ} (hη : IsLowpass η R) (j l : ℤ) (hjl : j + 1 ≤ l) :
    convolve (dyadicLowpass η j) (dyadicLowpass η l) = dyadicLowpass η j := by
  apply lowpass_reproduces_finer η hη (by positivity) (by positivity)
  calc
    2 * (2 : ℝ) ^ (-l) = (2 : ℝ) ^ (1 - l) := by
      rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    _ ≤ (2 : ℝ) ^ (-j) := zpow_le_zpow_right₀ (by norm_num) (by omega)

/-- Associativity with a bounded left factor needs no spatial decay of f. -/
lemma convolve_assoc_bounded_first {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {u v f : Euclidean d → 𝕜} (hu : Integrable u) (hv : Integrable v) (hf : Integrable f)
    (hb : BddAbove (Set.range fun y => ‖u y‖)) :
    convolve (convolve u v) f = convolve u (convolve v f) := by
  have hi : Integrable (convolve (fun y => ‖v y‖) (fun y => ‖f y‖)) :=
    hv.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hf.norm
  have hb' : BddAbove (Set.range fun y => ‖‖u y‖‖) := by simpa only [norm_norm] using hb
  ext z
  exact convolution_assoc (ContinuousLinearMap.mul 𝕜 𝕜) (ContinuousLinearMap.mul 𝕜 𝕜)
    (ContinuousLinearMap.mul 𝕜 𝕜) (ContinuousLinearMap.mul 𝕜 𝕜)
    (fun a b c => mul_assoc a b c)
    hu.aestronglyMeasurable hv.aestronglyMeasurable hf.aestronglyMeasurable
    (hu.ae_convolution_exists _ hv) (hv.norm.ae_convolution_exists _ hf.norm)
    (convolution_exists_bounded_left _ _ hu.norm.aestronglyMeasurable hi hb' z)

lemma schwartz_bounded {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (u : Schwartz 𝕜 d) :
    BddAbove (Set.range fun y => ‖u y‖) := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 u, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact SchwartzMap.norm_le_seminorm ℝ u y

lemma dyadic_lowpass_integrable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (j : ℤ) : Integrable (dyadicLowpass η j) :=
  HardyLowpass.dilate_schwartz_integrable _ (by positivity) η

lemma dyadic_lowpass_bounded {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (j : ℤ) : BddAbove (Set.range fun y => ‖dyadicLowpass η j y‖) :=
  schwartz_bounded (HardyLowpass.dilateSchwartz _ (by positivity) η)

lemma dyadic_difference_integrable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (j : ℤ) : Integrable (dyadicDifference η j) :=
  (dyadic_lowpass_integrable η j).sub (dyadic_lowpass_integrable η (j - 1))

lemma dyadic_difference_bounded {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (j : ℤ) :
    BddAbove (Set.range fun y => ‖dyadicDifference η j y‖) := by
  obtain ⟨B, hB⟩ := dyadic_lowpass_bounded η j
  obtain ⟨C, hC⟩ := dyadic_lowpass_bounded η (j - 1)
  refine ⟨B + C, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact (norm_sub_le _ _).trans (add_le_add (hB (Set.mem_range_self y)) (hC (Set.mem_range_self y)))

/-- Cancellation bands reproduce at the next finer dyadic scale. -/
lemma dyadic_difference_reproduces {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) {R : ℝ} (hη : IsLowpass η R) (j : ℤ) :
    convolve (dyadicDifference η j) (dyadicLowpass η (j + 1)) = dyadicDifference η j := by
  have he := convolve_sub_right (dyadicLowpass η (j + 1))
    (dyadicLowpass η j) (dyadicLowpass η (j - 1))
    (dyadic_lowpass_integrable η _).aestronglyMeasurable
    (dyadic_lowpass_integrable η _) (dyadic_lowpass_integrable η _)
    (dyadic_lowpass_bounded η _) 
  funext x
  rw [dyadicDifference, HardyLowpass.convolve_comm, he,
    HardyLowpass.convolve_comm (dyadicLowpass η (j + 1)) (dyadicLowpass η j),
    HardyLowpass.convolve_comm (dyadicLowpass η (j + 1)) (dyadicLowpass η (j - 1)),
    dyadic_lowpass_reproduces η hη j (j + 1) (by omega),
    dyadic_lowpass_reproduces η hη (j - 1) (j + 1) (by omega)]
  rfl


lemma convolve_sub_left {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u v f : Euclidean d → 𝕜) (hu : AEStronglyMeasurable u) (hv : AEStronglyMeasurable v)
    (hf : Integrable f) (hbu : BddAbove (Set.range fun y => ‖u y‖))
    (hbv : BddAbove (Set.range fun y => ‖v y‖)) :
    convolve (u - v) f = convolve u f - convolve v f := by
  ext z
  have heu := convolution_exists_bounded_left u f hu hf hbu z
  have hev := convolution_exists_bounded_left v f hv hf hbv z
  change Integrable (fun w => u w * f (z - w)) at heu
  change Integrable (fun w => v w * f (z - w)) at hev
  simp only [convolve, convolution_def, ContinuousLinearMap.mul_apply', Pi.sub_apply, sub_mul]
  exact integral_sub heu hev

/-- Identify each reconstructed band with an actual difference of consecutive
lowpass convolutions. The associativity uses bounded kernels, not decay of f. -/
lemma reconstruction_band_identity {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) {R : ℝ} (hη : IsLowpass η R)
    (u f : Euclidean d → 𝕜) (hu : Integrable u) (hf : Integrable f)
    (hb : BddAbove (Set.range fun y => ‖u y‖)) (l : ℤ) (z : Euclidean d) :
    convolve (convolve u (dyadicDifference η l))
        (convolve (dyadicLowpass η (l + 1)) f) z =
      convolve u (convolve (dyadicLowpass η l) f) z -
        convolve u (convolve (dyadicLowpass η (l - 1)) f) z := by
  have hηi := dyadic_lowpass_integrable η (l + 1)
  have hδi := dyadic_difference_integrable η l
  have hηf : Integrable (convolve (dyadicLowpass η (l + 1)) f) :=
    hηi.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) hf
  rw [convolve_assoc_bounded_first hu hδi hηf hb,
    ← convolve_assoc_bounded_first hδi hηi hf (dyadic_difference_bounded η l),
    dyadic_difference_reproduces η hη l]
  have he := convolve_sub_left (dyadicLowpass η l) (dyadicLowpass η (l - 1)) f
    (dyadic_lowpass_integrable η _).aestronglyMeasurable
    (dyadic_lowpass_integrable η _).aestronglyMeasurable hf
    (dyadic_lowpass_bounded η _) (dyadic_lowpass_bounded η _)
  change convolve u (convolve (dyadicLowpass η l - dyadicLowpass η (l - 1)) f) z = _
  rw [he]
  exact convolve_sub_right u _ _ hu.aestronglyMeasurable
    ((dyadic_lowpass_integrable η _).integrable_convolution _ hf)
    ((dyadic_lowpass_integrable η _).integrable_convolution _ hf) hb z

lemma reconstruction_partial_sum {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) {R : ℝ} (hη : IsLowpass η R)
    (u f : Euclidean d → 𝕜) (hu : Integrable u) (hf : Integrable f)
    (hb : BddAbove (Set.range fun y => ‖u y‖)) (j : ℤ) (z : Euclidean d) (m : ℕ) :
    convolve u (convolve (dyadicLowpass η j) f) z +
      ∑ k ∈ Finset.range m,
        convolve (convolve u (dyadicDifference η (j + (k : ℤ) + 1)))
          (convolve (dyadicLowpass η (j + (k : ℤ) + 2)) f) z =
      convolve u (convolve (dyadicLowpass η (j + (m : ℤ))) f) z := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Finset.sum_range_succ, ← add_assoc, hm]
    have hidx : j + (m : ℤ) + 2 = (j + (m : ℤ) + 1) + 1 := by omega
    rw [hidx, reconstruction_band_identity η hη u f hu hf hb]
    have hidx' : j + (m : ℤ) + 1 - 1 = j + (m : ℤ) := by omega
    simp only [hidx', Nat.cast_add, Nat.cast_one]
    abel_nf

lemma dyadic_scale_tendsto (j : ℤ) :
    Tendsto (fun m : ℕ => (2 : ℝ) ^ (-(j + (m : ℤ)))) atTop (𝓝[>] 0) := by
  have heq (m : ℕ) : (2 : ℝ) ^ (-(j + (m : ℤ))) =
      (2 : ℝ) ^ (-j) * (1 / 2 : ℝ) ^ m := by
    simp only [neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg, zpow_natCast,
      one_div, inv_pow]
  have hlim : Tendsto (fun m : ℕ => (2 : ℝ) ^ (-(j + (m : ℤ)))) atTop (𝓝 0) := by
    simp_rw [heq]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((2 : ℝ) ^ (-j))
  exact tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall
    (fun m => show 0 < (2 : ℝ) ^ (-(j + (m : ℤ))) from zpow_pos (by norm_num) _)⟩

/-- Full reconstruction for the actual compact smooth tests in the source. -/
theorem reconstruction : Reconstruction := by
  intro 𝕜 _ d _ η R hη N ψ t ht f hf j z
  have hcompact : HasCompactSupport ψ.val :=
    (isCompact_closedBall (0 : Euclidean d) 1).of_isClosed_subset
      (isClosed_tsupport _) (ψ.property.2.1.trans Metric.ball_subset_closedBall)
  let ψS : Schwartz 𝕜 d := hcompact.toSchwartzMap ψ.property.1
  have hu : Integrable (dilate t ψ.val) :=
    HardyLowpass.dilate_schwartz_integrable t ht ψS
  have hb : BddAbove (Set.range fun y => ‖dilate t ψ.val y‖) :=
    schwartz_bounded (HardyLowpass.dilateSchwartz t ht ψS)
  have hl := (bounded_convolution_lowpass_tendsto η (lowpass_integral_one η hη)
    (dilate t ψ.val) f hu.aestronglyMeasurable hf hb z).comp (dyadic_scale_tendsto j)
  apply hl.congr'
  apply Filter.Eventually.of_forall
  intro m
  exact (reconstruction_partial_sum η hη (dilate t ψ.val) f hu hf hb j z m).symm

/-- A conditional assembly retained for reuse. Its weighted cancellation
premise is established by `weighted_kernel_bounds` below. -/
theorem transfer_theorems_from_weighted_bounds : TransferTheoremsFromWeightedBounds := by
  intro hk
  have hc : CompactTransfer := compact_from_analytic_inputs hk reconstruction
  exact ⟨hc, uniform_from_compact hc, grand_from_compact hc⟩

lemma coordinateMultiply_apply {d : ℕ} (i : Fin d) (f : Schwartz ℂ d) (x : Euclidean d) :
    coordinateMultiply i f x = (x i : ℂ) * f x := by
  unfold coordinateMultiply
  rw [SchwartzMap.smulLeftCLM_apply_apply (ExpandedFA.Fourier.coordinate_growth i)]
  rfl

lemma fourier_coordinate_zero_germ {d : ℕ} (i : Fin d) (f : Schwartz ℂ d)
    (hf : (schwartzFourier f : Euclidean d → ℂ) =ᶠ[𝓝 0] 0) :
    (schwartzFourier (coordinateMultiply i f) : Euclidean d → ℂ) =ᶠ[𝓝 0] 0 := by
  have hder := hf.fderiv (𝕜 := ℝ)
  filter_upwards [hder] with x hx
  change schwartzFourier (coordinateMultiply i f) x = 0
  rw [Inversion.fourier_coordinate, smul_apply, smul_eq_mul,
    Inversion.partial_apply, hx]
  simp

lemma integral_monomial_zero_of_fourier_zero_germ {d n : ℕ}
    (f : Schwartz ℂ d)
    (hf : (schwartzFourier f : Euclidean d → ℂ) =ᶠ[𝓝 0] 0)
    (a : Fin n → Fin d) :
    (∫ x, (monomial a x : ℂ) * f x) = 0 := by
  induction n generalizing f with
  | zero =>
    have hz := hf.self_of_nhds
    rw [schwartz_integral] at hz
    simpa [integralFourier, monomial] using hz
  | succ n ih =>
    have h := ih (coordinateMultiply (a 0) f)
      (fourier_coordinate_zero_germ (a 0) f hf) (fun i => a i.succ)
    convert h using 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [coordinateMultiply_apply]
    simp only [monomial, Fin.prod_univ_succ, Complex.ofReal_mul]
    ring


lemma integral_monomial_smul_zero_of_scalarFourier_zero_germ
    {𝕜 : Type} [RCLike 𝕜] {d n : ℕ} (f : Schwartz 𝕜 d)
    (hf : scalarFourier f =ᶠ[𝓝 0] 0) (a : Fin n → Fin d) :
    (∫ x, monomial a x • f x) = 0 := by
  have hfg : scalarFourier f = (schwartzFourier (complexifySchwartz f) : Euclidean d → ℂ) := by
    funext ξ
    exact (schwartz_integral d (complexifySchwartz f) ξ).symm
  have h := integral_monomial_zero_of_fourier_zero_germ (complexifySchwartz f)
    (by rwa [← hfg]) a
  have hi : Integrable (fun x => monomial a x • f x) := by
    have h' := (SchwartzMap.smulLeftCLM 𝕜 (fun x => (monomial a x : 𝕜)) f).integrable (μ := volume)
    convert h' using 1
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (ExpandedFA.Fourier.monomial_growth a)]
    simp only [RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  apply toComplex_injective
  rw [map_zero, ← (RCLike.map 𝕜 ℂ).integral_comp_comm hi]
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  change RCLike.map 𝕜 ℂ (monomial a x • f x) =
    (monomial a x : ℂ) * RCLike.map 𝕜 ℂ (f x)
  rw [map_smul]
  rfl


lemma scalarFourier_sub {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f g : Schwartz 𝕜 d) :
    scalarFourier (f - g) = scalarFourier f - scalarFourier g := by
  simp only [scalarFourier_eq_complexify]
  have heq : complexifySchwartz (f - g) = complexifySchwartz f - complexifySchwartz g :=
    map_sub (SchwartzMap.postcompCLM (RCLike.map 𝕜 ℂ)) f g
  rw [heq, map_sub]
  rfl

lemma lowpass_difference_scalarFourier_zero_germ
    {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (η : Schwartz 𝕜 d) {R : ℝ}
    (hη : IsLowpass η R) :
    scalarFourier (η - ExpandedFA.PartIV.HardyLowpass.dilateSchwartz 2 (by norm_num) η)
      =ᶠ[𝓝 0] 0 := by
  have hr : 0 < 1 / (2 * R) := one_div_pos.mpr (mul_pos (by norm_num) hη.1)
  filter_upwards [Metric.ball_mem_nhds (0 : Euclidean d) hr] with ξ hξ
  have hξnorm : ‖ξ‖ < 1 / (2 * R) := by simpa using hξ
  have hb2 : (2 : ℝ) • ξ ∈ Metric.ball (0 : Euclidean d) (1 / R) := by
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have heq : (2 : ℝ) * (1 / (2 * R)) = 1 / R := by field_simp
    linarith
  have hb1 : ξ ∈ Metric.ball (0 : Euclidean d) (1 / R) := by
    simp only [Metric.mem_ball, dist_zero_right]
    have h2 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
    have hb2' : 2 * ‖ξ‖ < 1 / R := by simpa only [Metric.mem_ball, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hb2
    linarith
  change scalarFourier (η - ExpandedFA.PartIV.HardyLowpass.dilateSchwartz 2 (by norm_num) η) ξ = 0
  rw [scalarFourier_sub]
  change scalarFourier η ξ - scalarFourier (dilate 2 η) ξ = 0
  rw [ExpandedFA.PartIV.HardyLowpass.scalarFourier_dilate 2 (by norm_num),
    hη.2.2.2.2 ξ hb1, hη.2.2.2.2 _ hb2, sub_self]

lemma lowpass_difference_moments
    {𝕜 : Type} [RCLike 𝕜] {d n : ℕ} (η : Schwartz 𝕜 d) {R : ℝ}
    (hη : IsLowpass η R) (a : Fin n → Fin d) :
    (∫ x, monomial a x • (η x - dilate 2 η x)) = 0 := by
  exact integral_monomial_smul_zero_of_scalarFourier_zero_germ
    (η - ExpandedFA.PartIV.HardyLowpass.dilateSchwartz 2 (by norm_num) η)
    (lowpass_difference_scalarFourier_zero_germ η hη) a


lemma test_mass_bound {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    (ψ : Tests 𝕜 d N) :
    (∫ w, ‖ψ.val w‖) ≤ (volume (Metric.closedBall (0 : Euclidean d) 1)).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal measure_closedBall_lt_top.ne).mp
  apply integral_le_measure
  · intro w _
    simpa only [coordinatePartial, iteratedFDeriv_zero_apply] using
      ψ.property.2.2 0 (Nat.zero_le N) Fin.elim0 w
  · intro w hw
    have hnot : w ∉ tsupport ψ.val := fun hw' => hw
      (Metric.ball_subset_closedBall (ψ.property.2.1 hw'))
    rw [image_eq_zero_of_notMem_tsupport hnot, norm_zero]

lemma test_dilation_compact {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    (ψ : Tests 𝕜 d N) {t : ℝ} (ht : 0 < t) : HasCompactSupport (dilate t ψ.val) := by
  have hc : HasCompactSupport ψ.val :=
    (isCompact_closedBall (0 : Euclidean d) 1).of_isClosed_subset
      (isClosed_tsupport _) (ψ.property.2.1.trans Metric.ball_subset_closedBall)
  change HasCompactSupport ((fun _ : Euclidean d => (t ^ d)⁻¹) •
    (fun w : Euclidean d => ψ.val (t⁻¹ • w)))
  exact (hc.comp_smul (inv_ne_zero ht.ne')).smul_left

lemma test_low_term {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    (ψ : Tests 𝕜 d N) (t : ℝ) (ht : 0 < t) (j : ℤ)
    (ht2 : t < 2 * (2 : ℝ) ^ (-j)) (x z : Euclidean d) :
    Integrable (weightedIntegrand (dilate t ψ.val) j x z) ∧
    (∫ w, weightedIntegrand (dilate t ψ.val) j x z w) ≤
      ((volume (Metric.closedBall (0 : Euclidean d) 1)).toReal *
        3 ^ peetreExponent d) * (1 + ‖x - z‖ / t) ^ peetreExponent d := by
  have hψc := ψ.property.1.continuous
  have hcont : Continuous (weightedIntegrand (dilate t ψ.val) j x z) := by
    unfold weightedIntegrand dilate
    fun_prop
  have hcompact : HasCompactSupport (weightedIntegrand (dilate t ψ.val) j x z) :=
    ((test_dilation_compact ψ ht).comp_left norm_zero).mul_right
  have hi : Integrable (weightedIntegrand (dilate t ψ.val) j x z) :=
    hcont.integrable_of_hasCompactSupport hcompact
  refine ⟨hi, ?_⟩
  have hdi : Integrable (dilate t ψ.val) :=
    (by unfold dilate; fun_prop : Continuous (dilate t ψ.val)).integrable_of_hasCompactSupport
      (test_dilation_compact ψ ht)
  have hpoint (w : Euclidean d) :
      weightedIntegrand (dilate t ψ.val) j x z w ≤
        ‖dilate t ψ.val w‖ * (3 * (1 + ‖x - z‖ / t)) ^ peetreExponent d := by
    by_cases hw : ψ.val (t⁻¹ • w) = 0
    · simp [weightedIntegrand, dilate, hw]
    have hmem := ψ.property.2.1 (subset_tsupport ψ.val hw)
    have hwt : ‖w‖ < t := by
      have : t⁻¹ * ‖w‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr ht.le)] using hmem
      nlinarith [inv_mul_cancel₀ ht.ne']
    have hqpos : 0 < (2 : ℝ) ^ j := by positivity
    have hqinv : (2 : ℝ) ^ j * (2 : ℝ) ^ (-j) = 1 := by
      rw [← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]
    have hqt : (2 : ℝ) ^ j * t < 2 := by
      calc
        _ < (2 : ℝ) ^ j * (2 * (2 : ℝ) ^ (-j)) :=
          mul_lt_mul_of_pos_left ht2 hqpos
        _ = 2 * ((2 : ℝ) ^ j * (2 : ℝ) ^ (-j)) := by ring
        _ = 2 := by rw [hqinv]; norm_num
    have hdist : ‖x - (z - w)‖ ≤ ‖x - z‖ + ‖w‖ := by
      convert norm_add_le (x - z) w using 1; abel_nf
    have hbase : 1 + (2 : ℝ) ^ j * ‖x - (z - w)‖ ≤
        3 * (1 + ‖x - z‖ / t) := by
      have hq : (2 : ℝ) ^ j ≤ 2 / t := (le_div_iff₀ ht).mpr hqt.le
      have h₁ := mul_le_mul_of_nonneg_left hdist hqpos.le
      have h₂ := mul_le_mul_of_nonneg_right hq (norm_nonneg (x - z))
      have h₃ := mul_le_mul_of_nonneg_left hwt.le hqpos.le
      have h₄ : 0 ≤ ‖x - z‖ / t := by positivity
      have hdiv : 2 / t * ‖x - z‖ = 2 * (‖x - z‖ / t) := by ring
      nlinarith
    unfold weightedIntegrand
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hbase _) (norm_nonneg _)
  calc
    _ ≤ ∫ w, ‖dilate t ψ.val w‖ *
        (3 * (1 + ‖x - z‖ / t)) ^ peetreExponent d :=
      integral_mono hi (hdi.norm.mul_const _) hpoint
    _ = (∫ w, ‖ψ.val w‖) *
        (3 * (1 + ‖x - z‖ / t)) ^ peetreExponent d := by
      rw [integral_mul_const]
      congr 1
      have heq : (fun w => ‖dilate t ψ.val w‖) = dilate t (fun w => ‖ψ.val w‖) := by
        funext w
        simp [dilate, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (t ^ d)⁻¹)]
      rw [heq, integral_dilate _ ht]
    _ ≤ (volume (Metric.closedBall (0 : Euclidean d) 1)).toReal *
        (3 * (1 + ‖x - z‖ / t)) ^ peetreExponent d := by
      exact mul_le_mul_of_nonneg_right (test_mass_bound ψ) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The compact-support part of the weighted kernel estimate, uniform over tests. -/
lemma low_weighted_kernel_bounds {𝕜 : Type} [RCLike 𝕜] (d N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ψ : Tests 𝕜 d N) (t : ℝ), 0 < t →
      ∀ j : ℤ, (2 : ℝ) ^ (-j) ≤ t → t < 2 * (2 : ℝ) ^ (-j) →
        ∀ x z : Euclidean d,
          Integrable (weightedIntegrand (dilate t ψ.val) j x z) ∧
          (∫ w, weightedIntegrand (dilate t ψ.val) j x z w) ≤
            D * (1 + ‖x - z‖ / t) ^ peetreExponent d := by
  refine ⟨(volume (Metric.closedBall (0 : Euclidean d) 1)).toReal *
    3 ^ peetreExponent d, by positivity, ?_⟩
  intro ψ t ht j _ ht2 x z
  exact test_low_term ψ t ht j ht2 x z



/-- The integrable radial majorant used after cancellation. -/
lemma integrable_decay_majorant (d : ℕ) :
    Integrable (fun w : Euclidean d => (1 + ‖w‖) ^ (-(d : ℝ) - 1)) := by
  have hdim : (Module.finrank ℝ (Euclidean d) : ℝ) < (d : ℝ) + 1 := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    exact lt_add_one _
  convert (integrable_one_add_norm (μ := volume) hdim) using 1
  ext w
  congr 1
  ring

/-- Arbitrary polynomial decay, at exponent A+d+1, controls the weighted L1 norm. -/
lemma decay_weighted_integral_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (A : ℕ) (u : Euclidean d → 𝕜) (hu : Continuous u) (B : ℝ) (_hB : 0 ≤ B)
    (hdecay : ∀ w, ‖u w‖ * (1 + ‖w‖) ^ (A + d + 1) ≤ B) :
    Integrable (fun w => ‖u w‖ * (1 + ‖w‖) ^ A) ∧
      (∫ w, ‖u w‖ * (1 + ‖w‖) ^ A) ≤
        B * ∫ w : Euclidean d, (1 + ‖w‖) ^ (-(d : ℝ) - 1) := by
  have hpoint (w : Euclidean d) :
      ‖u w‖ * (1 + ‖w‖) ^ A ≤ B * (1 + ‖w‖) ^ (-(d : ℝ) - 1) := by
    have hb : 0 < 1 + ‖w‖ := by positivity
    have hpow : 0 < (1 + ‖w‖) ^ (d + 1) := by positivity
    have hscaled : (‖u w‖ * (1 + ‖w‖) ^ A) * (1 + ‖w‖) ^ (d + 1) ≤ B := by
      calc
        _ = ‖u w‖ * (1 + ‖w‖) ^ (A + d + 1) := by
          rw [Nat.add_assoc, pow_add]
          ring
        _ ≤ B := hdecay w
    have hrpow : (1 + ‖w‖) ^ (-(d : ℝ) - 1) = ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
      rw [show -(d : ℝ) - 1 = -((d + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_neg hb.le, Real.rpow_natCast]
    rw [hrpow, ← div_eq_mul_inv]
    exact (le_div_iff₀ hpow).mpr hscaled
  have hg : Integrable (fun w : Euclidean d => B * (1 + ‖w‖) ^ (-(d : ℝ) - 1)) :=
    (integrable_decay_majorant d).const_mul B
  have hm : AEStronglyMeasurable (fun w => ‖u w‖ * (1 + ‖w‖) ^ A) volume :=
    (by fun_prop : Continuous (fun w => ‖u w‖ * (1 + ‖w‖) ^ A)).aestronglyMeasurable
  have hi : Integrable (fun w => ‖u w‖ * (1 + ‖w‖) ^ A) := by
    apply hg.mono' hm
    filter_upwards [] with w
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpoint w
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ w : Euclidean d, B * (1 + ‖w‖) ^ (-(d : ℝ) - 1) :=
      integral_mono hi hg hpoint
    _ = _ := integral_const_mul _ _



lemma dilate_comp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s t : ℝ) (u : Euclidean d → 𝕜) :
    dilate s (dilate t u) = dilate (s * t) u := by
  funext x
  simp only [dilate, smul_smul, mul_pow, mul_inv_rev]
  rw [mul_comm (s ^ d)⁻¹ (t ^ d)⁻¹]

lemma dyadic_difference_dilate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (l : ℤ) :
    dyadicDifference η l = dilate ((2 : ℝ) ^ (-l)) ((η : Euclidean d → 𝕜) - dilate 2 η) := by
  have hs : (2 : ℝ) ^ (-l) * 2 = (2 : ℝ) ^ (-(l - 1)) := by
    rw [show -(l - 1) = -l + 1 by omega,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ext x
  change dilate ((2 : ℝ) ^ (-l)) η x - dilate ((2 : ℝ) ^ (-(l - 1))) η x = _
  have heq : dilate ((2 : ℝ) ^ (-l)) (dilate 2 η) =
      dilate ((2 : ℝ) ^ (-(l - 1))) η := by rw [dilate_comp, hs]
  rw [← heq]
  simp only [dilate, Pi.sub_apply, smul_sub]

lemma shifted_weight_le {d : ℕ} {t L : ℝ} (ht : 0 < t) (hLt : 1 ≤ L * t)
    (x z w : Euclidean d) :
    (1 + L * ‖x - (z - w)‖) ^ peetreExponent d ≤
      (L * t) ^ peetreExponent d * (1 + ‖x - z‖ / t) ^ peetreExponent d *
        (1 + ‖w‖ / t) ^ peetreExponent d := by
  have hL : 0 ≤ L := by nlinarith
  have hn : ‖x - (z - w)‖ ≤ ‖x - z‖ + ‖w‖ := by
    rw [show x - (z - w) = (x - z) + w by abel]
    exact norm_add_le _ _
  have hbase : 1 + L * ‖x - (z - w)‖ ≤
      (L * t) * (1 + ‖x - z‖ / t) * (1 + ‖w‖ / t) := by
    have heq : (L * t) * (1 + ‖x - z‖ / t) * (1 + ‖w‖ / t) =
        L * t + L * (‖x - z‖ + ‖w‖) + L / t * ‖x - z‖ * ‖w‖ := by
      field_simp
      ring
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hn hL,
      mul_nonneg (div_nonneg hL ht.le) (mul_nonneg (norm_nonneg (x - z)) (norm_nonneg w))]
  calc
    _ ≤ ((L * t) * (1 + ‖x - z‖ / t) * (1 + ‖w‖ / t)) ^ peetreExponent d := by
      gcongr
    _ = _ := by rw [mul_pow, mul_pow]

lemma weighted_dilate_integral {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Euclidean d → 𝕜) (hu : Continuous u)
    (hi : Integrable (fun w => ‖u w‖ * (1 + ‖w‖) ^ peetreExponent d))
    {t : ℝ} (ht : 0 < t) (j : ℤ) (hjt : 1 ≤ (2 : ℝ) ^ j * t)
    (x z : Euclidean d) :
    Integrable (weightedIntegrand (dilate t u) j x z) ∧
      (∫ w, weightedIntegrand (dilate t u) j x z w) ≤
        (((2 : ℝ) ^ j * t) ^ peetreExponent d *
          (1 + ‖x - z‖ / t) ^ peetreExponent d) *
          ∫ w, ‖u w‖ * (1 + ‖w‖) ^ peetreExponent d := by
  let H : ℝ := ((2 : ℝ) ^ j * t) ^ peetreExponent d *
    (1 + ‖x - z‖ / t) ^ peetreExponent d
  let v : Euclidean d → ℝ := fun w => ‖u w‖ * (1 + ‖w‖) ^ peetreExponent d
  let V : Euclidean d → ℝ := fun w => (t ^ d)⁻¹ * v (t⁻¹ • w)
  have hVi : Integrable V := by
    exact ((integrable_comp_smul_iff volume v (inv_ne_zero ht.ne')).mpr hi).const_mul _
  have hV (w : Euclidean d) :
      V w = ‖dilate t u w‖ * (1 + ‖w‖ / t) ^ peetreExponent d := by
    simp only [V, v, dilate, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (t ^ d)⁻¹),
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le), div_eq_mul_inv]
    ring
  have hb (w : Euclidean d) : weightedIntegrand (dilate t u) j x z w ≤ H * V w := by
    rw [hV]
    change ‖dilate t u w‖ * _ ≤ H * (‖dilate t u w‖ * _)
    calc
      _ ≤ ‖dilate t u w‖ *
          (((2 : ℝ) ^ j * t) ^ peetreExponent d *
            (1 + ‖x - z‖ / t) ^ peetreExponent d *
            (1 + ‖w‖ / t) ^ peetreExponent d) :=
        mul_le_mul_of_nonneg_left (shifted_weight_le ht hjt x z w) (norm_nonneg _)
      _ = _ := by dsimp [H]; ring
  have hmeas : Continuous (weightedIntegrand (dilate t u) j x z) := by
    unfold weightedIntegrand dilate
    fun_prop
  have hweight : Integrable (weightedIntegrand (dilate t u) j x z) :=
    (hVi.const_mul H).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (by unfold weightedIntegrand; positivity)]
        exact hb w)
  refine ⟨hweight, ?_⟩
  calc
    _ ≤ ∫ w, H * V w := integral_mono hweight (hVi.const_mul H) hb
    _ = H * ∫ w, v w := by
      rw [integral_const_mul]
      congr 1
      unfold V
      rw [integral_const_mul]
      rw [Measure.integral_comp_inv_smul_of_nonneg volume v ht.le]
      simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
      field_simp

lemma convolve_dyadic_rescale {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (δ : Schwartz 𝕜 d)
    (hδ : (δ : Euclidean d → 𝕜) = (η : Euclidean d → 𝕜) - dilate 2 η)
    (ψ : Euclidean d → 𝕜) {t : ℝ} (ht : 0 < t) (l : ℤ) :
    convolve (dilate t ψ) (dyadicDifference η l) =
      dilate t (convolve ψ (dilate ((2 : ℝ) ^ (-l) / t) δ)) := by
  have heq : t * ((2 : ℝ) ^ (-l) / t) = (2 : ℝ) ^ (-l) := by field_simp
  rw [dyadic_difference_dilate, ← hδ]
  have hfun : dilate ((2 : ℝ) ^ (-l)) δ =
      dilate t (dilate ((2 : ℝ) ^ (-l) / t) δ) := by rw [dilate_comp, heq]
  rw [hfun]
  ext w
  exact HardyLowpass.convolve_dilate t ht ψ _ w

/-- A unit-scale cancellation estimate supplies all finer shifted weights.
The one constant remains independent of the test and physical scale. -/
lemma high_weighted_kernel_bounds_of_unit_estimate
    {𝕜 : Type} [RCLike 𝕜] {d N : ℕ} (hN : peetreExponent d < N)
    (η δ : Schwartz 𝕜 d)
    (hδ : (δ : Euclidean d → 𝕜) = (η : Euclidean d → 𝕜) - dilate 2 η)
    {C : ℝ} (hC : 0 ≤ C)
    (hunit : ∀ (ψ : Tests 𝕜 d N) (ε : ℝ), 0 < ε → ε ≤ 1 →
      Integrable (fun w => ‖convolve ψ.val (dilate ε δ) w‖ *
        (1 + ‖w‖) ^ peetreExponent d) ∧
      (∫ w, ‖convolve ψ.val (dilate ε δ) w‖ * (1 + ‖w‖) ^ peetreExponent d) ≤
        C * ε ^ N) :
    ∀ (ψ : Tests 𝕜 d N) (t : ℝ), 0 < t →
      ∀ j : ℤ, (2 : ℝ) ^ (-j) ≤ t → ∀ x z : Euclidean d, ∀ k : ℕ,
        Integrable (weightedIntegrand
          (convolve (dilate t ψ.val) (dyadicDifference η (j + (k : ℤ) + 1)))
          (j + (k : ℤ) + 2) x z) ∧
        (∫ w, weightedIntegrand
          (convolve (dilate t ψ.val) (dyadicDifference η (j + (k : ℤ) + 1)))
          (j + (k : ℤ) + 2) x z w) ≤
          (C * 2 ^ peetreExponent d) *
            (1 + ‖x - z‖ / t) ^ peetreExponent d * (1 / 2 : ℝ) ^ k := by
  intro ψ t ht j hj x z k
  let l : ℤ := j + (k : ℤ) + 1
  let ε : ℝ := (2 : ℝ) ^ (-l) / t
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hscale : (2 : ℝ) ^ (-l) = (2 : ℝ) ^ (-j) * (1 / 2 : ℝ) ^ (k + 1) := by
    simp only [l, neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg,
      zpow_natCast, zpow_one, one_div, pow_succ, inv_pow]
    ring
  have hεk : ε ≤ (1 / 2 : ℝ) ^ k := by
    apply (div_le_iff₀ ht).mpr
    change (2 : ℝ) ^ (-l) ≤ _
    rw [hscale, pow_succ]
    have hm := mul_le_mul_of_nonneg_right hj (by positivity : 0 ≤ (1 / 2 : ℝ) ^ k)
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]
  have hε1 : ε ≤ 1 := hεk.trans (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨hui, hu⟩ := hunit ψ ε hε hε1
  have hqε : ((2 : ℝ) ^ (l + 1) * t) * ε = 2 := by
    dsimp [ε]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    have hz : (2 : ℝ) ^ l * (2 : ℝ) ^ (-l) = 1 := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
    field_simp
    nlinarith
  have hq : 1 ≤ (2 : ℝ) ^ (l + 1) * t := by
    nlinarith [mul_le_mul_of_nonneg_left hε1
      (by positivity : 0 ≤ (2 : ℝ) ^ (l + 1) * t)]
  have hψb : BddAbove (Set.range fun w => ‖ψ.val w‖) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨w, rfl⟩
    simpa only [coordinatePartial, iteratedFDeriv_zero_apply] using
      ψ.property.2.2 0 (Nat.zero_le N) Fin.elim0 w
  have huc : Continuous (convolve ψ.val (dilate ε δ)) :=
    hψb.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul 𝕜 𝕜)
      ψ.property.1.continuous (HardyLowpass.dilate_schwartz_integrable ε hε δ)
  obtain ⟨hwi, hw⟩ := weighted_dilate_integral _ huc hui ht (l + 1) hq x z
  have hrescale := convolve_dyadic_rescale η δ hδ ψ.val ht l
  have hidx : j + (k : ℤ) + 2 = l + 1 := by dsimp [l]; omega
  rw [hidx, hrescale]
  refine ⟨hwi, ?_⟩
  have hsplit : N = peetreExponent d + (N - peetreExponent d) := by omega
  have hpower : ε ^ (N - peetreExponent d) ≤ ε := by
    simpa using pow_le_pow_of_le_one hε.le hε1 (show 1 ≤ N - peetreExponent d by omega)
  have halgebra : ((2 : ℝ) ^ (l + 1) * t) ^ peetreExponent d * ε ^ N =
      2 ^ peetreExponent d * ε ^ (N - peetreExponent d) := by
    conv_lhs => rw [hsplit, pow_add]
    rw [← mul_assoc, ← mul_pow, hqε]
  calc
    _ ≤ (((2 : ℝ) ^ (l + 1) * t) ^ peetreExponent d *
        (1 + ‖x - z‖ / t) ^ peetreExponent d) * (C * ε ^ N) :=
      hw.trans (mul_le_mul_of_nonneg_left hu (by positivity))
    _ = (C * 2 ^ peetreExponent d) * (1 + ‖x - z‖ / t) ^ peetreExponent d *
        ε ^ (N - peetreExponent d) := by
      calc
        _ = (C * (1 + ‖x - z‖ / t) ^ peetreExponent d) *
            (((2 : ℝ) ^ (l + 1) * t) ^ peetreExponent d * ε ^ N) := by ring
        _ = _ := by rw [halgebra]; ring
    _ ≤ (C * 2 ^ peetreExponent d) * (1 + ‖x - z‖ / t) ^ peetreExponent d * ε :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hεk (by positivity)


lemma basis_sum {d : ℕ} (y : Euclidean d) :
    ∑ i, (y i) • basisVector i = y := by
  simpa [basisVector, EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr y

lemma multilinear_diagonal_expansion {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclidean d) 𝕜)
    (y : Euclidean d) :
    T (fun _ => y) = ∑ a : Fin k → Fin d,
      (monomial a y) • T (fun i => basisVector (a i)) := by
  have heq : (fun _ : Fin k => y) = (fun _ : Fin k => ∑ i, (y i) • basisVector i) := by
    funext i; exact (basis_sum y).symm
  rw [heq, T.map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact T.map_smul_univ (fun i => y (a i)) (fun i => basisVector (a i))

lemma directional_bound {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclidean d) 𝕜)
    {B : ℝ} (_hB : 0 ≤ B)
    (hT : ∀ a : Fin k → Fin d, ‖T (fun i => basisVector (a i))‖ ≤ B)
    (y : Euclidean d) :
    ‖T (fun _ => y)‖ ≤ (d : ℝ)^k * B * ‖y‖^k := by
  rw [multilinear_diagonal_expansion]
  calc
    _ ≤ ∑ a : Fin k → Fin d, ‖(monomial a y) • T (fun i => basisVector (a i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a : Fin k → Fin d, ‖y‖^k * B := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_smul, Real.norm_eq_abs]
      apply mul_le_mul _ (hT a) (norm_nonneg _) (by positivity)
      unfold monomial
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ i : Fin k, ‖y‖ := by
          apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          intro i hi
          exact PiLp.norm_apply_le y (a i)
        _ = ‖y‖^k := by simp
    _ = _ := by simp; ring

lemma weighted_directional_bound {𝕜 : Type} [RCLike 𝕜] {d N k : ℕ}
    (ψ : Euclidean d → 𝕜) (hψ : IsTest N ψ) (hk : k ≤ N) (M : ℕ)
    (x y : Euclidean d) :
    (1 + ‖x‖)^M * ‖iteratedFDeriv ℝ k ψ x (fun _ => y)‖ ≤
      2^M * (d : ℝ)^k * ‖y‖^k := by
  by_cases hx : x ∈ tsupport ψ
  · have hxnorm : ‖x‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hψ.2.1 hx
    calc
      _ ≤ 2^M * ((d : ℝ)^k * 1 * ‖y‖^k) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _)
          (directional_bound _ (by norm_num) (hψ.2.2 k hk · x) y)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ k ψ x = 0 := by
      by_contra h
      exact hx (support_iteratedFDeriv_subset k h)
    simp only [hz, zero_apply, norm_zero, mul_zero]
    positivity

lemma translated_weight_le {d : ℕ} (v y : Euclidean d) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 + ‖v‖ ≤ (1 + ‖v + t • y‖) * (1 + ‖y‖) := by
  have h : ‖v‖ ≤ ‖v + t • y‖ + ‖y‖ := calc
    _ ≤ ‖v + t • y‖ + ‖t • y‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (v + t • y) (t • y)
    _ ≤ ‖v + t • y‖ + ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      nlinarith [norm_nonneg y]
  nlinarith [norm_nonneg (v + t • y), norm_nonneg y,
    mul_nonneg (norm_nonneg (v + t • y)) (norm_nonneg y)]

lemma weighted_taylor_remainder {𝕜 : Type} [RCLike 𝕜] {d n : ℕ}
    (ψ : Euclidean d → 𝕜) (hψ : IsTest (n+1) ψ) (M : ℕ)
    (v y : Euclidean d) :
    (1 + ‖v‖)^M * ‖ψ (v + y) -
      ∑ k ∈ Finset.range (n+1), (k.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ k ψ v (fun _ => y)‖ ≤
      ((n.factorial : ℝ)⁻¹ * 2^M * (d : ℝ)^(n+1)) *
        ‖y‖^(n+1) * (1 + ‖y‖)^M := by
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (x := v) (y := y) (n := n) (fun t ht =>
      (hψ.1.of_le (by simp)).contDiffAt)
  rw [htaylor, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n.factorial : ℝ)⁻¹)]
  rw [mul_left_comm ((1 + ‖v‖)^M)]
  have hwp : ‖(1 + ‖v‖)^M‖ = (1 + ‖v‖)^M := Real.norm_of_nonneg (by positivity)
  rw [← hwp, ← norm_smul]
  rw [← intervalIntegral.integral_smul]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1)
    (C := 2^M * (d : ℝ)^(n+1) * ‖y‖^(n+1) * (1 + ‖y‖)^M)
    (f := fun t => (1 + ‖v‖)^M •
      ((1-t)^n • iteratedFDeriv ℝ (n+1) ψ (v + t • y) (fun _ => y))) ?_
  · simp only [sub_zero, abs_one, mul_one] at hi
    nlinarith [mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (n.factorial : ℝ)⁻¹)]
  intro t ht
  simp only [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at ht
  have ht0 : 0 ≤ t := le_of_lt ht.1
  have ht1 : t ≤ 1 := ht.2
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (1 + ‖v‖)^M),
    abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ 1-t) _)]
  have hp : (1-t)^n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hw := pow_le_pow_left₀ (by positivity) (translated_weight_le v y ht0 ht1) M
  rw [mul_pow] at hw
  calc
    _ ≤ (1 + ‖v‖)^M * (1 * ‖iteratedFDeriv ℝ (n+1) ψ (v+t • y) (fun _ => y)‖) := by
      gcongr
    _ ≤ ((1 + ‖v+t • y‖)^M * (1+‖y‖)^M) *
      ‖iteratedFDeriv ℝ (n+1) ψ (v+t • y) (fun _ => y)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = ((1 + ‖v+t • y‖)^M *
      ‖iteratedFDeriv ℝ (n+1) ψ (v+t • y) (fun _ => y)‖) * (1+‖y‖)^M := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (weighted_directional_bound ψ hψ le_rfl M (v+t • y) y) (by positivity)

lemma monomial_norm_le {d k : ℕ} (a : Fin k → Fin d) (y : Euclidean d) :
    |monomial a y| ≤ ‖y‖^k := by
  unfold monomial
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ i : Fin k, ‖y‖ := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro i hi
      exact PiLp.norm_apply_le y (a i)
    _ = _ := by simp

lemma integrable_monomial_smul {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (δ : Schwartz 𝕜 d) (a : Fin k → Fin d) :
    Integrable (fun y => monomial a y • δ y) := by
  apply (δ.integrable_pow_mul volume k).mono'
  · exact ((continuous_finsetProd _ (fun _ _ => by fun_prop)).smul δ.continuous).aestronglyMeasurable
  · filter_upwards [] with y
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (monomial_norm_le a y) (norm_nonneg _)

lemma multilinear_moment_zero {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (δ : Schwartz 𝕜 d)
    (hδ : ∀ a : Fin k → Fin d, (∫ y, monomial a y • δ y) = 0)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclidean d) 𝕜) :
    (∫ y, δ y * T (fun _ => y)) = 0 := by
  have heq (y : Euclidean d) : δ y * T (fun _ => y) =
      ∑ a : Fin k → Fin d, (monomial a y • δ y) * T (fun i => basisVector (a i)) := by
    rw [multilinear_diagonal_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [mul_smul_comm, smul_mul_assoc]
  simp_rw [heq]
  rw [integral_finsetSum _ (fun a ha => (integrable_monomial_smul δ a).mul_const _)]
  simp only [integral_mul_const, hδ, zero_mul, Finset.sum_const_zero]

lemma multilinear_scaled_moment_zero {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (δ : Schwartz 𝕜 d)
    (hδ : ∀ a : Fin k → Fin d, (∫ y, monomial a y • δ y) = 0)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclidean d) 𝕜) (s : ℝ) :
    (∫ y, δ y * T (fun _ => s • y)) = 0 := by
  have heq (y : Euclidean d) : T (fun _ => s • y) = s^k • T (fun _ => y) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      T.map_smul_univ (fun _ => s) (fun _ => y)
  simp_rw [heq, mul_smul_comm, integral_smul, multilinear_moment_zero δ hδ T, smul_zero]

lemma integrable_multilinear_mul {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (δ : Schwartz 𝕜 d)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclidean d) 𝕜) (s : ℝ) :
    Integrable (fun y => δ y * T (fun _ => s • y)) := by
  apply ((δ.integrable_pow_mul volume k).const_mul (‖T‖ * ‖s‖^k)).mono'
  · exact (δ.continuous.mul (T.cont.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [] with y
    rw [norm_mul]
    calc
      _ ≤ ‖δ y‖ * (‖T‖ * ∏ i : Fin k, ‖s • y‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          norm_smul, mul_pow]; ring

lemma integrable_moment_weight {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (δ : Schwartz 𝕜 d) (N M : ℕ) :
    Integrable (fun y => ‖δ y‖ * ‖y‖^N * (1+‖y‖)^M) := by
  apply (((δ.integrable_pow_mul volume N).add
    (δ.integrable_pow_mul volume (N+M))).const_mul (2^(M-1) : ℝ)).mono'
  · fun_prop
  · filter_upwards [] with y
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    have hp := add_pow_le (show (0:ℝ) ≤ 1 by norm_num) (norm_nonneg y) M
    calc
      _ ≤ ‖δ y‖ * ‖y‖^N * ((2 : ℝ)^(M-1)*(1+‖y‖^M)) := by
        simpa only [one_pow] using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ ‖δ y‖ * ‖y‖^N)
      _ = _ := by rw [pow_add]; ring

lemma convolve_dilate_right {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (ψ δ : Euclidean d → 𝕜) {ε : ℝ} (hε : 0 < ε) (v : Euclidean d) :
    convolve ψ (dilate ε δ) v = ∫ y, δ y * ψ (v - ε • y) := by
  unfold convolve
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.mul_apply', dilate]
  have hp (y : Euclidean d) : ψ (v-y) * ((ε^d)⁻¹ • δ (ε⁻¹ • y)) =
      (ε^d)⁻¹ • ((fun u => δ u * ψ (v - ε • u)) (ε⁻¹ • y)) := by
    simp only [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
    rw [mul_smul_comm, mul_comm]
  simp_rw [hp]
  rw [integral_smul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun u : Euclidean d => δ u * ψ (v - ε • u)) hε.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hε.ne'), one_smul]

lemma test_norm_le {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    (ψ : Euclidean d → 𝕜) (hψ : IsTest N ψ) (y : Euclidean d) : ‖ψ y‖ ≤ 1 := by
  simpa only [coordinatePartial, iteratedFDeriv_zero_apply] using
    hψ.2.2 0 (Nat.zero_le _) Fin.elim0 y

lemma convolve_dilate_taylor_identity {𝕜 : Type} [RCLike 𝕜] {d n : ℕ}
    (δ : Schwartz 𝕜 d)
    (hδ : ∀ k < n+1, ∀ a : Fin k → Fin d, (∫ y, monomial a y • δ y) = 0)
    (ψ : Euclidean d → 𝕜) (hψ : IsTest (n+1) ψ)
    {ε : ℝ} (hε : 0 < ε) (v : Euclidean d) :
    convolve ψ (dilate ε δ) v = ∫ y, δ y *
      (ψ (v + (-ε) • y) - ∑ k ∈ Finset.range (n+1),
        (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k ψ v (fun _ => (-ε) • y)) := by
  let P : Euclidean d → 𝕜 := fun y => ∑ k ∈ Finset.range (n+1),
    (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k ψ v (fun _ => (-ε) • y)
  have hi : Integrable (fun y => δ y * ψ (v + (-ε) • y)) := by
    apply δ.integrable.norm.mono' ((δ.continuous.mul
      (hψ.1.continuous.comp (by fun_prop))).aestronglyMeasurable)
    filter_upwards [] with y
    change ‖δ y * ψ (v + (-ε) • y)‖ ≤ ‖δ y‖
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (test_norm_le ψ hψ _) (norm_nonneg _)).trans_eq (mul_one _)
  have hp : Integrable (fun y => δ y * P y) := by
    simp only [P, Finset.mul_sum, mul_smul_comm]
    apply integrable_finsetSum
    intro k hk
    exact (integrable_multilinear_mul δ (iteratedFDeriv ℝ k ψ v) (-ε)).smul ((k.factorial : ℝ)⁻¹)
  have hz : (∫ y, δ y * P y) = 0 := by
    simp only [P, Finset.mul_sum, mul_smul_comm]
    rw [integral_finsetSum (Finset.range (n+1)) (f := fun k y =>
      (k.factorial : ℝ)⁻¹ • (δ y * iteratedFDeriv ℝ k ψ v (fun _ => (-ε) • y)))
      (fun k hk => (integrable_multilinear_mul δ (iteratedFDeriv ℝ k ψ v) (-ε)).smul ((k.factorial : ℝ)⁻¹))]
    apply Finset.sum_eq_zero
    intro k hk
    rw [integral_smul, multilinear_scaled_moment_zero δ (hδ k (Finset.mem_range.mp hk))]
    simp only [smul_zero]
  rw [convolve_dilate_right ψ δ hε]
  have heq : (∫ y, δ y * ψ (v - ε • y)) = ∫ y, δ y * ψ (v + (-ε) • y) := by
    simp only [neg_smul, sub_eq_add_neg]
  rw [heq]
  change _ = ∫ y, δ y * (ψ (v + (-ε) • y) - P y)
  simp only [mul_sub]
  rw [integral_sub hi hp, hz, sub_zero]

def cancellationConstant {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (δ : Schwartz 𝕜 d) (n M : ℕ) : ℝ :=
  ((n.factorial : ℝ)⁻¹ * 2^M * (d : ℝ)^(n+1)) *
    ∫ y, ‖δ y‖ * ‖y‖^(n+1) * (1+‖y‖)^M

lemma cancellationConstant_nonneg {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (δ : Schwartz 𝕜 d) (n M : ℕ) : 0 ≤ cancellationConstant δ n M := by
  unfold cancellationConstant
  positivity

theorem cancellation_pointwise_bound {𝕜 : Type} [RCLike 𝕜] {d n : ℕ}
    (δ : Schwartz 𝕜 d)
    (hδ : ∀ k < n+1, ∀ a : Fin k → Fin d, (∫ y, monomial a y • δ y) = 0)
    (ψ : Euclidean d → 𝕜) (hψ : IsTest (n+1) ψ)
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (v : Euclidean d) :
    ‖convolve ψ (dilate ε δ) v‖ * (1+‖v‖)^M ≤
      cancellationConstant δ n M * ε^(n+1) := by
  let R : Euclidean d → 𝕜 := fun y => ψ (v + (-ε) • y) -
    ∑ k ∈ Finset.range (n+1), (k.factorial : ℝ)⁻¹ •
      iteratedFDeriv ℝ k ψ v (fun _ => (-ε) • y)
  let C : ℝ := (n.factorial : ℝ)⁻¹ * 2^M * (d : ℝ)^(n+1)
  have hR (y : Euclidean d) :
      (1+‖v‖)^M * ‖R y‖ ≤ C * ε^(n+1) * ‖y‖^(n+1) * (1+‖y‖)^M := by
    have h := weighted_taylor_remainder ψ hψ M v ((-ε) • y)
    simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hε, mul_pow] at h
    calc
      _ ≤ C * (ε^(n+1) * ‖y‖^(n+1)) * (1+ε*‖y‖)^M := h
      _ ≤ _ := by
        have hnorm : 1+ε*‖y‖ ≤ 1+‖y‖ := by nlinarith [norm_nonneg y]
        dsimp [C]
        nlinarith [mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hnorm M)
          (show 0 ≤ C * (ε^(n+1) * ‖y‖^(n+1)) by dsimp [C]; positivity)]
  rw [convolve_dilate_taylor_identity δ hδ ψ hψ hε]
  change ‖∫ y, δ y * R y‖ * (1+‖v‖)^M ≤ _
  calc
    _ = ‖∫ y, (1+‖v‖)^M • (δ y * R y)‖ := by
      rw [integral_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring
    _ ≤ ∫ y, (C * ε^(n+1)) * (‖δ y‖ * ‖y‖^(n+1) * (1+‖y‖)^M) := by
      apply norm_integral_le_of_norm_le
        ((integrable_moment_weight δ (n+1) M).const_mul (C * ε^(n+1)))
      filter_upwards [] with y
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
      calc
        _ = ‖δ y‖ * ((1+‖v‖)^M * ‖R y‖) := by ring
        _ ≤ ‖δ y‖ * (C * ε^(n+1) * ‖y‖^(n+1) * (1+‖y‖)^M) :=
          mul_le_mul_of_nonneg_left (hR y) (norm_nonneg _)
        _ = _ := by ring
    _ = cancellationConstant δ n M * ε^(n+1) := by
      rw [integral_const_mul]
      dsimp [cancellationConstant, C]
      ring


/-- Finite cancellation and Schwartz decay give a single weighted integral
constant for the entire compact test class. -/
lemma unit_scale_cancellation {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (δ : Schwartz 𝕜 d) (N : ℕ) (hN : 0 < N)
    (hδ : ∀ k < N, ∀ a : Fin k → Fin d, (∫ y, monomial a y • δ y) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : Tests 𝕜 d N) (ε : ℝ), 0 < ε → ε ≤ 1 →
      Integrable (fun w => ‖convolve ψ.val (dilate ε δ) w‖ *
        (1 + ‖w‖) ^ peetreExponent d) ∧
      (∫ w, ‖convolve ψ.val (dilate ε δ) w‖ * (1 + ‖w‖) ^ peetreExponent d) ≤
        C * ε ^ N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  let M : ℕ := peetreExponent d + d + 1
  let C₀ : ℝ := cancellationConstant δ n M
  let J : ℝ := ∫ w : Euclidean d, (1 + ‖w‖) ^ (-(d : ℝ) - 1)
  have hC₀ : 0 ≤ C₀ := cancellationConstant_nonneg δ n M
  have hJ : 0 ≤ J := integral_nonneg fun _ => by positivity
  refine ⟨C₀ * J, mul_nonneg hC₀ hJ, ?_⟩
  intro ψ ε hε hε1
  have hψb : BddAbove (Set.range fun w => ‖ψ.val w‖) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact test_norm_le ψ.val ψ.property w
  have huc : Continuous (convolve ψ.val (dilate ε δ)) :=
    hψb.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul 𝕜 𝕜)
      ψ.property.1.continuous (HardyLowpass.dilate_schwartz_integrable ε hε δ)
  obtain ⟨hi, hb⟩ := decay_weighted_integral_bound (peetreExponent d)
    (convolve ψ.val (dilate ε δ)) huc (C₀ * ε ^ (n + 1)) (by positivity)
    (fun w => cancellation_pointwise_bound δ hδ ψ.val ψ.property M hε hε1 w)
  refine ⟨hi, hb.trans_eq ?_⟩
  dsimp [J]
  ring

/-- The complete analytic kernel estimate, with constants chosen uniformly
before the compact test and all spatial and scale parameters. -/
theorem weighted_kernel_bounds : WeightedKernelBounds := by
  intro 𝕜 _ d _ N hN η R hη
  let δ : Schwartz 𝕜 d := η - HardyLowpass.dilateSchwartz 2 (by norm_num) η
  have hδ : (δ : Euclidean d → 𝕜) = (η : Euclidean d → 𝕜) - dilate 2 η := rfl
  have hm (k : ℕ) (_hk : k < N) (a : Fin k → Fin d) :
      (∫ y, monomial a y • δ y) = 0 :=
    lowpass_difference_moments η hη a
  have hNA : peetreExponent d < N := by
    dsimp [AdmissibleOrder] at hN
    omega
  obtain ⟨C, hC, hunit⟩ := unit_scale_cancellation δ N (by omega) hm
  obtain ⟨D, hD, hlo⟩ := low_weighted_kernel_bounds (𝕜 := 𝕜) d N
  have hhi := high_weighted_kernel_bounds_of_unit_estimate hNA η δ hδ hC hunit
  refine ⟨max D (C * 2 ^ peetreExponent d), hD.trans (le_max_left _ _), ?_⟩
  intro ψ t ht j hj hjt x z
  obtain ⟨hli, hl⟩ := hlo ψ t ht j hj hjt x z
  refine ⟨⟨hli, hl.trans ?_⟩, ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · intro k
    obtain ⟨hhi', hhigh⟩ := hhi ψ t ht j hj x z k
    refine ⟨hhi', hhigh.trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)

/-- The compact-test transfer estimate of the manuscript. -/
theorem compact_transfer : CompactTransfer :=
  compact_from_analytic_inputs weighted_kernel_bounds reconstruction

/-- Uniform transfer for every family with common support and C^N bounds. -/
theorem uniform_transfer : UniformTransfer :=
  uniform_from_compact compact_transfer

/-- The literal supremum over all compact tests and all positive scales. -/
theorem grand_transfer : GrandTransfer :=
  grand_from_compact compact_transfer

end ExpandedFA.PartIV.HardyCompactTransfer
