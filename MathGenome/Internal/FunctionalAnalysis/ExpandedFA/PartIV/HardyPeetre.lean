import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyPeetre
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyRadialTransfer
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.MaximalStrongBoundsAndDifferentiation

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ExpandedFA.PartIV.HardyPeetre
open ExpandedFA.Fourier HardyMaximalSpec HardyLowpassSpec HardyPeetreSpec
open ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec
open ExpandedFA.SingularIntegrals

/-- Weak (1,1), including the exceptional set where the supremum is infinite. -/
lemma maximal_finite_ae {d : ℕ} (H : Euclidean d → ℝ) (hH : Integrable H) :
    ∀ᵐ x ∂volume, MaximalValue volume H x < ∞ := by
  let Q : ℝ≥0∞ := (5 : ℝ≥0∞) ^ d * ENNReal.ofReal (∫ x, ‖H x‖)
  have hQ : Q ≠ ∞ := ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top
  have hb : ∀ᶠ n : ℕ in atTop,
      volume {x | MaximalValue volume H x = ∞} ≤ Q / (n : ℝ≥0∞) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hw := centeredMaximal_weak d H hH (n : ℝ) hn'
    simp only [ENNReal.ofReal_natCast] at hw
    apply le_trans (measure_mono (fun x hx => ?_)) hw
    · simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [hx]
      finiteness
  have hz : volume {x | MaximalValue volume H x = ∞} ≤ 0 := by
    apply ge_of_tendsto _ hb
    simpa only [ENNReal.div_top] using
      (ENNReal.Tendsto.const_div (a := Q) ENNReal.tendsto_nat_nhds_top (Or.inr hQ))
  simpa only [ae_iff, not_lt_top_iff, nonpos_iff_eq_zero] using hz

lemma radial_toReal_integrable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ f : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) (hf : Integrable f)
    (hF : (∫⁻ x, radial Φ f x) < ∞) :
    Integrable (fun x => (radial Φ f x).toReal) :=
  integrable_toReal_of_lintegral_ne_top
    (HardyMaximal.radial_regularity Φ f hΦ hf).2.aemeasurable hF.ne

lemma dyadic_radial_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ f : Euclidean d → 𝕜) (j : ℤ) (z : Euclidean d) :
    ENNReal.ofReal ‖convolve (dilate ((2 : ℝ) ^ (-j)) Φ) f z‖ ≤ radial Φ f z :=
  le_iSup_of_le (⟨(2 : ℝ) ^ (-j), by positivity⟩ : Scale) le_rfl

lemma inverse_bounded {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ψ : Euclidean d → 𝕜) {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ z, ‖Ψ z‖ ≤ D * (1 + ‖z‖) ^ (-(d : ℝ) - 1 / 2)) :
    ∀ z, ‖Ψ z‖ ≤ D := by
  intro z
  apply (hb z).trans
  apply mul_le_of_le_one_right hD
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) (by have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d); linarith)

lemma lowpass_factorization {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ)
    (η : Schwartz 𝕜 d) (Ψ : Euclidean d → 𝕜) (hΨ : Integrable Ψ)
    (hb : BddAbove (Set.range fun z => ‖Ψ z‖))
    (hη : ∀ z, η z = convolve Ψ Φ z)
    (f : Euclidean d → 𝕜) (hf : Integrable f) (s : ℝ) (hs : 0 < s) :
    convolve (dilate s η) f =
      convolve (dilate s Ψ) (convolve (dilate s Φ) f) := by
  have he : dilate s η = convolve (dilate s Ψ) (dilate s Φ) := by
    ext z
    rw [HardyLowpass.convolve_dilate s hs]
    simp only [dilate, hη]
  rw [he]
  apply HardyCompactTransfer.convolve_assoc_bounded_first
    (HardyRadialTransfer.integrable_dilate Ψ hΨ hs.ne')
    (HardyRadialTransfer.integrable_dilate Φ (HardyLowpass.fixed_kernel_integrable Φ hΦ).1 hs.ne') hf
  obtain ⟨B, hB⟩ := hb
  refine ⟨‖(s ^ d)⁻¹‖ * B, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact HardyRadialTransfer.norm_dilate_le Ψ (fun z => hB (Set.mem_range_self z)) s z

lemma peetre_le_of_enorm_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (f : Euclidean d → 𝕜) (x : Euclidean d) (B : ℝ≥0∞)
    (hb : ∀ (j : ℤ) (y : Euclidean d),
      ENNReal.ofReal ‖convolve (dilate ((2 : ℝ) ^ (-j)) η) f y‖ ≤
        B * ENNReal.ofReal ((1 + (2 : ℝ) ^ j * ‖x - y‖) ^ peetreExponent d)) :
    peetre η f x ≤ B := by
  apply iSup_le
  intro j
  apply iSup_le
  intro y
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  apply (ENNReal.div_le_iff (by positivity) ENNReal.ofReal_ne_top).mpr
  exact hb j y

/-- The lowpass inverse and the shifted average give the preliminary linear bound. -/
theorem linear_bound : LinearBound := by
  intro 𝕜 _ d hd Φ hΦ η Ψ D hΨ hD hdec hη
  obtain ⟨C, hC, hshift⟩ := HardyWeightedKernel.shifted_average d hd (1 / 2) D
    (by norm_num) hD
  refine ⟨C + 1, by positivity, ?_⟩
  intro f hf hF x
  let F : Euclidean d → ℝ := fun z => (radial Φ f z).toReal
  have hFi : Integrable F := radial_toReal_integrable Φ f hΦ hf hF
  have hfinite := ae_lt_top (HardyMaximal.radial_regularity Φ f hΦ hf).2 hF.ne
  apply peetre_le_of_enorm_bound η f x
  intro j y
  let s : ℝ := (2 : ℝ) ^ (-j)
  have hs : 0 < s := by positivity
  have hid := congrFun (lowpass_factorization Φ hΦ η Ψ hΨ
    ⟨D, by rintro _ ⟨z, rfl⟩; exact inverse_bounded Ψ hD hdec z⟩ hη f hf s hs) y
  have hb : ENNReal.ofReal ‖convolve (dilate s η) f y‖ ≤
      ∫⁻ z, ENNReal.ofReal (‖dilate s Ψ (y - z)‖ * F z) := by
    rw [hid, HardyRadialTransfer.convolve_eq_integral_swap]
    rw [ofReal_norm]
    apply (enorm_integral_le_lintegral_enorm _).trans
    apply lintegral_mono_ae
    filter_upwards [hfinite] with z hz
    rw [← ofReal_norm, norm_mul, ENNReal.ofReal_mul (norm_nonneg _),
      ENNReal.ofReal_mul (norm_nonneg _)]
    apply mul_le_mul_right
    rw [show F z = (radial Φ f z).toReal from rfl, ENNReal.ofReal_toReal hz.ne]
    exact dyadic_radial_le Φ f j z
  have hav := hshift Ψ hdec F (fun _ => ENNReal.toReal_nonneg) hFi.locallyIntegrable
    s hs x y
  have hweight : (1 + ‖x - y‖ / s) ^ d ≤
      (1 + (2 : ℝ) ^ j * ‖x - y‖) ^ peetreExponent d := by
    have he : ‖x - y‖ / s = (2 : ℝ) ^ j * ‖x - y‖ := by
      simp [s, zpow_neg, div_eq_mul_inv, mul_comm]
    rw [he]
    exact pow_le_pow_right₀ (by linarith [mul_nonneg (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) j)) (norm_nonneg (x - y))]) (by simp [peetreExponent])
  exact (hb.trans hav).trans (by
    rw [ENNReal.ofReal_mul hC]
    calc
      ENNReal.ofReal C * ENNReal.ofReal ((1 + ‖x - y‖ / s) ^ d) *
          MaximalValue volume F x ≤
        ENNReal.ofReal (C + 1) *
          ENNReal.ofReal ((1 + (2 : ℝ) ^ j * ‖x - y‖) ^ peetreExponent d) *
          MaximalValue volume F x :=
            mul_le_mul_left (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith))
              (ENNReal.ofReal_le_ofReal hweight)) _
      _ = _ := by ac_rfl)

theorem finite_almost_everywhere : FiniteAlmostEverywhere := by
  intro 𝕜 _ d hd Φ hΦ η Ψ D hΨ hD hdec hη f hf hF
  obtain ⟨C, hC, hb⟩ := linear_bound hd Φ hΦ η Ψ D hΨ hD hdec hη
  filter_upwards [maximal_finite_ae _ (radial_toReal_integrable Φ f hΦ hf hF)] with x hx
  exact (hb f hf hF x).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx)

/-- The interpolation step uses two bounds on the same nonnegative number. -/
lemma interpolate_bounds {a b c r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c)
    (hr : 0 < r) (hr1 : r < 1) (hab : a ≤ b) (hac : a ≤ c) :
    a ≤ b ^ (1 - r) * c ^ r := by
  calc
    a = a ^ (1 - r) * a ^ r := by
      rw [← Real.rpow_add_of_nonneg ha (by linarith) hr.le]
      simp
    _ ≤ b ^ (1 - r) * c ^ r :=
      mul_le_mul (Real.rpow_le_rpow ha hab (by linarith))
        (Real.rpow_le_rpow ha hac hr.le) (by positivity) (by positivity)

lemma shifted_weight {d : ℕ} (x y z : Euclidean d) {s : ℝ} (hs : 0 < s) :
    1 + ‖x - z‖ / s ≤ (1 + ‖x - y‖ / s) * (1 + ‖y - z‖ / s) := by
  have h := (div_le_div_of_nonneg_right (show ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ by simpa only [dist_eq_norm] using dist_triangle x y z) hs.le)
  rw [add_div] at h
  have hp : 0 ≤ (‖x - y‖ / s) * (‖y - z‖ / s) := by positivity
  nlinarith

/-- Multiplying the inverse by a quarter power still leaves integrable decay. -/
def tiltedInverse {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ψ : Euclidean d → 𝕜) (z : Euclidean d) : 𝕜 :=
  (1 + ‖z‖) ^ (1 / 4 : ℝ) • Ψ z

lemma tiltedInverse_decay {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ψ : Euclidean d → 𝕜) {D : ℝ}
    (hdec : ∀ z, ‖Ψ z‖ ≤ D * (1 + ‖z‖) ^ (-(d : ℝ) - 1 / 2)) (z : Euclidean d) :
    ‖tiltedInverse Ψ z‖ ≤ D * (1 + ‖z‖) ^ (-(d : ℝ) - 1 / 4) := by
  rw [tiltedInverse, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (1 + ‖z‖) ^ (1 / 4 : ℝ) *
        (D * (1 + ‖z‖) ^ (-(d : ℝ) - 1 / 2)) :=
      mul_le_mul_of_nonneg_left (hdec z) (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add (by positivity)]
      congr 2
      ring

lemma tiltedInverse_dilate_norm {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ψ : Euclidean d → 𝕜) {s : ℝ} (hs : 0 < s) (v : Euclidean d) :
    ‖dilate s Ψ v‖ * (1 + ‖v‖ / s) ^ (1 / 4 : ℝ) =
      ‖dilate s (tiltedInverse Ψ) v‖ := by
  simp only [dilate, tiltedInverse, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hs.le)]
  rw [div_eq_inv_mul]
  simp only [abs_of_nonneg (by positivity : 0 ≤ (1 + s⁻¹ * ‖v‖) ^ (1 / 4 : ℝ))]
  ring

lemma dyadic_weight_eq {d : ℕ} (j : ℤ) (x z : Euclidean d) :
    1 + (2 : ℝ) ^ j * ‖x - z‖ = 1 + ‖x - z‖ / (2 : ℝ) ^ (-j) := by
  simp [zpow_neg, div_eq_mul_inv, mul_comm]

lemma dyadic_interpolated_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (η : Schwartz 𝕜 d) (f : Euclidean d → 𝕜)
    (x : Euclidean d) {B : ℝ} (hB : 0 ≤ B)
    (htransfer : ∀ (j : ℤ) (z : Euclidean d),
      ‖convolve (dilate ((2 : ℝ) ^ (-j)) Φ) f z‖ ≤
        B * (peetre η f x).toReal *
          (1 + (2 : ℝ) ^ j * ‖x - z‖) ^ peetreExponent d)
    (j : ℤ) (z : Euclidean d) (hz : radial Φ f z < ∞) :
    ‖convolve (dilate ((2 : ℝ) ^ (-j)) Φ) f z‖ ≤
      B ^ (1 - averagingExponent d) * (peetre η f x).toReal ^ (1 - averagingExponent d) *
        (1 + ‖x - z‖ / (2 : ℝ) ^ (-j)) ^ (1 / 4 : ℝ) *
          (radial Φ f z).toReal ^ averagingExponent d := by
  obtain ⟨hr, hr1, _, hparam, _⟩ := HardyMaximal.parameters d
  have hU := (ENNReal.ofReal_le_iff_le_toReal hz.ne).mp (dyadic_radial_le Φ f j z)
  have hb := interpolate_bounds (norm_nonneg _) (by positivity) ENNReal.toReal_nonneg
    hr hr1 (htransfer j z) hU
  apply hb.trans_eq
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hB ENNReal.toReal_nonneg, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), hparam, dyadic_weight_eq]

lemma radial_power_memLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ f : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) (hf : Integrable f)
    (hF : (∫⁻ x, radial Φ f x) < ∞) :
    MemLp (fun z => (radial Φ f z).toReal ^ averagingExponent d)
      (ENNReal.ofReal (1 / averagingExponent d)) volume := by
  have hr := (HardyMaximal.parameters d).1
  have h := (memLp_one_iff_integrable.mpr (radial_toReal_integrable Φ f hΦ hf hF)).norm_rpow_div
    (ENNReal.ofReal (averagingExponent d))
  simpa only [ENNReal.toReal_ofReal hr.le, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, one_div,
    ENNReal.ofReal_inv_of_pos hr] using h

/-- The analytic bootstrap, still before division by P^(1-r). -/
lemma bootstrap_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (hd : 0 < d)
    (N : ℕ) (hN : AdmissibleOrder d N)
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ)
    (η : Schwartz 𝕜 d) (R : ℝ) (Ψ : Euclidean d → 𝕜) (D : ℝ)
    (hηlow : IsLowpass η R) (hΨ : Integrable Ψ) (hD : 0 ≤ D)
    (hdec : ∀ z, ‖Ψ z‖ ≤ D * (1 + ‖z‖) ^ (-(d : ℝ) - 1 / 2))
    (hη : ∀ z, η z = convolve Ψ Φ z) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Euclidean d → 𝕜), Integrable f →
      (∫⁻ x, radial Φ f x) < ∞ → ∀ x, peetre η f x < ∞ →
      peetre η f x ≤
        ENNReal.ofReal (C * (peetre η f x).toReal ^ (1 - averagingExponent d)) *
          MaximalValue volume (fun z => (radial Φ f z).toReal ^ averagingExponent d) x := by
  obtain ⟨B, hB, htransfer⟩ := HardyRadialTransfer.dyadic_transfer hd N hN Φ hΦ η R hηlow
  obtain ⟨E, hE, hshift⟩ := HardyWeightedKernel.shifted_average d hd (1 / 4) D
    (by norm_num) hD
  let C : ℝ := E * B ^ (1 - averagingExponent d) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f hf hF x hP
  let H : Euclidean d → ℝ := fun z => (radial Φ f z).toReal ^ averagingExponent d
  let Q : ℝ := B ^ (1 - averagingExponent d) *
    (peetre η f x).toReal ^ (1 - averagingExponent d)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hfinite := ae_lt_top (HardyMaximal.radial_regularity Φ f hΦ hf).2 hF.ne
  have hH : LocallyIntegrable H volume := by
    apply (radial_power_memLp Φ f hΦ hf hF).locallyIntegrable
    have hr := (HardyMaximal.parameters d).1
    have hr1 := (HardyMaximal.parameters d).2.1
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((one_le_div hr).mpr (le_of_lt hr1))
  apply peetre_le_of_enorm_bound η f x
  intro j y
  let s : ℝ := (2 : ℝ) ^ (-j)
  have hs : 0 < s := by positivity
  let w : ℝ := 1 + ‖x - y‖ / s
  have hw : 1 ≤ w := by dsimp [w]; linarith [div_nonneg (norm_nonneg (x - y)) hs.le]
  have hid := congrFun (lowpass_factorization Φ hΦ η Ψ hΨ
    ⟨D, by rintro _ ⟨z, rfl⟩; exact inverse_bounded Ψ hD hdec z⟩ hη f hf s hs) y
  have hb : ENNReal.ofReal ‖convolve (dilate s η) f y‖ ≤
      ENNReal.ofReal (Q * w ^ (1 / 4 : ℝ)) *
        ∫⁻ z, ENNReal.ofReal (‖dilate s (tiltedInverse Ψ) (y - z)‖ * H z) := by
    rw [hid, HardyRadialTransfer.convolve_eq_integral_swap, ofReal_norm]
    apply (enorm_integral_le_lintegral_enorm _).trans
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hfinite] with z hz
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul]
    have hU := dyadic_interpolated_bound Φ η f x hB (htransfer f hf x hP) j z hz
    have hweight : (1 + ‖x - z‖ / s) ^ (1 / 4 : ℝ) ≤
        w ^ (1 / 4 : ℝ) * (1 + ‖y - z‖ / s) ^ (1 / 4 : ℝ) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (shifted_weight x y z hs) (by norm_num)
    calc
      _ ≤ ‖dilate s Ψ (y - z)‖ * (Q * (1 + ‖x - z‖ / s) ^ (1 / 4 : ℝ) * H z) :=
        mul_le_mul_of_nonneg_left hU (norm_nonneg _)
      _ ≤ ‖dilate s Ψ (y - z)‖ * (Q *
          (w ^ (1 / 4 : ℝ) * (1 + ‖y - z‖ / s) ^ (1 / 4 : ℝ)) * H z) := by
        gcongr
      _ = _ := by
        rw [← tiltedInverse_dilate_norm Ψ hs]
        ring
  have hav := hshift (tiltedInverse Ψ) (tiltedInverse_decay Ψ hdec) H
    (fun z => Real.rpow_nonneg ENNReal.toReal_nonneg _) hH s hs x y
  have hpow : w ^ (1 / 4 : ℝ) * w ^ d ≤ w ^ peetreExponent d := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity), ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hw
    simp only [peetreExponent, Nat.cast_add, Nat.cast_one]
    linarith
  apply (hb.trans (mul_le_mul_right hav _)).trans
  have he : ENNReal.ofReal (Q * w ^ (1 / 4 : ℝ)) *
      (ENNReal.ofReal (E * w ^ d) * MaximalValue volume H x) =
      ENNReal.ofReal (E * B ^ (1 - averagingExponent d) *
        (peetre η f x).toReal ^ (1 - averagingExponent d) * (w ^ (1 / 4 : ℝ) * w ^ d)) *
          MaximalValue volume H x := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    dsimp [Q]
    ring
  change ENNReal.ofReal (Q * w ^ (1 / 4 : ℝ)) *
    (ENNReal.ofReal (E * w ^ d) * MaximalValue volume H x) ≤ _
  rw [he]
  have hc : E * B ^ (1 - averagingExponent d) ≤ C := by dsimp [C]; linarith
  have hreal : E * B ^ (1 - averagingExponent d) *
      (peetre η f x).toReal ^ (1 - averagingExponent d) * (w ^ (1 / 4 : ℝ) * w ^ d) ≤
      (C * (peetre η f x).toReal ^ (1 - averagingExponent d)) * w ^ peetreExponent d := by
    gcongr
  have hwdy : w = 1 + (2 : ℝ) ^ j * ‖x - y‖ := (dyadic_weight_eq j x y).symm
  rw [hwdy] at hreal ⊢
  apply le_trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _)
  rw [ENNReal.ofReal_mul (by positivity)]
  apply le_of_eq
  dsimp [H]
  ac_rfl

/-- Ordinary division is performed only for a positive finite P; P=0 is separate. -/
lemma solve_bootstrap {P M C r : ℝ} (hP : 0 ≤ P) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hr : 0 < r) (_hr1 : r < 1) (hb : P ≤ C * P ^ (1 - r) * M) :
    P ≤ C ^ (1 / r) * M ^ (1 / r) := by
  by_cases hz : P = 0
  · rw [hz]
    positivity
  have hp : 0 < P := lt_of_le_of_ne hP (Ne.symm hz)
  have hdiv : P ^ r ≤ C * M := by
    have he : P ^ r = P / P ^ (1 - r) := by
      calc
        P ^ r = P ^ (1 - (1 - r)) := by congr 1; ring
        _ = P / P ^ (1 - r) := by rw [Real.rpow_sub hp, Real.rpow_one]
    rw [he]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hp _)).mpr
    nlinarith [hb]
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ P ^ r) hdiv
    (by positivity : 0 ≤ 1 / r)
  simpa only [one_div, Real.rpow_rpow_inv hP hr.ne', Real.mul_rpow hC hM] using hh

/-- The nonlinear estimate for the chosen low-frequency inverse. -/
theorem nonlinear_bound : NonlinearBound := by
  intro 𝕜 _ d hd N hN Φ hΦ η R Ψ D hηlow hΨ hD hdec hη
  obtain ⟨C, hC, hb⟩ := bootstrap_bound hd N hN Φ hΦ η R Ψ D hηlow hΨ hD hdec hη
  have hr := (HardyMaximal.parameters d).1
  have hr1 := (HardyMaximal.parameters d).2.1
  refine ⟨C ^ (1 / averagingExponent d), Real.rpow_pos_of_pos hC _, ?_⟩
  intro f hf hF
  filter_upwards [finite_almost_everywhere hd Φ hΦ η Ψ D hΨ hD hdec hη f hf hF] with x hx
  let M : ℝ≥0∞ := MaximalValue volume
    (fun z => (radial Φ f z).toReal ^ averagingExponent d) x
  change peetre η f x ≤ ENNReal.ofReal (C ^ (1 / averagingExponent d)) * M ^ (1 / averagingExponent d)
  by_cases hM : M = ∞
  · rw [hM, ENNReal.top_rpow_of_pos (by positivity), ENNReal.mul_top
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hC _)))]
    exact le_top
  have hboot := hb f hf hF x hx
  change peetre η f x ≤ ENNReal.ofReal (C * (peetre η f x).toReal ^
    (1 - averagingExponent d)) * M at hboot
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM) hboot
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hh
  have hs := solve_bootstrap ENNReal.toReal_nonneg ENNReal.toReal_nonneg hC.le hr hr1 hh
  have he := ENNReal.ofReal_le_ofReal hs
  rw [ENNReal.ofReal_toReal hx.ne, ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
    ENNReal.ofReal_toReal hM] at he
  exact he

/-- Strong maximal boundedness at 1/r, in the exact extended-integral form needed. -/
lemma maximal_radial_power_integral {d : ℕ} :
    ∃ K : ℝ, 0 < K ∧ ∀ {𝕜 : Type} [RCLike 𝕜]
      (Φ f : Euclidean d → 𝕜), IsFixedKernel Φ → Integrable f →
      (∫⁻ x, radial Φ f x) < ∞ →
      (∫⁻ x, (MaximalValue volume
        (fun z => (radial Φ f z).toReal ^ averagingExponent d) x) ^
          (1 / averagingExponent d)) ≤ ENNReal.ofReal K * ∫⁻ x, radial Φ f x := by
  have hr := (HardyMaximal.parameters d).1
  have hr1 := (HardyMaximal.parameters d).2.1
  have hp : 1 < 1 / averagingExponent d := (one_lt_div hr).mpr hr1
  have hp0 : 0 < 1 / averagingExponent d := by positivity
  obtain ⟨C, hstrong⟩ := centeredMaximal_strong_finite d (1 / averagingExponent d) hp
  let K : ℝ := ((C : ℝ) + 1) ^ (1 / averagingExponent d)
  refine ⟨K, Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro 𝕜 _ Φ f hΦ hf hF
  let H : Euclidean d → ℝ := fun z => (radial Φ f z).toReal ^ averagingExponent d
  have hH := radial_power_memLp Φ f hΦ hf hF
  have hb := ENNReal.rpow_le_rpow (hstrong H hH) hp0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    Interpolation.eLpNorm_ofReal_rpow hH.aestronglyMeasurable hp0] at hb
  have heq : (∫⁻ x, ‖H x‖ₑ ^ (1 / averagingExponent d)) = ∫⁻ x, radial Φ f x := by
    apply lintegral_congr_ae
    filter_upwards [ae_lt_top (HardyMaximal.radial_regularity Φ f hΦ hf).2 hF.ne] with x hx
    dsimp only [H]
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hr.le,
      ← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one,
      ENNReal.ofReal_toReal hx.ne]
  rw [heq] at hb
  have hconst : (C : ℝ≥0∞) ^ (1 / averagingExponent d) ≤ ENNReal.ofReal K := by
    dsimp [K]
    rw [← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (by linarith)) hp0.le
  exact hb.trans (mul_le_mul_left hconst _)

/-- Assemble the grand L¹ estimate from the pointwise estimate and strong maximal bound. -/
theorem grand_L1_bound : GrandL1Bound := by
  intro 𝕜 _ d hd N hN Φ hΦ
  obtain ⟨R, η, Ψ, D, hηlow, hΨ, hD, hdec, hη⟩ := HardyLowpass.lowpass_inverse hd Φ hΦ
  obtain ⟨C, hC, hb⟩ := nonlinear_bound hd N hN Φ hΦ η R Ψ D hηlow hΨ hD hdec hη
  obtain ⟨B, hB, hg⟩ := HardyCompactTransfer.grand_transfer hd N hN η R hηlow
  obtain ⟨K, hK, hk⟩ := maximal_radial_power_integral (d := d)
  refine ⟨B * C * K, by positivity, ?_⟩
  intro f hf hF
  calc
    (∫⁻ x, grand N f x) ≤ ∫⁻ x,
        ENNReal.ofReal B * (ENNReal.ofReal C *
          (MaximalValue volume (fun z => (radial Φ f z).toReal ^ averagingExponent d) x) ^
            (1 / averagingExponent d)) := by
      apply lintegral_mono_ae
      filter_upwards [hb f hf hF] with x hx
      exact (hg f hf x).trans (mul_le_mul_right hx _)
    _ = ENNReal.ofReal B * (ENNReal.ofReal C * ∫⁻ x,
          (MaximalValue volume (fun z => (radial Φ f z).toReal ^ averagingExponent d) x) ^
            (1 / averagingExponent d)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal C *
        (ENNReal.ofReal K * ∫⁻ x, radial Φ f x)) :=
      mul_le_mul_right (mul_le_mul_right (hk Φ f hΦ hf hF) _) _
    _ = ENNReal.ofReal (B * C * K) * ∫⁻ x, radial Φ f x := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hB.le]
      ac_rfl

end ExpandedFA.PartIV.HardyPeetre
