import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyWeightedKernel
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal
namespace ExpandedFA.PartIV.HardyWeightedKernel
open ExpandedFA.Fourier HardyMaximalSpec

lemma weight_comparison {d : ℕ} (x y : Euclidean d) (h : ‖x‖ ≤ 2 * ‖y‖) :
    (1 + ‖x‖) ^ ((d : ℝ) + 1 / 2) ≤
      (2 : ℝ) ^ ((d : ℝ) + 1 / 2) * (1 + ‖y‖) ^ ((d : ℝ) + 1 / 2) := by
  rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

lemma weighted_pointwise {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Euclidean d → 𝕜) (x : Euclidean d) :
    ENNReal.ofReal ((1 + ‖x‖) ^ ((d : ℝ) + 1 / 2)) * ‖u x‖ₑ ≤ weightedNorm u := by
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  exact le_iSup (fun x => ENNReal.ofReal
    ((1 + ‖x‖) ^ ((d : ℝ) + 1 / 2) * ‖u x‖)) x

lemma weighted_integrand {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u v : Euclidean d → 𝕜) (x z : Euclidean d) :
    ENNReal.ofReal ((1 + ‖x‖) ^ ((d : ℝ) + 1 / 2)) * ‖u z * v (x - z)‖ₑ ≤
    ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) + 1 / 2)) *
      (weightedNorm u * ‖v (x - z)‖ₑ + ‖u z‖ₑ * weightedNorm v) := by
  let W : Euclidean d → ℝ≥0∞ := fun a =>
    ENNReal.ofReal ((1 + ‖a‖) ^ ((d : ℝ) + 1 / 2))
  let c : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) + 1 / 2))
  have hc (a : Euclidean d) (ha : ‖x‖ ≤ 2 * ‖a‖) : W x ≤ c * W a := by
    dsimp [W, c]
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (weight_comparison x a ha)
  change W x * _ ≤ c * _
  rw [enorm_mul, ← mul_assoc]
  by_cases h : ‖x‖ ≤ 2 * ‖z‖
  · calc
      W x * ‖u z‖ₑ * ‖v (x - z)‖ₑ ≤ c * weightedNorm u * ‖v (x - z)‖ₑ := by
        apply mul_le_mul_left
        exact (mul_le_mul_left (hc z h) _).trans
          (by simpa only [mul_assoc] using mul_le_mul_right (weighted_pointwise u z) c)
      _ ≤ c * (weightedNorm u * ‖v (x - z)‖ₑ + ‖u z‖ₑ * weightedNorm v) := by
        rw [mul_assoc]; exact mul_le_mul_right le_self_add c
  · have h' : ‖x‖ ≤ 2 * ‖x - z‖ := by
      have ht : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
        simpa only [add_sub_cancel] using norm_add_le z (x - z)
      linarith
    calc
      W x * ‖u z‖ₑ * ‖v (x - z)‖ₑ = ‖u z‖ₑ * (W x * ‖v (x - z)‖ₑ) := by ac_rfl
      _ ≤ ‖u z‖ₑ * (c * weightedNorm v) := by
        apply mul_le_mul_right
        exact (mul_le_mul_left (hc (x-z) h') _).trans
          (by simpa only [mul_assoc] using mul_le_mul_right (weighted_pointwise v (x-z)) c)
      _ ≤ c * (weightedNorm u * ‖v (x - z)‖ₑ + ‖u z‖ₑ * weightedNorm v) := by
        calc
          _ = c * (‖u z‖ₑ * weightedNorm v) := by ac_rfl
          _ ≤ _ := mul_le_mul_right le_add_self c

theorem weighted_convolution : HardyWeightedKernelSpec.WeightedConvolution := by
  intro 𝕜 _ d hd u v hu hv _ _
  apply iSup_le
  intro x
  let c := ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) + 1 / 2))
  let w := ENNReal.ofReal ((1 + ‖x‖) ^ ((d : ℝ) + 1 / 2))
  have hvs : AEStronglyMeasurable (fun z => v (x - z)) volume :=
    hv.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x)
  change ENNReal.ofReal (_ * ‖convolve u v x‖) ≤ _
  rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
  calc
    w * ‖convolve u v x‖ₑ ≤ w * ∫⁻ z, ‖u z * v (x-z)‖ₑ := by
      gcongr
      exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ z, w * ‖u z * v (x-z)‖ₑ :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ z, c * (weightedNorm u * ‖v (x-z)‖ₑ + ‖u z‖ₑ * weightedNorm v) :=
      lintegral_mono (weighted_integrand u v x)
    _ = c * (weightedNorm u * ENNReal.ofReal (∫ z, ‖v z‖) +
        ENNReal.ofReal (∫ z, ‖u z‖) * weightedNorm v) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left' (hvs.enorm.const_mul _),
        lintegral_const_mul'' _ hvs.enorm,
        lintegral_mul_const'' _ hu.aestronglyMeasurable.enorm,
        (volume.measurePreserving_sub_left x).lintegral_comp_emb (Homeomorph.subLeft x).measurableEmbedding (fun a => ‖v a‖ₑ),
        ← ofReal_integral_norm_eq_lintegral_enorm hv,
        ← ofReal_integral_norm_eq_lintegral_enorm hu]

lemma norm_le_weighted {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Euclidean d → 𝕜) (x : Euclidean d) : ‖u x‖ₑ ≤ weightedNorm u := by
  have hw : 1 ≤ ENNReal.ofReal ((1 + ‖x‖) ^ ((d : ℝ) + 1 / 2)) := by
    rw [ENNReal.one_le_ofReal]
    exact Real.one_le_rpow (by linarith [norm_nonneg x]) (by positivity)
  apply le_trans _ (weighted_pointwise u x)
  simpa only [one_mul] using mul_le_mul_left hw ‖u x‖ₑ

theorem convolution_absolute : HardyWeightedKernelSpec.ConvolutionAbsolute := by
  intro 𝕜 _ d _ u v hu hv _ hw x
  have hb : ∀ z, ‖v z‖ ≤ (weightedNorm v).toReal := fun z =>
    by
      have h := (ENNReal.toReal_le_toReal (by finiteness) hw.ne).mpr (norm_le_weighted v z)
      simpa using h
  have hm : AEStronglyMeasurable (fun z => u z * v (x-z)) volume :=
    hu.aestronglyMeasurable.mul (hv.aestronglyMeasurable.comp_measurePreserving
      (volume.measurePreserving_sub_left x))
  apply Integrable.mono' (hu.norm.mul_const (weightedNorm v).toReal) hm
  filter_upwards [] with z
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb (x-z)) (norm_nonneg (u z))

/-- A polynomial-decay function is dominated by a positive sum of dyadic balls.
Using overlapping balls avoids measurable-shell boundary bookkeeping. -/
lemma decay_le_dyadic (p r : ℝ) (hp : 0 ≤ p) (hr : 0 ≤ r) :
    ENNReal.ofReal ((1+r) ^ (-p)) ≤
      ∑' n : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (-p)) ^ n) *
        (if r < (2 : ℝ) ^ (n+1) then 1 else 0) := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (by linarith : 1 ≤ 1+r)
    (by norm_num : (1 : ℝ) < 2)
  have hnr : r < (2 : ℝ) ^ (n+1) := by linarith
  have hb : (1+r) ^ (-p) ≤ ((2 : ℝ) ^ (-p)) ^ n := by
    rw [Real.rpow_pow_comm (by norm_num)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hn (neg_nonpos.mpr hp)
  exact (ENNReal.ofReal_le_ofReal hb).trans
    (by simpa only [ite_eq_left hnr, mul_one] using
      ENNReal.le_tsum n (f := fun n : ℕ => ENNReal.ofReal (((2 : ℝ) ^ (-p)) ^ n) *
        (if r < (2 : ℝ) ^ (n+1) then 1 else 0)))

/-- Every shifted ball average is controlled by the centered maximal function.
The enlarged radius is the original radius plus the distance of the centers. -/
lemma shifted_ball_integral {d : ℕ} (H : Euclidean d → ℝ) (hH : ∀ z, 0 ≤ H z)
    (x y : Euclidean d) (R : ℝ) (hR : 0 < R) :
    (∫⁻ z in ball y R, ENNReal.ofReal (H z)) ≤
      volume (ball x (R + ‖x-y‖)) *
        ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec.MaximalValue volume H x := by
  have hsub : ball y R ⊆ ball x (R + ‖x-y‖) := by
    intro z hz
    have ht := dist_triangle z y x
    rw [dist_comm y x, dist_eq_norm x y] at ht
    apply mem_ball.mpr
    linarith [mem_ball.mp hz]
  apply (lintegral_mono_set hsub).trans
  have hb := le_iSup₂ (f := fun (r : ℝ) (_ : 0 < r) =>
    (∫⁻ z in ball x r, ‖H z‖ₑ) / volume (ball x r)) (R + ‖x-y‖)
    (by positivity : 0 < R + ‖x-y‖)
  rw [ENNReal.div_le_iff (measure_ball_pos volume x (by positivity)).ne'
    measure_ball_lt_top.ne] at hb
  have he : (fun z => ENNReal.ofReal (H z)) = (fun z => ‖H z‖ₑ) := by
    funext z
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hH z)]
  rw [he]
  exact hb.trans_eq (mul_comm _ _)

lemma dyadic_ball_integral {d : ℕ} (H : Euclidean d → ℝ) (hH : ∀ z, 0 ≤ H z)
    (x y : Euclidean d) (s : ℝ) (hs : 0 < s) (n : ℕ) :
    (∫⁻ z in ball y ((2 : ℝ) ^ (n+1) * s), ENNReal.ofReal (H z)) ≤
      ENNReal.ofReal ((1 + ‖x-y‖ / s) ^ d * s ^ d * (2 : ℝ) ^ d) *
        ENNReal.ofReal ((2 : ℝ) ^ d) ^ n *
        volume (ball (0 : Euclidean d) 1) *
        ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec.MaximalValue volume H x := by
  let R := (2 : ℝ) ^ (n+1) * s
  let A := 1 + ‖x-y‖ / s
  have hR : 0 < R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsR : s ≤ R := by
    have ht : (1 : ℝ) ≤ 2 ^ (n+1) := one_le_pow₀ (by norm_num)
    dsimp [R]
    nlinarith
  have hrad : R + ‖x-y‖ ≤ A * R := by
    have hd : 0 ≤ ‖x-y‖ / s := by positivity
    have he : ‖x-y‖ / s * s = ‖x-y‖ := div_mul_cancel₀ _ hs.ne'
    dsimp [A]
    nlinarith
  have hvol : volume (ball x (R + ‖x-y‖)) ≤ volume (ball x (A*R)) :=
    measure_mono (ball_subset_ball hrad)
  have hAR : 0 < A * R := by dsimp [A]; positivity
  have hv : volume (ball x (A*R)) =
      ENNReal.ofReal ((1 + ‖x-y‖ / s) ^ d * s ^ d * (2 : ℝ) ^ d) *
        ENNReal.ofReal ((2 : ℝ) ^ d) ^ n * volume (ball (0 : Euclidean d) 1) := by
    rw [volume.addHaar_ball_of_pos x hAR]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    have he : (A*R) ^ d =
        ((1 + ‖x-y‖ / s) ^ d * s ^ d * 2 ^ d) * (2 ^ d) ^ n := by
      dsimp [A, R]
      simp only [mul_pow, pow_succ]
      ring
    rw [he, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
  exact (shifted_ball_integral H hH x y R hR).trans
    (mul_le_mul_left (hvol.trans_eq hv) _)

lemma decay_average {d : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (H : Euclidean d → ℝ) (hH : ∀ z, 0 ≤ H z) (hm : LocallyIntegrable H volume)
    (x y : Euclidean d) (s : ℝ) (hs : 0 < s) :
    (∫⁻ z, ENNReal.ofReal ((1 + ‖y-z‖ / s) ^ (-(d : ℝ)-τ)) * ENNReal.ofReal (H z)) ≤
      ENNReal.ofReal ((1 + ‖x-y‖ / s) ^ d * s ^ d * (2 : ℝ) ^ d) *
        volume (ball (0 : Euclidean d) 1) *
        (∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-τ)) ^ n) *
        ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec.MaximalValue volume H x := by
  let b := ENNReal.ofReal ((2 : ℝ) ^ (-(d : ℝ)-τ))
  let D := ENNReal.ofReal ((2 : ℝ) ^ d)
  let B := ENNReal.ofReal ((1 + ‖x-y‖ / s) ^ d * s ^ d * (2 : ℝ) ^ d)
  let V := volume (ball (0 : Euclidean d) 1)
  let M := ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec.MaximalValue volume H x
  let F : ℕ → Euclidean d → ℝ≥0∞ := fun n =>
    (ball y ((2 : ℝ) ^ (n+1) * s)).indicator (fun z => ENNReal.ofReal (H z))
  have hmF (n : ℕ) : AEMeasurable (F n) volume :=
    hm.aestronglyMeasurable.aemeasurable.ennreal_ofReal.indicator measurableSet_ball
  have hb (z : Euclidean d) :
      ENNReal.ofReal ((1 + ‖y-z‖ / s) ^ (-(d : ℝ)-τ)) * ENNReal.ofReal (H z) ≤
        ∑' n : ℕ, b ^ n * F n z := by
    have h := decay_le_dyadic ((d : ℝ)+τ) (‖y-z‖ / s) (by positivity) (by positivity)
    have hn (n : ℕ) : (‖y-z‖ / s < (2 : ℝ) ^ (n+1)) ↔
        z ∈ ball y ((2 : ℝ) ^ (n+1) * s) := by
      rw [mem_ball, dist_eq_norm, norm_sub_rev, div_lt_iff₀ hs]
    have hi (n : ℕ) :
        (if ‖y-z‖ / s < (2 : ℝ) ^ (n+1) then (1 : ℝ≥0∞) else 0) *
          ENNReal.ofReal (H z) = F n z := by
      dsimp [F]
      by_cases hz : z ∈ ball y ((2 : ℝ) ^ (n+1) * s) <;> simp [hn, hz]
    rw [show -((d : ℝ)+τ) = -(d : ℝ)-τ by ring] at h
    simp_rw [ENNReal.ofReal_pow (by positivity : 0 ≤ (2 : ℝ) ^ (-(d : ℝ)-τ))] at h
    have h' := mul_le_mul_left h (ENNReal.ofReal (H z))
    rw [← ENNReal.tsum_mul_right] at h'
    simp_rw [mul_assoc, hi] at h'
    exact h'

  have hq : b * D = ENNReal.ofReal ((2 : ℝ) ^ (-τ)) := by
    dsimp [b, D]
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num)]
    congr 2
    ring
  calc
    _ ≤ ∫⁻ z, ∑' n : ℕ, b ^ n * F n z := lintegral_mono hb
    _ = ∑' n : ℕ, b ^ n * ∫⁻ z, F n z := by
      rw [lintegral_tsum (fun n => (hmF n).const_mul _)]
      congr 1
      funext n
      exact lintegral_const_mul'' _ (hmF n)
    _ ≤ ∑' n : ℕ, b ^ n * (B * D ^ n * V * M) := by
      apply ENNReal.tsum_le_tsum
      intro n
      apply mul_le_mul_right
      dsimp [F]
      rw [lintegral_indicator measurableSet_ball]
      exact dyadic_ball_integral H hH x y s hs n
    _ = B * V * (∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-τ)) ^ n) * M := by
      have he (n : ℕ) : b ^ n * (B * D ^ n * V * M) = B * V * (b*D) ^ n * M := by
        rw [mul_pow]
        ac_rfl
      simp_rw [he, hq]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

/-- The shifted averaging estimate, with an explicit admissible constant. -/
theorem shifted_average : HardyWeightedKernelSpec.ShiftedAverage := by
  intro d _ τ C hτ hC
  let q : ℝ := (2 : ℝ) ^ (-τ)
  let V : ℝ := volume.real (ball (0 : Euclidean d) 1)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨C * 2 ^ d * V * (1-q)⁻¹, by positivity, ?_⟩
  intro 𝕜 _ K hK H hH hm s hs x y
  let A := 1 + ‖x-y‖ / s
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let a := (s ^ d)⁻¹ * C
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hk (z : Euclidean d) :
      ‖dilate s K (y-z)‖ ≤ a * (1 + ‖y-z‖ / s) ^ (-(d : ℝ)-τ) := by
    have hn : ‖s⁻¹ • (y-z)‖ = ‖y-z‖ / s := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_comm _ _
    dsimp [dilate]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (s ^ d)⁻¹ * (C * (1 + ‖s⁻¹ • (y-z)‖) ^ (-(d : ℝ)-τ)) :=
        mul_le_mul_of_nonneg_left (hK _) (by positivity)
      _ = a * (1 + ‖y-z‖ / s) ^ (-(d : ℝ)-τ) := by rw [hn]; exact (mul_assoc _ _ _).symm
  have hpoint (z : Euclidean d) :
      ENNReal.ofReal (‖dilate s K (y-z)‖ * H z) ≤
        ENNReal.ofReal a * (ENNReal.ofReal ((1 + ‖y-z‖ / s) ^ (-(d : ℝ)-τ)) *
          ENNReal.ofReal (H z)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul ha]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hk z) (hH z))
  have hseries : (∑' n : ℕ, ENNReal.ofReal q ^ n) = ENNReal.ofReal ((1-q)⁻¹) := by
    simp_rw [← ENNReal.ofReal_pow hq0]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hq0 n)
      (summable_geometric_of_lt_one hq0 hq1), tsum_geometric_of_lt_one hq0 hq1]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal a *
        (ENNReal.ofReal ((1 + ‖y-z‖ / s) ^ (-(d : ℝ)-τ)) * ENNReal.ofReal (H z)) :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal a * ∫⁻ z,
        ENNReal.ofReal ((1 + ‖y-z‖ / s) ^ (-(d : ℝ)-τ)) * ENNReal.ofReal (H z) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal (A ^ d * s ^ d * (2 : ℝ) ^ d) *
        volume (ball (0 : Euclidean d) 1) * ENNReal.ofReal ((1-q)⁻¹) *
        ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec.MaximalValue volume H x) := by
      apply mul_le_mul_right
      have hda := decay_average τ hτ H hH hm x y s hs
      change _ ≤ ENNReal.ofReal (A ^ d * s ^ d * (2 : ℝ) ^ d) *
        volume (ball (0 : Euclidean d) 1) * (∑' n : ℕ, ENNReal.ofReal q ^ n) *
        ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec.MaximalValue volume H x at hda
      rw [hseries] at hda
      exact hda
    _ = ENNReal.ofReal ((C * 2 ^ d * V * (1-q)⁻¹) * A ^ d) *
        ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec.MaximalValue volume H x := by
      have hv : volume (ball (0 : Euclidean d) 1) = ENNReal.ofReal V :=
        (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
      rw [hv]
      have he : a * (A ^ d * s ^ d * (2 : ℝ) ^ d) * V * (1-q)⁻¹ =
          (C * 2 ^ d * V * (1-q)⁻¹) * A ^ d := by
        dsimp [a]
        field_simp
      calc
        _ = ENNReal.ofReal (a * (A ^ d * s ^ d * (2 : ℝ) ^ d) * V * (1-q)⁻¹) *
            ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec.MaximalValue volume H x := by
          simp only [ENNReal.ofReal_mul, ha, hV, pow_nonneg, hA, hs.le,
            Nat.ofNat_nonneg, mul_assoc]
        _ = _ := by rw [he]

theorem shifted_ordinary_integral : HardyWeightedKernelSpec.ShiftedOrdinaryIntegral := by
  intro d hd τ C hτ hC
  obtain ⟨C', hC', hb⟩ := shifted_average d hd τ C hτ hC
  refine ⟨C', hC', ?_⟩
  intro 𝕜 _ K hK H hH hm s hs x y
  apply le_trans _ (hb K hK H hH hm s hs x y)
  calc
    _ ≤ ‖∫ z, ‖dilate s K (y-z)‖ * H z‖ₑ := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ z, ‖‖dilate s K (y-z)‖ * H z‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hH z))]

end ExpandedFA.PartIV.HardyWeightedKernel
