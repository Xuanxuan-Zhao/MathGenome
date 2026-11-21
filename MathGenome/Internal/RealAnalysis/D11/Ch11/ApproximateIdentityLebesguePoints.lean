import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.ApproximateIdentityLebesguePoints
import MathGenome.Internal.RealAnalysis.D11.Ch11.ConvolutionYoung
import MathGenome.Internal.RealAnalysis.D11.Ch13.LebesgueDifferentiation
import MathGenome.Internal.RealAnalysis.D11.Ch10.FiniteMeasureInclusion
import MathGenome.Internal.RealAnalysis.D11.Ch09.LinearJacobian

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace D11.Ch11.ApproximateIdentityLebesguePoints
open D11.Ch03 D11.Ch03.LebesgueMeasures
open D11.Ch13.AveragesMaximalDefinition
open D11.Ch13.LebesgueDifferentiation
open ConvolutionBound (convolution measurePreserving_const_sub)

abbrev dilate : Specs.D11.Ch11.ApproximateIdentityLebesguePoints.dilate_type :=
  Specs.D11.Ch11.ApproximateIdentityLebesguePoints.dilate_value

private lemma volume_ball_scale {n : ℕ} (x : Point n) {t : ℝ} (ht : 0 < t) (R : ℝ) :
    (volume (ball x (t*R))).toReal = t^n * (volume (ball (0 : Point n) R)).toReal := by
  rw [Measure.addHaar_ball_mul_of_pos volume x ht R, ENNReal.toReal_mul]
  simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_ofReal (pow_nonneg ht.le _)]

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := lebesgueSpace n
variable {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

lemma locallyIntegrable_of_memLp {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : Point n → 𝕜) (hm : Measurable f) (hf : MemLp f p (lebesgue n)) :
    locallyIntegrable f := by
  apply (locallyIntegrable_iff f).mpr
  refine ⟨hm, fun K hK => ?_⟩
  let : IsFiniteMeasure ((lebesgue n).restrict K) :=
    ⟨by simpa using hK.measure_lt_top (μ := lebesgue n)⟩
  exact memLp_one_iff_integrable.mp ((hf.mono_measure Measure.restrict_le_self).mono_exponent hp)

/-- Absolute existence for a bounded measurable kernel supported in a ball.
Only local integrability of the second factor is needed. -/
lemma integrable_kernel (f k : Point n → 𝕜) (hf : locallyIntegrable f)
    (hk : Measurable k) (M R : ℝ) (hb : ∀ y, ‖k y‖ ≤ M)
    (hs : Function.support k ⊆ ball 0 R) (x : Point n) :
    Integrable (fun y => k y * f (x-y)) (lebesgue n) := by
  let F := (ball x R).indicator f
  have hi : Integrable F (lebesgue n) :=
    (integrable_indicator_iff (ball_measurable x R)).mpr (integrableOn_ball f hf x R)
  have hc := (measurePreserving_const_sub x).integrable_comp_of_integrable hi
  have hmul := hc.bdd_mul hk.aestronglyMeasurable (ae_of_all _ hb)
  apply hmul.congr
  apply ae_of_all
  intro y
  dsimp only [Function.comp_def]
  by_cases hy : k y = 0
  · simp [hy]
  · have hyball : x-y ∈ ball x R := by
      have hyR := hs hy
      simpa only [mem_ball, dist_eq_norm, show x-y-x = -y by abel, norm_neg, sub_zero] using hyR
    simp only [F, indicator_of_mem hyball]

/-- Invariance of every scalar integral under reflection about x/2. -/
lemma integral_const_sub (g : Point n → 𝕜) (x : Point n) :
    (∫ y, g (x-y) ∂lebesgue n) = ∫ y, g y ∂lebesgue n := by
  let e : Point n ≃ᵐ Point n :=
    { toEquiv := ⟨fun y => x-y, fun y => x-y, fun y => sub_sub_cancel x y,
        fun y => sub_sub_cancel x y⟩
      measurable_toFun := (measurePreserving_const_sub x).measurable
      measurable_invFun := (measurePreserving_const_sub x).measurable }
  exact (measurePreserving_const_sub x).integral_comp e.measurableEmbedding g

/-- A bounded ball-supported kernel controls error by the local L1 oscillation. -/
lemma error_bound (f k : Point n → 𝕜) (hf : locallyIntegrable f)
    (hk : Measurable k) (M R : ℝ) (hM : 0 ≤ M) (hb : ∀ y, ‖k y‖ ≤ M)
    (hs : Function.support k ⊆ ball 0 R) (hunit : (∫ y, k y ∂lebesgue n) = 1)
    (x : Point n) :
    ‖convolution n k f x - f x‖ ≤ M * ∫ y in ball x R, ‖f y - f x‖ ∂lebesgue n := by
  have he := locallyIntegrable_sub_const f hf (f x)
  have hi := integrable_kernel f k hf hk M R hb hs x
  have hei := integrable_kernel (fun y => f y - f x) k he hk M R hb hs x
  have hkint : Integrable k (lebesgue n) := by
    exact Integrable.of_integral_ne_zero (hunit.trans_ne one_ne_zero)
  have heq : convolution n k f x - f x =
      ∫ y, k y * (f (x-y) - f x) ∂lebesgue n := by
    simp only [mul_sub]
    rw [integral_sub hi (hkint.mul_const (f x)), integral_mul_const, hunit, one_mul]
    rfl
  rw [heq]
  apply (norm_integral_le_integral_norm _).trans
  have hosc : IntegrableOn (fun y => ‖f y - f x‖) (ball x R) (lebesgue n) :=
    (integrableOn_ball _ he x R).norm
  have hmajor : Integrable (fun y => M * (ball x R).indicator
      (fun z => ‖f z - f x‖) (x-y)) (lebesgue n) :=
    ((measurePreserving_const_sub x).integrable_comp_of_integrable
      ((integrable_indicator_iff (ball_measurable x R)).mpr hosc)).const_mul M
  calc
    (∫ y, ‖k y * (f (x-y) - f x)‖ ∂lebesgue n) ≤
        ∫ y, M * (ball x R).indicator (fun z => ‖f z - f x‖) (x-y) ∂lebesgue n := by
      apply integral_mono hei.norm hmajor
      intro y
      dsimp only
      by_cases hy : k y = 0
      · simp only [hy, zero_mul, norm_zero]
        exact mul_nonneg hM (indicator_nonneg (fun z _ => norm_nonneg _) _)
      · have hyball : x-y ∈ ball x R := by
          have hyR := hs hy
          simpa only [mem_ball, dist_eq_norm, show x-y-x = -y by abel, norm_neg, sub_zero] using hyR
        rw [indicator_of_mem hyball, norm_mul]
        exact mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _)
    _ = M * ∫ y in ball x R, ‖f y - f x‖ ∂lebesgue n := by
      rw [integral_const_mul, integral_const_sub, integral_indicator (ball_measurable x R)]

/-- Scalar change of variables on the completed measure, including totalized integrals. -/
lemma integral_comp_smul (g : Point n → 𝕜) {a : ℝ} (ha : a ≠ 0) :
    (∫ y, g (a • y) ∂lebesgue n) = |(a^n)⁻¹| • ∫ y, g y ∂lebesgue n := by
  let T := LinearEquiv.smulOfNeZero ℝ (Point n) a ha
  have hT : (T : Point n →ₗ[ℝ] Point n) = a • LinearMap.id := rfl
  have hd : LinearMap.det (T : Point n →ₗ[ℝ] Point n) = a^n := by
    rw [hT, LinearMap.det_smul]
    simp
  have H := integral_map_equiv (μ := lebesgue n) (D11.Ch09.LinearJacobian.completedEquiv n T) g
  change (∫ y, g y ∂Measure.map T (lebesgue n)) = ∫ y, g (a • y) ∂lebesgue n at H
  rw [D11.Ch09.LinearJacobian.map_lebesgue, integral_smul_measure, hd,
    ENNReal.toReal_ofReal (abs_nonneg _)] at H
  exact H.symm

lemma dilate_measurable (φ : Point n → 𝕜) (hφ : Measurable φ) {t : ℝ} (ht : 0 < t) :
    Measurable (dilate n φ t) := by
  exact (hφ.comp (D11.Ch09.LinearJacobian.completed_measurable n
    (LinearEquiv.smulOfNeZero ℝ (Point n) t⁻¹ (inv_ne_zero ht.ne')))).const_smul _

lemma dilate_integral (φ : Point n → 𝕜) {t : ℝ} (ht : 0 < t)
    (hunit : (∫ y, φ y ∂lebesgue n) = 1) :
    (∫ y, dilate n φ t y ∂lebesgue n) = 1 := by
  change (∫ y, (t^n)⁻¹ • φ (t⁻¹ • y) ∂lebesgue n) = 1
  rw [integral_smul, integral_comp_smul φ (inv_ne_zero ht.ne'), hunit,
    inv_pow, inv_inv, abs_of_pos (pow_pos ht n), smul_smul, inv_mul_cancel₀ (pow_ne_zero n ht.ne'), one_smul]

lemma dilate_bound (φ : Point n → 𝕜) (M : ℝ) (hb : ∀ y, ‖φ y‖ ≤ M)
    {t : ℝ} (ht : 0 < t) : ∀ y, ‖dilate n φ t y‖ ≤ (t^n)⁻¹ * M := by
  intro y
  change ‖(t^n)⁻¹ • φ (t⁻¹ • y)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos ht n))]
  exact mul_le_mul_of_nonneg_left (hb _) (inv_nonneg.mpr (pow_nonneg ht.le _))

lemma dilate_support (φ : Point n → 𝕜) (R : ℝ)
    (hs : Function.support φ ⊆ ball 0 R) {t : ℝ} (ht : 0 < t) :
    Function.support (dilate n φ t) ⊆ ball 0 (t*R) := by
  intro y hy
  have hφ : φ (t⁻¹ • y) ≠ 0 := by
    intro h
    exact hy (by simp [dilate, Specs.D11.Ch11.ApproximateIdentityLebesguePoints.dilate_value, h])
  have h := hs hφ
  simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ht)] at h ⊢
  exact (inv_mul_lt_iff₀ ht).mp h

lemma lebesgue_ball_scale (x : Point n) {t : ℝ} (ht : 0 < t) (R : ℝ) :
    (lebesgue n (ball x (t*R))).toReal = t^n * (lebesgue n (ball (0 : Point n) R)).toReal := by
  rw [EuclideanRegularity.lebesgue_eq_volume, EuclideanRegularity.lebesgue_eq_volume]
  exact volume_ball_scale x ht R

/-- The power from dilation cancels the volume of the shrinking ball. -/
lemma tendsto_at_lebesguePoint (f φ : Point n → 𝕜) (hf : locallyIntegrable f)
    (hφ : Measurable φ) (M R : ℝ) (hM : 0 ≤ M) (hR : 0 < R)
    (hb : ∀ y, ‖φ y‖ ≤ M) (hs : Function.support φ ⊆ ball 0 R)
    (hunit : (∫ y, φ y ∂lebesgue n) = 1) (x : Point n)
    (hx : lebesguePoint f hf x) :
    Tendsto (fun t => convolution n (dilate n φ t) f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have hrad : Tendsto (fun t : ℝ => t*R) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [zero_mul] using (show Tendsto (fun t : ℝ => t)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) from nhdsWithin_le_nhds).mul_const R
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos ht hR
  have hlim := (hx.comp hrad).const_mul
    (M * (lebesgue n (ball (0 : Point n) R)).toReal)
  simp only [mul_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have he := error_bound f (dilate n φ t) hf (dilate_measurable φ hφ ht)
    ((t^n)⁻¹*M) (t*R) (mul_nonneg (inv_nonneg.mpr (pow_nonneg ht.le _)) hM)
    (dilate_bound φ M hb ht) (dilate_support φ R hs ht) (dilate_integral φ ht hunit) x
  apply he.trans_eq
  change (t^n)⁻¹ * M * (∫ y in ball x (t*R), ‖f y - f x‖ ∂lebesgue n) =
    M * (lebesgue n (ball (0 : Point n) R)).toReal *
      ((lebesgue n (ball x (t*R))).toReal⁻¹ *
        ∫ y in ball x (t*R), ‖f y - f x‖ ∂lebesgue n)
  rw [lebesgue_ball_scale x ht R]
  field_simp [pow_ne_zero n ht.ne', (ball_measure (0 : Point n) R hR).2.2.ne']

theorem approximate_identity :
    Specs.D11.Ch11.ApproximateIdentityLebesguePoints.approximate_identity := by
  intro n _ 𝕜 _ _ _ p hp f φ hfm hfp hφ hcs hbound hunit
  obtain ⟨M, hb⟩ := hbound
  have hM : 0 ≤ M := (norm_nonneg (φ 0)).trans (hb 0)
  obtain ⟨R, hR, hs⟩ := hcs.isBounded.subset_ball_lt 0 (0 : Point n)
  have hs' : Function.support φ ⊆ ball 0 R := subset_closure.trans hs
  let hf := locallyIntegrable_of_memLp hp f hfm hfp
  have hpoint (x : Point n) (hx : lebesguePoint f hf x) :
      Tendsto (fun t => convolution n f (dilate n φ t) x)
        (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
    have heq : (fun t => convolution n f (dilate n φ t) x) =
        (fun t => convolution n (dilate n φ t) f x) :=
      funext fun t => congrFun (ConvolutionYoung.commutative f (dilate n φ t)) x
    rw [heq]
    exact tendsto_at_lebesguePoint f φ hf hφ M R hM hR hb hs' hunit x hx
  refine ⟨hf, ?_, hpoint, ?_, ?_⟩
  · intro t ht x
    have hi := integrable_kernel f (dilate n φ t) hf (dilate_measurable φ hφ ht)
      ((t^n)⁻¹*M) (t*R) (dilate_bound φ M hb ht) (dilate_support φ R hs' ht) x
    have hj := (measurePreserving_const_sub x).integrable_comp_of_integrable hi
    simpa only [Function.comp_def, sub_sub_cancel, mul_comm] using hj
  · filter_upwards [ae_lebesguePoint f hf] with x hx
    exact hpoint x hx
  · intro x hx
    exact hpoint x (continuous_lebesguePoint f hf hx)

end D11.Ch11.ApproximateIdentityLebesguePoints
