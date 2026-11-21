import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.ConcentrationScaling
import MathGenome.Internal.FourierSobolev.P102.U4.ZeroExtension
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff ENNReal NNReal Topology
namespace P102.Sobolev.EndpointNoncompactness
open P102.U4

lemma scales_pos {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) : 0 < scales ρ n :=
  div_pos hρ (by positivity)

lemma scales_lt {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) : scales ρ n < ρ := by
  unfold scales
  exact (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 2)).mpr (by nlinarith)

lemma scales_tendsto (ρ : ℝ) : Tendsto (scales ρ) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  change Tendsto (fun n : ℕ => ρ / (n + 2 : ℝ)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, Function.comp_apply, mul_zero] using
    tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp h)

lemma rescale_smooth {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x₀ : Space d) (a r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (rescale φ x₀ a r) :=
  (hφ.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)).const_smul _

lemma rescale_compact {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : HasCompactSupport φ)
    (x₀ : Space d) (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasCompactSupport (rescale φ x₀ a r) := by
  let H : Space d ≃ₜ Space d := (Homeomorph.subRight x₀).trans
    (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr)))
  change HasCompactSupport ((fun _ : Space d => r ^ a) • (φ ∘ H))
  exact (hφ.comp_isClosedEmbedding H.isClosedEmbedding).smul_left

lemma rescale_center {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Space d → 𝕜) (x₀ : Space d) (a r : ℝ) :
    rescale φ x₀ a r x₀ = r ^ a • φ 0 := by simp [rescale]

/-- Smooth normalized bumps can be chosen in the canonical Euclidean space. -/
theorem exists_normalized_bump (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    ∃ φ : Space d → 𝕜, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Metric.ball 0 1 ∧ φ 0 = 1 := by
  obtain ⟨f, hfs, hfc, hfd, _, hf0⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (Metric.ball_mem_nhds (0 : Space d) zero_lt_one)
  refine ⟨fun x => (f x : 𝕜), (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hfd,
    hfc.comp_left (by simp), ?_, by simp [hf0]⟩
  exact (tsupport_comp_subset (g := fun t : ℝ => (t : 𝕜)) (by simp) f).trans hfs

/-- Every sufficiently small rescaling stays strictly inside the interior ball. -/
lemma rescale_support {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : tsupport φ ⊆ Metric.closedBall 0 1)
    (x₀ : Space d) (a : ℝ) {r ρ : ℝ} (hr : 0 < r) (hrρ : r < ρ) :
    tsupport (rescale φ x₀ a r) ⊆ Metric.ball x₀ ρ := by
  intro x hx
  have hpre : r⁻¹ • (x - x₀) ∈ tsupport φ :=
    tsupport_comp_subset_preimage φ
      (f := fun y : Space d => r⁻¹ • (y - x₀)) (by fun_prop)
      ((tsupport_smul_subset_right (fun _ : Space d => r ^ a)
        (fun y => φ (r⁻¹ • (y - x₀)))) hx)
  have hnorm : r⁻¹ * ‖x - x₀‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] using hφ hpre
  have hsmall : ‖x - x₀‖ ≤ r := by
    calc
      ‖x - x₀‖ = r * (r⁻¹ * ‖x - x₀‖) := by field_simp
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hnorm hr.le
      _ = r := mul_one _
  exact (Metric.mem_ball.mpr (by simpa only [dist_eq_norm] using hsmall.trans_lt hrρ))


/-- Exact change of variables for a Euclidean dilation and translation. The
real-valued norm formula includes q=∞, with q.toReal=0 in that case. -/
theorem dilated_lpNorm {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (φ : Space d → E) (hφ : Continuous φ) {t : ℝ} (ht : 0 < t)
    (x₀ : Space d) (q : ℝ≥0∞) :
    (eLpNorm (fun x => φ (t • (x - x₀))) q volume).toReal =
      t ^ (-(d : ℝ) / q.toReal) * (eLpNorm φ q volume).toReal := by
  have hmap : Measure.map (fun x : Space d => t • x) volume =
      (ENNReal.ofReal (t ^ d))⁻¹ • volume := by
    rw [Measure.map_addHaar_smul volume ht.ne']
    simp only [finrank_euclideanSpace, Fintype.card_fin,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht.le d)),
      ENNReal.ofReal_inv_of_pos (pow_pos ht d)]
  have htrans : eLpNorm (fun x => φ (t • (x - x₀))) q volume =
      eLpNorm (fun x => φ (t • x)) q volume :=
    eLpNorm_comp_measurePreserving
      (hφ.comp (by fun_prop : Continuous (fun x : Space d => t • x))).aestronglyMeasurable
      (measurePreserving_sub_right volume x₀)
  rw [htrans]
  change (eLpNorm (φ ∘ (fun x : Space d => t • x)) q volume).toReal = _
  rw [← eLpNorm_map_measure hφ.aestronglyMeasurable (by fun_prop), hmap,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)]
  simp only [one_div, ENNReal.toReal_inv, smul_eq_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (pow_nonneg ht.le d)]
  rw [Real.inv_rpow (pow_nonneg ht.le d), ← Real.rpow_neg (pow_nonneg ht.le d),
    ← Real.rpow_natCast_mul ht.le]
  congr 2
  ring

/-- The amplitude and Jacobian factors combine to r^(a+d/q). -/
theorem rescale_lpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Space d → 𝕜) (hφ : Continuous φ) (x₀ : Space d)
    (a : ℝ) {r : ℝ} (hr : 0 < r) (q : ℝ≥0∞) :
    (eLpNorm (rescale φ x₀ a r) q volume).toReal =
      r ^ (a + (d : ℝ) / q.toReal) * (eLpNorm φ q volume).toReal := by
  change (eLpNorm ((r ^ a) • (fun x => φ (r⁻¹ • (x - x₀)))) q volume).toReal = _
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, enorm_eq_nnnorm, ENNReal.coe_toReal,
    coe_nnnorm, Real.norm_of_nonneg (Real.rpow_nonneg hr.le _),
    dilated_lpNorm φ hφ (inv_pos.mpr hr)]
  rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, ← mul_assoc, ← Real.rpow_add hr]
  congr 2
  ring

/-- The ordinary chain rule for the exact source scaling. -/
theorem rescale_fderiv {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x₀ : Space d) (a : ℝ) {r : ℝ} (hr : 0 < r) (x z : Space d) :
    fderiv ℝ (rescale φ x₀ a r) x z =
      r ^ (a - 1) • fderiv ℝ φ (r⁻¹ • (x - x₀)) z := by
  have hi : HasFDerivAt (fun y : Space d => r⁻¹ • (y - x₀))
      (r⁻¹ • ContinuousLinearMap.id ℝ (Space d)) x :=
    ((hasFDerivAt_id x).sub_const x₀).const_smul r⁻¹
  have ho := ((hφ.differentiable (by simp) _).hasFDerivAt.comp x hi).const_smul (r ^ a)
  have heq := congrArg (fun L : Space d →L[ℝ] 𝕜 => L z) ho.fderiv
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul] at heq
  rw [Real.rpow_sub hr, Real.rpow_one, div_eq_mul_inv]
  exact heq



lemma rescale_critical_lpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0} (hp : 1 ≤ p) (hpd : p < d)
    (φ : Space d → 𝕜) (hφ : Continuous φ) (x₀ : Space d)
    {r : ℝ} (hr : 0 < r) :
    (eLpNorm (rescale φ x₀ (1 - (d : ℝ) / p) r) (criticalExponent d p) volume).toReal =
      (eLpNorm φ (criticalExponent d p) volume).toReal := by
  rw [rescale_lpNorm φ hφ x₀ _ hr]
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt
    (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp))
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt
    (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp.trans hpd.le))
  have hdp : (d : ℝ) - p ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hpd))
  have hq : ((criticalExponent d p : ℝ≥0∞)).toReal =
      (d : ℝ) * p / ((d : ℝ) - p) := by
    simp only [ENNReal.coe_toReal, criticalExponent, NNReal.coe_div,
      NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_sub hpd.le]
  have hexp : 1 - (d : ℝ) / p + (d : ℝ) / (criticalExponent d p : ℝ≥0∞).toReal = 0 := by
    rw [hq]
    field_simp
    ring
  rw [hexp, Real.rpow_zero, one_mul]

lemma rescale_coordinate_derivative_lpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0) {φ : Space d → 𝕜} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x₀ : Space d) {r : ℝ} (hr : 0 < r) (i : Fin d) :
    (eLpNorm (fun x => fderiv ℝ (rescale φ x₀ (1 - (d : ℝ) / p) r) x
        (coordinateVector d i)) p volume).toReal =
      (eLpNorm (fun x => fderiv ℝ φ x (coordinateVector d i)) p volume).toReal := by
  have heq : (fun x => fderiv ℝ (rescale φ x₀ (1 - (d : ℝ) / p) r) x
      (coordinateVector d i)) =
      rescale (fun x => fderiv ℝ φ x (coordinateVector d i)) x₀
        ((1 - (d : ℝ) / p) - 1) r := by
    funext x
    exact rescale_fderiv hφ x₀ _ hr x _
  rw [heq, rescale_lpNorm _
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) x₀ _ hr,
    ENNReal.coe_toReal]
  have hexp : (1 - (d : ℝ) / p) - 1 + (d : ℝ) / p = 0 := by ring
  rw [hexp, Real.rpow_zero, one_mul]

lemma bump_lpNorm_pos {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) {q : ℝ≥0∞} (hq : q ≠ 0) :
    0 < (eLpNorm φ q volume).toReal := by
  apply ENNReal.toReal_pos
  · intro hz
    have hae := (eLpNorm_eq_zero_iff hq).mp hz
    have heq := (hφ.ae_eq_iff_eq volume continuous_const).mp hae
    have : (1 : 𝕜) = 0 := hφ0.symm.trans (congrFun heq 0)
    exact one_ne_zero this
  · exact (hφ.memLp_of_hasCompactSupport hcompact).eLpNorm_ne_top



/-- Canonical Sobolev realization of a smooth test, using the proved weak equations. -/
def smoothClass {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : TestSpace 𝕜 Ω) : Sobolev 𝕜 Ω 1 p :=
  Classical.choose (zeroExtension_smoothInclusion Ω 1 p φ)

lemma smoothClass_underlying {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : TestSpace 𝕜 Ω) :
    sobolevUnderlying (smoothClass Ω p φ) = testToDomainLp Ω p φ :=
  Classical.choose_spec (zeroExtension_smoothInclusion Ω 1 p φ)

lemma smoothClass_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : TestSpace 𝕜 Ω) (α : SobolevIndex d 1) :
    sobolevDerivative (smoothClass Ω p φ) α =
      testToDomainLp Ω p (testPartialWord Ω (α.val.sort (· ≤ ·)) φ) := by
  apply Eq.symm
  apply sobolev_derivative_unique Ω 1 p
  rw [smoothClass_underlying, regular_testToDomainLp, regular_testToDomainLp,
    derivative_classicalCompatibility d 𝕜 Ω α.val φ
      (φ.contDiff.of_le (by simp)).contDiffOn]
  congr 1
  exact (testPartialWord_coe Ω _ φ).symm

lemma smoothClass_first_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : TestSpace 𝕜 Ω) (i : Fin d) :
    (sobolevDerivative (smoothClass Ω p φ) (firstIndex i) : Space d → 𝕜) =ᵐ[
      volume.restrict (Ω : Set (Space d))]
      (fun x => fderiv ℝ φ x (coordinateVector d i)) := by
  rw [smoothClass_derivative]
  convert testToDomainLp_ae Ω p (testPartialWord Ω [i] φ) using 1
  · simp [firstIndex]
  · rw [testPartialWord_coe]
    rfl

/-- The classical gradient with the Euclidean, also for complex scalars, norm. -/
def classicalGradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (φ : Space d → 𝕜)
    (x : Space d) : EuclideanSpace 𝕜 (Fin d) :=
  WithLp.toLp 2 (fun i => fderiv ℝ φ x (coordinateVector d i))

lemma classicalGradient_continuous {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Continuous (classicalGradient φ) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const)

lemma classicalGradient_support {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Space d → 𝕜) : tsupport (classicalGradient φ) ⊆ tsupport φ := by
  exact (tsupport_comp_subset (g := fun L : Space d →L[ℝ] 𝕜 =>
    (WithLp.toLp 2 (fun i : Fin d => L (coordinateVector d i)) : EuclideanSpace 𝕜 (Fin d)))
    (by ext i; simp) (fderiv ℝ φ)).trans (tsupport_fderiv_subset ℝ)

lemma classicalGradient_compact {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : HasCompactSupport φ) :
    HasCompactSupport (classicalGradient φ) :=
  hφ.of_isClosed_subset (isClosed_tsupport _) (classicalGradient_support φ)

lemma smoothClass_gradient_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : TestSpace 𝕜 Ω) :
    weakGradientOn (smoothClass Ω p φ) =ᵐ[volume.restrict (Ω : Set (Space d))]
      classicalGradient φ := by
  filter_upwards [ae_all_iff.mpr (smoothClass_first_ae Ω p φ)] with x hx
  exact PiLp.ext fun i => hx i


lemma eLpNorm_restrict_of_support {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Ω : Opens (Space d)) {f : Space d → E} (hf : tsupport f ⊆ Ω)
    (q : ℝ≥0∞) : eLpNorm f q (volume.restrict (Ω : Set (Space d))) =
      eLpNorm f q volume := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet]
  congr 1
  exact Set.indicator_eq_self.mpr ((subset_tsupport _).trans hf)

lemma classicalGradient_rescale {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x₀ : Space d) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    classicalGradient (rescale φ x₀ a r) =
      r ^ (a - 1) • (fun x => classicalGradient φ (r⁻¹ • (x - x₀))) := by
  funext x
  apply PiLp.ext
  intro i
  exact rescale_fderiv hφ x₀ a hr x (coordinateVector d i)

lemma rescale_gradient_lpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x₀ : Space d) (p : ℝ≥0) {r : ℝ} (hr : 0 < r) :
    (eLpNorm (classicalGradient (rescale φ x₀ (1 - (d : ℝ) / p) r)) p volume).toReal =
      (eLpNorm (classicalGradient φ) p volume).toReal := by
  rw [classicalGradient_rescale hφ x₀ _ hr, eLpNorm_const_smul, ENNReal.toReal_mul,
    enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm,
    Real.norm_of_nonneg (Real.rpow_nonneg hr.le _),
    dilated_lpNorm _ (classicalGradient_continuous hφ) (inv_pos.mpr hr),
    ENNReal.coe_toReal, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le,
    ← mul_assoc, ← Real.rpow_add hr]
  have he : 1 - (d : ℝ) / p - 1 - (-(d : ℝ) / p) = 0 := by ring
  change r ^ (1 - (d : ℝ) / p - 1 - (-(d : ℝ) / p)) * _ = _
  rw [he, Real.rpow_zero, one_mul]

lemma classicalGradient_lpNorm_pos {d : ℕ} (hd : 0 < d) {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Metric.ball 0 1)
    (h0 : φ 0 = 1) {q : ℝ≥0∞} (hq : q ≠ 0) :
    0 < (eLpNorm (classicalGradient φ) q volume).toReal := by
  apply ENNReal.toReal_pos
  · intro hz
    have heq := ((classicalGradient_continuous hφ).ae_eq_iff_eq volume continuous_const).mp
      ((eLpNorm_eq_zero_iff hq).mp hz)
    have hder : ∀ x, fderiv ℝ φ x = 0 := by
      intro x
      apply ContinuousLinearMap.ext
      intro z
      have hb := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr z
      rw [← hb, map_sum]
      have hi (i : Fin d) : fderiv ℝ φ x (coordinateVector d i) = 0 :=
        congrArg (fun v : EuclideanSpace 𝕜 (Fin d) => v i) (congrFun heq x)
      simp only [map_smul, coordinateVector] at hi ⊢
      simp only [hi, smul_zero, Finset.sum_const_zero, zero_apply]
    let i : Fin d := ⟨0, hd⟩
    have hn : ‖coordinateVector d i‖ = 1 :=
      (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one i
    have hout : coordinateVector d i ∉ tsupport φ := by
      intro hx
      have := hs hx
      simp [Metric.mem_ball, dist_zero_right, hn] at this
    have hv := is_const_of_fderiv_eq_zero (hφ.differentiable (by simp)) hder
      (coordinateVector d i) 0
    rw [image_eq_zero_of_notMem_tsupport hout, h0] at hv
    exact zero_ne_one hv
  · exact ((classicalGradient_continuous hφ).memLp_of_hasCompactSupport
      (classicalGradient_compact hc)).eLpNorm_ne_top

lemma smoothClass_derivative_norm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : TestSpace 𝕜 Ω)
    (α : SobolevIndex d 1) :
    ‖sobolevDerivative (smoothClass Ω p φ) α‖ =
      (eLpNorm (partialWord φ (α.val.sort (· ≤ ·))) p volume).toReal := by
  rw [smoothClass_derivative, Lp.norm_def,
    eLpNorm_congr_ae (testToDomainLp_ae Ω p _),
    eLpNorm_restrict_of_support Ω (testPartialWord Ω _ φ).tsupport_subset]
  rw [testPartialWord_coe]

lemma rescale_partial_lpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x₀ : Space d) (p : ℝ≥0) {r : ℝ} (hr : 0 < r)
    (α : SobolevIndex d 1) :
    (eLpNorm (partialWord (rescale φ x₀ (1 - (d : ℝ) / p) r)
      (α.val.sort (· ≤ ·))) p volume).toReal =
      (if α.val = 0 then r else 1) *
        (eLpNorm (partialWord φ (α.val.sort (· ≤ ·))) p volume).toReal := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp α.property with hz | ho
  · have hα := Multiset.card_eq_zero.mp hz
    simp only [hα, Multiset.sort_zero, partialWord, ↓reduceIte]
    rw [rescale_lpNorm φ hφ.continuous x₀ _ hr, ENNReal.coe_toReal]
    have he : 1 - (d : ℝ) / p + (d : ℝ) / p = 1 := by ring
    rw [he, Real.rpow_one]
  · obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp ho
    simp only [hi, Multiset.sort_singleton, partialWord, Multiset.singleton_ne_zero,
      ↓reduceIte, one_mul]
    exact rescale_coordinate_derivative_lpNorm p hφ x₀ hr i

lemma smoothClass_gradient_memLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : TestSpace 𝕜 Ω) :
    MemLp (weakGradientOn (smoothClass Ω p φ)) p (volume.restrict (Ω : Set (Space d))) := by
  apply (memLp_congr_ae (smoothClass_gradient_ae Ω p φ)).mpr
  exact (classicalGradient_continuous φ.contDiff).memLp_of_hasCompactSupport
    (classicalGradient_compact φ.hasCompactSupport)

lemma smoothClass_gradient_eLpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : TestSpace 𝕜 Ω) :
    eLpNorm (weakGradientOn (smoothClass Ω p φ)) p (volume.restrict (Ω : Set (Space d))) =
      eLpNorm (classicalGradient φ) p volume := by
  rw [eLpNorm_congr_ae (smoothClass_gradient_ae Ω p φ)]
  exact eLpNorm_restrict_of_support Ω
    ((classicalGradient_support φ).trans φ.tsupport_subset) p

set_option maxHeartbeats 500000 in
/-- The common family on an arbitrary nonempty open set. No extension or
boundary regularity is assumed: each member is a compactly supported test. -/
theorem concentration_family : ScalingExpected.Construction := by
  intro d hd 𝕜 _ Ω hΩ p hp _
  classical
  obtain ⟨x₀, hx₀⟩ := hΩ
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen x₀ hx₀
  obtain ⟨φ, hφ, hc, hs, hφ0⟩ := exists_normalized_bump d 𝕜
  have hs' : tsupport φ ⊆ Metric.closedBall 0 1 := hs.trans Metric.ball_subset_closedBall
  let f := rescale φ x₀ (1 - (d : ℝ) / p)
  let T : ∀ r : ℝ, 0 < r → r < ρ → TestSpace 𝕜 Ω := fun r hr hrρ =>
    ⟨f r, rescale_smooth hφ x₀ _ r, rescale_compact hc x₀ _ hr.ne',
      (rescale_support hs' x₀ _ hr hrρ).trans hball⟩
  let U : ℝ → U4.Sobolev 𝕜 Ω 1 p := fun r =>
    if h : 0 < r ∧ r < ρ then smoothClass Ω p (T r h.1 h.2) else 0
  have hU (r : ℝ) (hr : 0 < r) (hrρ : r < ρ) :
      U r = smoothClass Ω p (T r hr hrρ) := by
    dsimp only [U]
    rw [dite_eq_left (show 0 < r ∧ r < ρ from ⟨hr, hrρ⟩)]
  let b : SobolevIndex d 1 → ℝ := fun α =>
    (eLpNorm (partialWord φ (α.val.sort (· ≤ ·))) p volume).toReal
  let B := max ρ 1 * ∑ α, b α
  have hB : 0 ≤ B := mul_nonneg (zero_le_one.trans (le_max_right _ _))
    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
  have hbound (r : ℝ) (hr : 0 < r) (hrρ : r < ρ) : ‖U r‖ ≤ B := by
    rw [hU r hr hrρ, sobolev_norm Ω 1 p]
    change (∑ α, ‖sobolevDerivative (smoothClass Ω p (T r hr hrρ)) α‖) ≤
      max ρ 1 * ∑ α, b α
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α _
    rw [smoothClass_derivative_norm]
    change (eLpNorm (partialWord (rescale φ x₀ (1 - (d : ℝ) / p) r)
      (α.val.sort (· ≤ ·))) p volume).toReal ≤ max ρ 1 * b α
    rw [rescale_partial_lpNorm hφ x₀ p hr α]
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    split_ifs
    · exact hrρ.le.trans (le_max_left _ _)
    · exact le_max_right _ _
  have hp0 : (p : ℝ≥0∞) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out))
  let c := (eLpNorm (classicalGradient φ) p volume).toReal
  have hcpos : 0 < c := classicalGradient_lpNorm_pos hd hφ hc hs hφ0 hp0
  refine ⟨{
    center := x₀, center_mem := hx₀, radius := ρ, radius_pos := hρ,
    ball_subset := hball, bump := φ, smooth := hφ, compact := hc, support := hs,
    value_zero := hφ0, U := U, representative := ?_, derivative_representative := ?_, support_rescale := ?_,
    bound := B, bound_nonneg := hB, bounded_norm := hbound,
    gradient_size := c, gradient_size_pos := hcpos,
    gradient_memLp := ?_, gradient_fixed := ?_ }⟩
  · intro r hr hrρ
    change (sobolevUnderlying (U r) : Space d → 𝕜) =ᵐ[_] _
    rw [hU r hr hrρ, smoothClass_underlying]
    exact testToDomainLp_ae Ω p (T r hr hrρ)
  · intro r hr hrρ i
    rw [hU r hr hrρ]
    exact smoothClass_first_ae Ω p (T r hr hrρ) i
  · intro r hr hrρ
    exact (T r hr hrρ).tsupport_subset
  · intro r hr hrρ
    rw [hU r hr hrρ]
    exact smoothClass_gradient_memLp Ω p (T r hr hrρ)
  · intro r hr hrρ
    rw [hU r hr hrρ, smoothClass_gradient_eLpNorm]
    have hfin : eLpNorm (classicalGradient (T r hr hrρ)) p volume ≠ ⊤ :=
      ((classicalGradient_continuous (T r hr hrρ).contDiff).memLp_of_hasCompactSupport
        (classicalGradient_compact (T r hr hrρ).hasCompactSupport)).eLpNorm_ne_top
    calc
      _ = ENNReal.ofReal (eLpNorm (classicalGradient (T r hr hrρ)) p volume).toReal :=
        (ENNReal.ofReal_toReal hfin).symm
      _ = ENNReal.ofReal c := congrArg ENNReal.ofReal (rescale_gradient_lpNorm hφ x₀ p hr)

/-- Exact scalar scaling, including the finite target exponents at the endpoints. -/
theorem scalar_scaling : ScalingExpected.ScalarScaling := by
  intro d 𝕜 _ φ hφ x₀ a r hr q
  exact rescale_lpNorm φ hφ x₀ a hr q

theorem derivative_scaling : ScalingExpected.DerivativeScaling := by
  intro d 𝕜 _ φ hφ x₀ a r hr x z
  exact rescale_fderiv hφ x₀ a hr x z

theorem scale_sequence : ScalingExpected.ScaleSequence := by
  intro ρ hρ
  exact ⟨fun n => ⟨scales_pos hρ n, scales_lt hρ n⟩, scales_tendsto ρ⟩


/-- Extended-norm form of the scaling law for compactly supported functions.
Finiteness makes the real-valued formula an exact ENNReal identity. -/
lemma rescale_eLpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (x₀ : Space d) (a : ℝ) {r : ℝ} (hr : 0 < r) (q : ℝ≥0∞) :
    eLpNorm (rescale φ x₀ a r) q volume =
      ENNReal.ofReal (r ^ (a + (d : ℝ) / q.toReal)) * eLpNorm φ q volume := by
  have hcont : Continuous (rescale φ x₀ a r) :=
    (hφ.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)).const_smul _
  have hf := (hcont.memLp_of_hasCompactSupport (p := q) (μ := volume)
    (rescale_compact hc x₀ a hr.ne')).eLpNorm_ne_top
  have hg := (hφ.memLp_of_hasCompactSupport (p := q) (μ := volume) hc).eLpNorm_ne_top
  calc
    _ = ENNReal.ofReal (eLpNorm (rescale φ x₀ a r) q volume).toReal :=
      (ENNReal.ofReal_toReal hf).symm
    _ = ENNReal.ofReal (r ^ (a + (d : ℝ) / q.toReal) * (eLpNorm φ q volume).toReal) :=
      congrArg ENNReal.ofReal (rescale_lpNorm φ hφ x₀ a hr q)
    _ = _ := by rw [ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), ENNReal.ofReal_toReal hg]

theorem family_scalar_scaling : ScalingExpected.FamilyScalarScaling := by
  intro d 𝕜 _ Ω p _ D r hr hrρ q
  refine ⟨((rescale_smooth D.smooth D.center _ r).continuous.memLp_of_hasCompactSupport
    (rescale_compact D.compact D.center _ hr.ne')), ?_⟩
  rw [eLpNorm_restrict_of_support Ω (D.support_rescale r hr hrρ)]
  exact rescale_eLpNorm D.smooth.continuous D.compact D.center _ hr q

end P102.Sobolev.EndpointNoncompactness
