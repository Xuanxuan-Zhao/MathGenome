import MathGenome.Internal.LinearPDE.P201.Heat.CausalFundamental
import MathGenome.Internal.LinearPDE.P201Specs.Heat.GaussianSemigroup
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.HeatLpMaximalDomain
import MathGenome.Internal.FourierSobolev.P102.U2.ApproximateIdentities

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
namespace P201.Heat

abbrev heatConvolution : P201Specs.Heat.heatConvolutionType :=
  @P201Specs.Heat.heatConvolution
abbrev heatFlow : P201Specs.Heat.heatFlowType := @P201Specs.Heat.heatFlow

theorem kernelProperties : P201Specs.Heat.kernelPropertiesStatement :=
  ⟨gaussianNonnegative, gaussianIntegrable, gaussianMass, gaussianHeatEquation,
    gaussianConvolution, causalLocallyIntegrable, causalFundamental⟩

lemma gaussian_toLp (n : ℕ) (t : ℝ) (x : Fin n → ℝ) :
    gaussianKernel n t (WithLp.toLp 2 x) = ExpandedFA.Models.HeatLp.gaussian t x := by
  unfold gaussianKernel P201Specs.Heat.gaussianKernel ExpandedFA.Models.HeatLp.gaussian
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

/-- The pointwise convolution agrees with the library's translated-kernel
formula, after changing from product coordinates to Euclidean coordinates. -/
lemma heatConvolution_toLp {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (t : ℝ) (f : Space n → 𝕜) (x : Fin n → ℝ) :
    heatConvolution t f (WithLp.toLp 2 x) =
      ExpandedFA.Models.HeatLp.heatConvolution t (f ∘ WithLp.toLp 2) x := by
  change (∫ y, gaussianKernel n t (WithLp.toLp 2 x - y) • f y) = _
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toHomeomorph.measurableEmbedding]
  change (∫ y : Fin n → ℝ,
    gaussianKernel n t (WithLp.toLp 2 (x - y)) • f (WithLp.toLp 2 y)) = _
  simp_rw [gaussian_toLp]
  rw [← integral_sub_left_eq_self (fun y : Fin n → ℝ =>
    ExpandedFA.Models.HeatLp.gaussian t (x - y) • f (WithLp.toLp 2 y)) volume x]
  simp [ExpandedFA.Models.HeatLp.heatConvolution, sub_sub_cancel]

/-- Pullback and pushforward of Lp classes preserve their exact norms. -/
def coordinateLp {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MeasureTheory.Lp 𝕜 p (spatialMeasure n) ≃ₗᵢ[𝕜]
      ExpandedFA.Models.HeatLp.ScalarLp 𝕜 n p where
  toLinearEquiv :=
    { toLinearMap := Lp.compMeasurePreservingₗ 𝕜 (WithLp.toLp 2)
        (PiLp.volume_preserving_toLp (Fin n))
      invFun := Lp.compMeasurePreserving (WithLp.ofLp)
        (PiLp.volume_preserving_ofLp (Fin n))
      left_inv := by
        intro f
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
        rw [← Lp.compMeasurePreserving_comp_apply]
        exact Lp.compMeasurePreserving_id_apply f
      right_inv := by
        intro f
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
        rw [← Lp.compMeasurePreserving_comp_apply]
        exact Lp.compMeasurePreserving_id_apply f }
  norm_map' := fun f => Lp.norm_compMeasurePreserving f _

lemma coordinateLp_ae {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) :
    coordinateLp p f =ᵐ[volume] f ∘ WithLp.toLp 2 :=
  Lp.coeFn_compMeasurePreserving f _

lemma coordinateLp_symm_ae {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : ExpandedFA.Models.HeatLp.ScalarLp 𝕜 n p) :
    (coordinateLp p).symm f =ᵐ[spatialMeasure n] f ∘ WithLp.ofLp :=
  Lp.coeFn_compMeasurePreserving f _

/-- Conjugate the product-coordinate heat operator by the exact Lp isometry. -/
def euclideanHeatOperator {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (t : ℝ≥0) :
    MeasureTheory.Lp 𝕜 p (spatialMeasure n) →L[𝕜]
      MeasureTheory.Lp 𝕜 p (spatialMeasure n) :=
  (coordinateLp p).symm.toContinuousLinearEquiv.toContinuousLinearMap |>.comp
    ((ExpandedFA.Models.HeatLp.heatOperators t).comp
      (coordinateLp p).toContinuousLinearEquiv.toContinuousLinearMap)

lemma euclideanHeatOperator_representative {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (t : ℝ≥0) (ht : 0 < t)
    (f : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) :
    euclideanHeatOperator p t f =ᵐ[spatialMeasure n] heatConvolution t f := by
  have hrep := (PiLp.volume_preserving_ofLp (Fin n)).quasiMeasurePreserving.ae
    (ExpandedFA.Models.HeatLp.heatOperators_representative t ht (coordinateLp p f))
  have hconv := ExpandedFA.Models.HeatLp.heatConvolution_congr (t := (t : ℝ))
    (coordinateLp_ae p f)
  filter_upwards [coordinateLp_symm_ae p
    (ExpandedFA.Models.HeatLp.heatOperators t (coordinateLp p f)), hrep] with x hx hr
  change ((coordinateLp p).symm
    (ExpandedFA.Models.HeatLp.heatOperators t (coordinateLp p f))) x = _
  rw [hx, Function.comp_apply, hr, hconv]
  exact (heatConvolution_toLp t f (WithLp.ofLp x)).symm

lemma heatConvolution_integrable_toLp {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (t : ℝ) (f : Space n → 𝕜) (x : Fin n → ℝ) :
    Integrable (fun y => gaussianKernel n t (WithLp.toLp 2 x - y) • f y) ↔
      Integrable (fun y : Fin n → ℝ =>
        ExpandedFA.Models.HeatLp.gaussian t y • f (WithLp.toLp 2 (x - y))) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toHomeomorph.measurableEmbedding]
  change Integrable (fun y : Fin n → ℝ =>
    gaussianKernel n t (WithLp.toLp 2 (x - y)) • f (WithLp.toLp 2 y)) ↔ _
  simp_rw [gaussian_toLp]
  simpa only [sub_sub_cancel] using
    (integrable_comp_sub_left (μ := (volume : Measure (Fin n → ℝ)))
      (fun y => ExpandedFA.Models.HeatLp.gaussian t (x - y) • f (WithLp.toLp 2 y)) x).symm

lemma heatConvolution_integrable_ae {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {t : ℝ} (ht : 0 < t)
    (f : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) :
    ∀ᵐ x ∂spatialMeasure n,
      Integrable (fun y => gaussianKernel n t (x - y) • f y) (spatialMeasure n) := by
  have hm := (Lp.memLp f).comp_measurePreserving (PiLp.volume_preserving_toLp (Fin n))
  have hi := (ExpandedFA.Models.HeatLp.heatConvolution_memLp_bound p Fact.out ht
    (f ∘ WithLp.toLp 2) hm).1
  have hx := (PiLp.volume_preserving_ofLp (Fin n)).quasiMeasurePreserving.ae hi
  filter_upwards [hx] with x hx
  exact (heatConvolution_integrable_toLp t f (WithLp.ofLp x)).2 hx

theorem lpSemigroup : P201Specs.Heat.lpSemigroupStatement := by
  intro n _ 𝕜 _ p _
  refine ⟨euclideanHeatOperator p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro f
    change (coordinateLp p).symm
      (ExpandedFA.Models.HeatLp.heatOperators 0 (coordinateLp p f)) = f
    rw [ExpandedFA.Models.HeatLp.heatOperators_zero]
    exact (coordinateLp p).symm_apply_apply f
  · intro t s
    apply ContinuousLinearMap.ext
    intro f
    change (coordinateLp p).symm
      (ExpandedFA.Models.HeatLp.heatOperators (t+s) (coordinateLp p f)) =
        (coordinateLp p).symm (ExpandedFA.Models.HeatLp.heatOperators t
          (coordinateLp p ((coordinateLp p).symm
            (ExpandedFA.Models.HeatLp.heatOperators s (coordinateLp p f)))))
    rw [(coordinateLp p).apply_symm_apply,
      ExpandedFA.Models.HeatLp.heatOperators_add_time]
    rfl
  · intro t f
    change ‖(coordinateLp p).symm
      (ExpandedFA.Models.HeatLp.heatOperators t (coordinateLp p f))‖ ≤ ‖f‖
    rw [(coordinateLp p).symm.norm_map]
    calc
      _ ≤ 1 * ‖coordinateLp p f‖ :=
        (ExpandedFA.Models.HeatLp.heatOperators (𝕜 := 𝕜) (d := n) (p := p) t).le_of_opNorm_le
          (ExpandedFA.Models.HeatLp.heatOperators_norm_le t) _
      _ = _ := by simp
  · intro t f
    by_cases ht : t = 0
    · subst t
      change ((coordinateLp p).symm
        (ExpandedFA.Models.HeatLp.heatOperators 0 (coordinateLp p f)) : Space n → 𝕜)
        =ᵐ[spatialMeasure n] _
      rw [ExpandedFA.Models.HeatLp.heatOperators_zero]
      simp [P201Specs.Heat.heatFlow]
    · simpa [P201Specs.Heat.heatFlow, ht] using
        euclideanHeatOperator_representative p t (pos_iff_ne_zero.mpr ht) f
  · intro t ht f
    exact heatConvolution_integrable_ae p (NNReal.coe_pos.mpr ht) f
  · intro hp f
    exact (coordinateLp p).symm.continuous.comp
      ((ExpandedFA.Models.HeatLp.heatSemigroup (𝕜 := 𝕜) (d := n) hp).continuous_orbit
        (coordinateLp p f))

lemma gaussian_dilation {n : ℕ} {s : ℝ} (hs : 0 < s) (x : Space n) :
    gaussianKernel n (s ^ 2) (s • x) = (s ^ n)⁻¹ * gaussianKernel n 1 x := by
  have h := ExpandedFA.Models.HeatLp.gaussian_dilation hs (WithLp.ofLp x)
  simpa only [← gaussian_toLp, WithLp.toLp_smul, WithLp.toLp_ofLp] using h

lemma heatConvolution_swap {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (t : ℝ) (f : Space n → 𝕜) (x : Space n) :
    heatConvolution t f x = ∫ y, gaussianKernel n t y • f (x - y) := by
  change (∫ y, gaussianKernel n t (x - y) • f y) = _
  rw [← integral_sub_left_eq_self
    (fun y => gaussianKernel n t (x - y) • f y) volume x]
  simp only [sub_sub_cancel]

lemma heatConvolution_dilation {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {s : ℝ} (hs : 0 < s) (f : Space n → 𝕜) (x : Space n) :
    heatConvolution (s ^ 2) f x = ∫ y, gaussianKernel n 1 y • f (x - s • y) := by
  rw [heatConvolution_swap]
  have he := Measure.integral_comp_smul_of_nonneg volume
    (fun y : Space n => gaussianKernel n (s ^ 2) y • f (x - y)) s (hR := hs.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin] at he
  simp_rw [gaussian_dilation hs, mul_smul, integral_smul] at he
  exact (smul_right_injective _ (inv_ne_zero (pow_ne_zero _ hs.ne'))) he.symm

lemma bounded_convolution_integrable {n : ℕ} (g : Space n → ℝ)
    (hg : Continuous g) (hb : ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M) {t : ℝ} (ht : 0 < t)
    (x : Space n) : Integrable (fun y => gaussianKernel n t (x - y) * g y) := by
  obtain ⟨M, hM⟩ := hb
  exact ((gaussian_integrable_aux n ht).comp_sub_left x).mul_bdd
    hg.aestronglyMeasurable (Eventually.of_forall hM)

/-- After dilation, the far part has a fixed integrable dominating density.
This estimate uses the Euclidean norm, in every dimension including one. -/
lemma gaussian_dilated_tail {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun s : ℝ => ∫ y in {y : Space n | δ ≤ ‖s • y‖}, gaussianKernel n 1 y)
      (𝓝 0) (𝓝 0) := by
  have hmeas (s : ℝ) : MeasurableSet {y : Space n | δ ≤ ‖s • y‖} :=
    measurableSet_le measurable_const (by fun_prop)
  have hi := gaussian_integrable_aux n (t := 1) zero_lt_one
  have hnonneg (y : Space n) : 0 ≤ gaussianKernel n 1 y := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    positivity
  have hlim (y : Space n) :
      Tendsto (fun s : ℝ => {y : Space n | δ ≤ ‖s • y‖}.indicator
        (gaussianKernel n 1) y) (𝓝 0) (𝓝 0) := by
    have hc : Tendsto (fun s : ℝ => ‖s • y‖) (𝓝 0) (𝓝 0) := by
      have hc' : Continuous (fun s : ℝ => ‖s • y‖) := by fun_prop
      simpa using hc'.tendsto (0 : ℝ)
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_order.mp hc).2 δ hδ] with s hs
    simp only [indicator_of_notMem (show y ∉ {y : Space n | δ ≤ ‖s • y‖}
      from not_le.mpr hs)]
  have h := tendsto_integral_filter_of_dominated_convergence
    (gaussianKernel n 1)
    (Eventually.of_forall fun s : ℝ => hi.aestronglyMeasurable.indicator (hmeas s))
    (Eventually.of_forall fun s : ℝ => Eventually.of_forall fun y : Space n => by
      by_cases hy : δ ≤ ‖s • y‖
      · simp [hy, Real.norm_of_nonneg (hnonneg y)]
      · simp [hy, hnonneg y]) hi (Eventually.of_forall hlim)
  simpa only [integral_indicator (hmeas _), integral_zero] using h

/-- Near/far recovery on any set where one common spatial modulus is
available. Compact continuity and global uniform continuity both supply it. -/
lemma bounded_recovery_on {n : ℕ} (g : Space n → ℝ) (hg : Continuous g)
    (hb : ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M) (K : Set (Space n))
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ y, ‖y‖ < δ → ‖g (x-y) - g x‖ < ε) :
    TendstoUniformlyOn (fun t => heatConvolution t g) g (𝓝[>] 0) K := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have hi := gaussian_integrable_aux n (t := 1) zero_lt_one
  have hnonneg (y : Space n) : 0 ≤ gaussianKernel n 1 y := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    positivity
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := hmod (ε / 2) (half_pos hε)
  have htail := ((gaussian_dilated_tail (n := n) hδ).comp hsqrt).const_mul (2 * M)
  simp only [mul_zero] at htail
  filter_upwards [(tendsto_order.mp htail).2 (ε / 2) (half_pos hε),
    self_mem_nhdsWithin] with t ht (htpos : 0 < t)
  intro x hx
  have hconv : Integrable (fun y : Space n =>
      gaussianKernel n 1 y * g (x - Real.sqrt t • y)) :=
    hi.mul_bdd (show Continuous (fun y : Space n => g (x - Real.sqrt t • y)) by
      fun_prop).aestronglyMeasurable
      (Eventually.of_forall fun y => hM _)
  have heq : heatConvolution t g x - g x =
      ∫ y : Space n, gaussianKernel n 1 y * (g (x - Real.sqrt t • y) - g x) := by
    have hdil := heatConvolution_dilation (Real.sqrt_pos.mpr htpos) g x
    rw [Real.sq_sqrt htpos.le] at hdil
    rw [hdil]
    simp only [smul_eq_mul]
    simp_rw [mul_sub]
    rw [integral_sub hconv (hi.mul_const (g x)), integral_mul_const,
      gaussian_mass_aux n zero_lt_one, one_mul]
  rw [dist_comm, dist_eq_norm, heq]
  have hlocal : ∀ y ∈ {y : Space n | ‖Real.sqrt t • y‖ < δ},
      ‖gaussianKernel n 1 y * (g (x - Real.sqrt t • y) - g x)‖ ≤
        gaussianKernel n 1 y * (ε / 2) := by
    intro y hy
    rw [norm_mul, Real.norm_of_nonneg (hnonneg y)]
    exact mul_le_mul_of_nonneg_left (hnear x hx _ hy).le (hnonneg y)
  have hbound : ∀ y : Space n,
      ‖gaussianKernel n 1 y * (g (x - Real.sqrt t • y) - g x)‖ ≤
        gaussianKernel n 1 y * (2 * M) := by
    intro y
    rw [norm_mul, Real.norm_of_nonneg (hnonneg y)]
    apply mul_le_mul_of_nonneg_left _ (hnonneg y)
    exact (norm_sub_le _ _).trans (by linarith [hM (x - Real.sqrt t • y), hM x])
  have hest := P102.U2.ApproximateIdentities.norm_integral_le_near_add_tail
    hi hnonneg (measurableSet_lt (by fun_prop) measurable_const)
    (half_pos hε).le hlocal hbound
  have hc : {y : Space n | ‖Real.sqrt t • y‖ < δ}ᶜ =
      {y : Space n | δ ≤ ‖Real.sqrt t • y‖} := by ext y; simp
  rw [hc, gaussian_mass_aux n zero_lt_one, mul_one] at hest
  dsimp only [Function.comp_apply] at ht
  linarith

theorem boundedContinuousRecovery : P201Specs.Heat.boundedContinuousRecoveryStatement := by
  intro n _ g hg hb
  refine ⟨fun _ ht x => bounded_convolution_integrable g hg hb ht x, ?_⟩
  intro K hK
  apply bounded_recovery_on g hg hb K
  intro ε hε
  have hU := hK.uniformContinuousAt_of_continuousAt g
    (fun _ _ => hg.continuousAt) (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hprop⟩ := Metric.mem_uniformity_dist.mp hU
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy
  have hd : dist x (x-y) < δ := by simpa [dist_eq_norm] using hy
  have hh := hprop hd hx
  change dist (g x) (g (x-y)) < ε at hh
  simpa only [dist_eq_norm, norm_sub_rev] using hh

theorem boundedUniformRecovery : P201Specs.Heat.boundedUniformRecoveryStatement := by
  intro n _ g hg hb
  refine ⟨fun _ ht x => bounded_convolution_integrable g hg.continuous hb ht x, ?_⟩
  rw [← tendstoUniformlyOn_univ]
  apply bounded_recovery_on g hg.continuous hb univ
  intro ε hε
  obtain ⟨δ, hδ, hprop⟩ := Metric.uniformContinuous_iff.mp hg ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x _ y hy
  have hd : dist (x-y) x < δ := by simpa [dist_eq_norm] using hy
  simpa only [dist_eq_norm] using hprop hd

end P201.Heat
