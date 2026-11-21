import MathGenome.Internal.FourierSobolev.Specs.P102.U4.WholeSpaceDensity
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionOperations
import MathGenome.Internal.FourierSobolev.P102.U4.LocalConvolution
import MathGenome.Internal.FourierSobolev.P102.U2.ApproximateIdentities
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

import MathGenome.Internal.FourierSobolev.P102.U4.DistributionConvolution
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions ENNReal Topology Pointwise
namespace P102.U4

/-- Smoothness of the pointwise regularization on all of Euclidean space. -/
theorem localConvolution_contDiff {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (ρ : WholeTests d 𝕜) :
    ContDiff ℝ (⊤ : ℕ∞) (localConvolution T ρ) := by
  have h := localConvolution_smooth d 𝕜 ⊤ T ρ
  rw [convolutionDomain_top, contDiffOn_univ] at h
  exact h

/-- No representative choices enter the exact Sobolev error norm. -/
theorem sobolevSumError_eq_norm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : Sobolev 𝕜 (⊤ : Opens (Space d)) m p) :
    sobolevSumError u v = ‖u - v‖ := by
  rw [sobolev_norm]
  rfl

/-- All coordinate derivatives of a test are actual compactly supported smooth tests. -/
theorem test_multiPartial_memLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) (φ : WholeTests d 𝕜) (α : MultiIndex d) :
    MemLp (multiPartial φ α) p volume := by
  have h := (testPartialWord ⊤ (α.sort (· ≤ ·)) φ).continuous.memLp_of_hasCompactSupport
    (μ := volume) (p := p) (testPartialWord ⊤ (α.sort (· ≤ ·)) φ).hasCompactSupport
  rwa [testPartialWord_coe] at h

/-- Tests embed into the existing derivative-tuple Sobolev space. -/
theorem smoothTest_hasSobolevRepresentative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : WholeTests d 𝕜) :
    ∃ u : Sobolev 𝕜 (⊤ : Opens (Space d)) m p, RepresentsSobolev φ u := by
  let f : DomainLp 𝕜 (⊤ : Opens (Space d)) p :=
    (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ
  have hf : (f : Space d → 𝕜) =ᵐ[volume] φ := by
    simpa using (φ.continuous.memLp_of_hasCompactSupport
      (μ := volume.restrict ((⊤ : Opens (Space d)) : Set (Space d))) (p := p)
      φ.hasCompactSupport).coeFn_toLp
  have hr : regularDistribution ⊤ f = regularDistribution ⊤ φ := by
    apply (regular_injectivity d 𝕜 ⊤ f φ (domainLp_locallyIntegrable ⊤ p f)
      (φ.continuous.continuousOn.locallyIntegrableOn isOpen_univ.measurableSet)).mpr
    simpa using hf
  have hmem : HasSobolevDerivatives ⊤ m p f := by
    intro α _
    have hv : MemLp (multiPartial φ α) p
        (volume.restrict ((⊤ : Opens (Space d)) : Set (Space d))) := by
      simpa using test_multiPartial_memLp p φ α
    refine ⟨hv.toLp (multiPartial φ α), ?_⟩
    rw [hr, derivative_classicalCompatibility d 𝕜 ⊤ α φ
      (φ.contDiff.of_le (by simp)).contDiffOn]
    apply (regular_injectivity d 𝕜 ⊤ _ _
      ((partialWord_contDiff φ.contDiff _).continuous.continuousOn.locallyIntegrableOn
        isOpen_univ.measurableSet)
      (domainLp_locallyIntegrable ⊤ p _)).mpr
    exact hv.coeFn_toLp.symm
  obtain ⟨u, hu⟩ := (Set.ext_iff.mp (sobolev_range (𝕜 := 𝕜) ⊤ m p) f).mpr hmem
  refine ⟨u, fun α => ?_⟩
  have hdist := sobolev_derivative_distribution ⊤ m p u α
  rw [hu, hr, derivative_classicalCompatibility d 𝕜 ⊤ α.val φ
    (φ.contDiff.of_le (by simp)).contDiffOn] at hdist
  have he := (regular_injectivity d 𝕜 ⊤ _ _
    ((partialWord_contDiff φ.contDiff _).continuous.continuousOn.locallyIntegrableOn
      isOpen_univ.measurableSet)
    (domainLp_locallyIntegrable ⊤ p (sobolevDerivative u α))).mp hdist
  simpa [multiPartial] using he.symm

/-- Conditional draft: the ordered premises are the frozen upstream contract. -/
theorem wholeSpace_smoothTests_conditional
    (_hConvolution : DistributionConvolutionExpected.Convolution)
    (_hConstruction : DistributionConvolutionExpected.Construction)
    (_hExtension : DistributionConvolutionExpected.ExtensionPairing)
    (_hOperator : DistributionConvolutionExpected.InnerOperator)
    (_hInner : DistributionConvolutionExpected.InnerTest)
    (_hRegular : DistributionConvolutionExpected.RegularInner) :
    WholeSpaceDensityExpected.SmoothTests := by
  intro d 𝕜 _ m p _ φ
  exact smoothTest_hasSobolevRepresentative m p φ

/-- Distributional differentiation of regularization becomes ordinary
pointwise differentiation of its smooth representative. -/
theorem localConvolution_distributionPartial
    (hConvolution : DistributionConvolutionExpected.Convolution)
    {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (ρ : WholeTests d 𝕜)
    (α : MultiIndex d) :
    multiPartial (localConvolution T ρ) α =
      localConvolution (distributionPartial α T) ρ := by
  obtain ⟨C, _hpair, _hsupport, hder, hreg, _hfun⟩ := hConvolution d 𝕜
  obtain ⟨hρ, hT⟩ := hreg T ρ
  obtain ⟨hρ', hT'⟩ := hreg (distributionPartial α T) ρ
  have he : regularDistribution ⊤ (multiPartial (localConvolution T ρ) α) =
      regularDistribution ⊤ (localConvolution (distributionPartial α T) ρ) := by
    rw [← derivative_classicalCompatibility d 𝕜 ⊤ α _
      ((localConvolution_contDiff T ρ).of_le (by simp)).contDiffOn,
      ← hT, (hder T _ hρ α).2, hT']
  have hl := partialWord_contDiff (localConvolution_contDiff T ρ) (α.sort (· ≤ ·))
  have hr := localConvolution_contDiff (distributionPartial α T) ρ
  apply MeasureTheory.Measure.eq_of_ae_eq (μ := volume) _ hl.continuous hr.continuous
  have hae := (regular_injectivity d 𝕜 ⊤ _ _
    (hl.continuous.continuousOn.locallyIntegrableOn isOpen_univ.measurableSet)
    (hr.continuous.continuousOn.locallyIntegrableOn isOpen_univ.measurableSet)).mp he
  simpa using hae

/-- Conditional draft of the full weak-derivative commutation statement. -/
theorem wholeSpace_weakMollification_conditional
    (hConvolution : DistributionConvolutionExpected.Convolution)
    (_hConstruction : DistributionConvolutionExpected.Construction)
    (_hExtension : DistributionConvolutionExpected.ExtensionPairing)
    (_hOperator : DistributionConvolutionExpected.InnerOperator)
    (_hInner : DistributionConvolutionExpected.InnerTest)
    (_hRegular : DistributionConvolutionExpected.RegularInner) :
    WholeSpaceDensityExpected.WeakMollification := by
  intro d 𝕜 _ m p _ u ρ α
  rw [localConvolution_distributionPartial hConvolution,
    sobolev_derivative_distribution ⊤ m p u α]

/-- Positive radii are used only for ε>0; the extension at other parameters is harmless. -/
def sobolevMollifierBump (d : ℕ) (ε : ℝ) : ContDiffBump (0 : Space d) := by
  by_cases hε : 0 < ε
  · exact ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  · exact ⟨1, 2, by norm_num, by norm_num⟩

/-- Normalized bump construction works also on the zero-dimensional Haar space. -/
def sobolevMollifierKernel (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (ε : ℝ) : WholeTests d 𝕜 :=
  TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜)
    ⟨(sobolevMollifierBump d ε).normed volume,
      (sobolevMollifierBump d ε).contDiff_normed,
      (sobolevMollifierBump d ε).hasCompactSupport_normed, subset_univ _⟩

theorem sobolevMollifierKernel_support (d : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (ε : ℝ) (hε : 0 < ε) :
    tsupport (sobolevMollifierKernel d 𝕜 ε) ⊆ Metric.closedBall 0 ε := by
  change tsupport (fun x => ((sobolevMollifierBump d ε).normed volume x : 𝕜)) ⊆ _
  apply (tsupport_comp_subset (g := fun t : ℝ => (t : 𝕜)) (by simp) _).trans
  rw [(sobolevMollifierBump d ε).tsupport_normed_eq]
  simp [sobolevMollifierBump, hε]

theorem sobolevMollifierKernel_conditions (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    IsSobolevMollifier (sobolevMollifierKernel d 𝕜) := by
  have hnorm (ε : ℝ) (x : Space d) : ‖sobolevMollifierKernel d 𝕜 ε x‖ =
      (sobolevMollifierBump d ε).normed volume x := by
    change ‖((sobolevMollifierBump d ε).normed volume x : 𝕜)‖ = _
    rw [RCLike.norm_ofReal, abs_of_nonneg (ContDiffBump.nonneg_normed _ _)]
  have hi (ε : ℝ) : ∫ x, sobolevMollifierKernel d 𝕜 ε x = (1 : 𝕜) := by
    change (∫ x, ((sobolevMollifierBump d ε).normed volume x : 𝕜)) = 1
    rw [integral_ofReal, ContDiffBump.integral_normed, RCLike.ofReal_one]
  refine ⟨⟨fun ε _ => (sobolevMollifierKernel d 𝕜 ε).continuous.integrable_of_hasCompactSupport
    (sobolevMollifierKernel d 𝕜 ε).hasCompactSupport,
    fun ε _ => hi ε, ⟨1, zero_le_one, fun ε _ => ?_⟩, ?_⟩,
    sobolevMollifierKernel_support d 𝕜⟩
  · simp_rw [hnorm]
    exact le_of_eq (ContDiffBump.integral_normed _)
  · intro δ hδ
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < δ from
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0) (gt_mem_nhds hδ))] with ε hε hεδ
    symm
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hxout : x ∉ tsupport (sobolevMollifierKernel d 𝕜 ε) := by
      intro hxmem
      have hxle := sobolevMollifierKernel_support d 𝕜 ε hε hxmem
      exact (not_lt_of_ge hxle) (hεδ.trans hx)
    rw [image_eq_zero_of_notMem_tsupport hxout, norm_zero]

/-- Conditional draft of existence of genuine smooth approximate identities. -/
theorem wholeSpace_mollifierExistence_conditional
    (_hConvolution : DistributionConvolutionExpected.Convolution)
    (_hConstruction : DistributionConvolutionExpected.Construction)
    (_hExtension : DistributionConvolutionExpected.ExtensionPairing)
    (_hOperator : DistributionConvolutionExpected.InnerOperator)
    (_hInner : DistributionConvolutionExpected.InnerTest)
    (_hRegular : DistributionConvolutionExpected.RegularInner) :
    WholeSpaceDensityExpected.MollifierExistence := by
  intro d 𝕜 _
  exact ⟨sobolevMollifierKernel d 𝕜, sobolevMollifierKernel_conditions d 𝕜⟩

/-- Pointwise regularization is the ordinary integral with the source's orientation. -/
theorem localConvolution_regular_whole {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : LocallyIntegrable f volume) (ρ : WholeTests d 𝕜) :
    localConvolution (regularDistribution ⊤ f) ρ =
      P102.U2.Young.integralConvolution volume ρ f := by
  funext x
  rw [localConvolution_regularIntegral d 𝕜 ⊤ f (by simpa only [Opens.coe_top, locallyIntegrableOn_univ] using hf) ρ x
    (by rw [convolutionDomain_top]; trivial)]
  simp only [Opens.coe_top, Measure.restrict_univ, P102.U2.Young.integralConvolution]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => mul_comm _ _

/-- Essential support is sufficient: null-set changes of the input do not affect
any pointwise regularization. Its support lies in the compact sum. -/
theorem localConvolution_hasCompactSupport {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : LocallyIntegrable f volume)
    (hfc : HasCompactEssentialSupport f) (ρ : WholeTests d 𝕜) :
    HasCompactSupport (localConvolution (regularDistribution ⊤ f) ρ) := by
  obtain ⟨K, hK⟩ := hfc
  have hs : Function.support (localConvolution (regularDistribution ⊤ f) ρ) ⊆
      (K : Set (Space d)) + tsupport ρ := by
    intro x hx
    by_contra hxsum
    apply hx
    rw [localConvolution_regular_whole hf]
    apply integral_eq_zero_of_ae
    filter_upwards [hK] with y hy
    by_cases hyK : y ∈ K
    · have hz : ρ (x - y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hz
        apply hxsum
        exact ⟨y, hyK, x - y, hz, by abel_nf⟩
      simp [hz]
    · simp [hy hyK]
  exact (K.isCompact.add ρ.hasCompactSupport).of_isClosed_subset isClosed_closure
    (closure_minimal hs (K.isCompact.add ρ.hasCompactSupport).isClosed)

/-- The restricted whole-space Lp norm is the ordinary volume Lp norm. -/
theorem wholeLp_norm_sub {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u v : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    ‖u - v‖ = (eLpNorm (fun x => u x - v x) p volume).toReal := by
  rw [Lp.norm_def]
  congr 1
  have h : (u - v : DomainLp 𝕜 (⊤ : Opens (Space d)) p) =ᵐ[volume]
      fun x => u x - v x := by
    have h := Lp.coeFn_sub u v
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    exact h
  simpa using eLpNorm_congr_ae h

/-- Coordinatewise approximate-identity convergence with the pointwise regularization
on the left; the proof is valid in dimension zero as well. -/
theorem localConvolution_lp_tendsto {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (ρ : ℝ → WholeTests d 𝕜) (hρ : IsSobolevMollifier ρ)
    (f : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    Tendsto (fun ε => eLpNorm (fun x =>
      localConvolution (regularDistribution ⊤ f) (ρ ε) x - f x) p volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hf : MemLp (f : Space d → 𝕜) p volume := by simpa using Lp.memLp f
  have hfli : LocallyIntegrable (f : Space d → 𝕜) volume := hf.locallyIntegrable Fact.out
  simpa only [localConvolution_regular_whole hfli, P102.U2.Young.integralConvolution] using
    (P102.U2.ApproximateIdentities.lp_recovery volume (fun ε => (ρ ε : Space d → 𝕜))
      hρ.1 p Fact.out hp f hf).2

/-- Conditional draft of compactly supported Sobolev mollification, including
membership, support, all weak derivatives, and convergence in the exact sum norm. -/
theorem wholeSpace_mollification_conditional
    (hConvolution : DistributionConvolutionExpected.Convolution)
    (hConstruction : DistributionConvolutionExpected.Construction)
    (hExtension : DistributionConvolutionExpected.ExtensionPairing)
    (hOperator : DistributionConvolutionExpected.InnerOperator)
    (hInner : DistributionConvolutionExpected.InnerTest)
    (hRegular : DistributionConvolutionExpected.RegularInner) :
    WholeSpaceDensityExpected.Mollification := by
  intro d 𝕜 _ m p _ hp ρ hρ u hu
  have hfli : LocallyIntegrable (sobolevUnderlying u : Space d → 𝕜) volume := by
    simpa using (Lp.memLp (sobolevUnderlying u)).locallyIntegrable (Fact.out : 1 ≤ p)
  let φ (ε : ℝ) : WholeTests d 𝕜 :=
    ⟨localConvolution (regularDistribution ⊤ (sobolevUnderlying u)) (ρ ε),
      localConvolution_contDiff _ _, localConvolution_hasCompactSupport hfli hu _, subset_univ _⟩
  choose v hv using fun ε => smoothTest_hasSobolevRepresentative m p (φ ε)
  have hder (ε : ℝ) (α : SobolevIndex d m) :
      (sobolevDerivative (v ε) α : Space d → 𝕜) =ᵐ[volume]
        localConvolution (regularDistribution ⊤ (sobolevDerivative u α)) (ρ ε) := by
    have h := hv ε α
    change (sobolevDerivative (v ε) α : Space d → 𝕜) =ᵐ[volume]
      multiPartial (localConvolution (regularDistribution ⊤ (sobolevUnderlying u)) (ρ ε)) α.val at h
    rwa [wholeSpace_weakMollification_conditional hConvolution hConstruction hExtension
      hOperator hInner hRegular m p u (ρ ε) α] at h
  have ht (α : SobolevIndex d m) :
      Tendsto (fun ε => ‖sobolevDerivative (v ε) α - sobolevDerivative u α‖)
        (𝓝[>] 0) (𝓝 0) := by
    have he := localConvolution_lp_tendsto hp ρ hρ (sobolevDerivative u α)
    have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
    simp only [ENNReal.toReal_zero] at hr
    apply hr.congr'
    exact Eventually.of_forall fun ε => by
      dsimp only [Function.comp_apply]
      rw [wholeLp_norm_sub]
      congr 1
      exact eLpNorm_congr_ae ((hder ε α).sub EventuallyEq.rfl).symm
  refine ⟨v, fun ε _ => ⟨localConvolution_contDiff _ _,
    localConvolution_hasCompactSupport hfli hu _, hv ε, hder ε⟩, ht, ?_⟩
  simpa only [sobolevSumError, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun α _ => ht α)

/-- A fixed cutoff of the kind used in the manuscript exists in every dimension. -/
theorem exists_unitSobolevCutoff (d : ℕ) :
    ∃ χ : WholeTests d ℝ, (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀ x ∈ Metric.closedBall (0 : Space d) 1, χ x = 1 := by
  let b : ContDiffBump (0 : Space d) := ⟨1, 2, by norm_num, by norm_num⟩
  exact ⟨⟨b, b.contDiff, b.hasCompactSupport, subset_univ _⟩,
    fun x => ⟨b.nonneg, b.le_one⟩, fun x hx => b.one_of_mem_closedBall hx⟩

/-- Analytic reduction of sequential density to the cutoff-convergence statement.
This intermediate lemma separates the cutoff estimate from the final
sequence selection; the cutoff estimate is proved below before the final helper. -/
theorem wholeSpace_density_of_cutoff
    (hConvolution : DistributionConvolutionExpected.Convolution)
    (hConstruction : DistributionConvolutionExpected.Construction)
    (hExtension : DistributionConvolutionExpected.ExtensionPairing)
    (hOperator : DistributionConvolutionExpected.InnerOperator)
    (hInner : DistributionConvolutionExpected.InnerTest)
    (hRegular : DistributionConvolutionExpected.RegularInner)
    (hCutoff : WholeSpaceDensityExpected.Cutoff) : WholeSpaceDensityExpected.Density := by
  intro d 𝕜 _ m p _ hp u
  obtain ⟨χ, hχ, hχone⟩ := exists_unitSobolevCutoff d
  obtain ⟨v, _hvgraph, hvcompact, hvconv⟩ := hCutoff m p hp χ hχ hχone u
  let ρ := sobolevMollifierKernel d 𝕜
  have hρ := sobolevMollifierKernel_conditions d 𝕜
  have hmoll := wholeSpace_mollification_conditional hConvolution hConstruction hExtension
    hOperator hInner hRegular m p hp ρ hρ
  choose w hw using fun n => hmoll (v n) (hvcompact n)
  have hchoose (n : ℕ) : ∃ ε : ℝ, 0 < ε ∧
      sobolevSumError (w n ε) (v n) < ((n + 1 : ℕ) : ℝ)⁻¹ := by
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hsmall := (tendsto_order.mp (hw n).2.2).2 _ hpos
    have hboth := hsmall.and self_mem_nhdsWithin
    obtain ⟨ε, hε, hεpos⟩ := hboth.exists
    exact ⟨ε, hεpos, hε⟩
  choose ε hεpos hεsmall using hchoose
  let φ (n : ℕ) : WholeTests d 𝕜 :=
    ⟨localConvolution (regularDistribution ⊤ (sobolevUnderlying (v n))) (ρ (ε n)),
      ((hw n).1 (ε n) (hεpos n)).1,
      ((hw n).1 (ε n) (hεpos n)).2.1, subset_univ _⟩
  have heconv : Tendsto (fun n => sobolevSumError (w n (ε n)) u) atTop (𝓝 0) := by
    have hbound (n : ℕ) : sobolevSumError (w n (ε n)) u ≤
        ((n + 1 : ℕ) : ℝ)⁻¹ + sobolevSumError (v n) u := by
      simp only [sobolevSumError_eq_norm] at *
      calc
        ‖w n (ε n) - u‖ ≤ ‖w n (ε n) - v n‖ + ‖v n - u‖ := by simpa only [dist_eq_norm] using dist_triangle (w n (ε n)) (v n) u
        _ ≤ _ := by gcongr; exact (hεsmall n).le
    have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hupper := hinv.add hvconv
    simp only [zero_add] at hupper
    exact squeeze_zero (fun n => by rw [sobolevSumError_eq_norm]; positivity) hbound hupper
  refine ⟨φ, fun n => w n (ε n), fun n => ((hw n).1 (ε n) (hεpos n)).2.2.1, ?_, heconv⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sobolevSumError_eq_norm] using heconv

/-- Multiplication of an Lp class by an actual smooth compactly supported test. -/
def testMulLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (f : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    DomainLp 𝕜 (⊤ : Opens (Space d)) p :=
  ((a.continuous.memLp_of_hasCompactSupport (p := ⊤) a.hasCompactSupport).mul
    (Lp.memLp f) : MemLp _ p _).toLp (fun x => a x * f x)

theorem testMulLp_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (f : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    (testMulLp a f : Space d → 𝕜) =ᵐ[volume] fun x => a x * f x := by
  have h := ((a.continuous.memLp_of_hasCompactSupport (p := ⊤) a.hasCompactSupport).mul
    (Lp.memLp f) : MemLp _ p _).coeFn_toLp
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  exact h

/-- A test regarded as a globally smooth coefficient. -/
def testCoefficient {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (a : WholeTests d 𝕜) :
    SmoothCoefficient 𝕜 (⊤ : Opens (Space d)) := ⟨a, a.contDiff.contDiffOn⟩

theorem regularLp_testMul {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (f : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    regularDistribution ⊤ (testMulLp a f) =
      distributionMultiplier (testCoefficient a) (regularDistribution ⊤ f) := by
  ext ψ
  rw [distributionMultiplier_apply, regular_pairing d 𝕜 ⊤ _
    (domainLp_locallyIntegrable ⊤ p _), regular_pairing d 𝕜 ⊤ _
    (domainLp_locallyIntegrable ⊤ p _)]
  simp only [Opens.coe_top, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [testMulLp_ae a f] with x hx
  change testMulLp a f x * ψ x = f x * (a x * ψ x)
  rw [hx]
  ring

theorem regularLp_add {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f g : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    regularDistribution ⊤ (f + g) = regularDistribution ⊤ f + regularDistribution ⊤ g := by
  ext ψ
  simp only [regularLp_pairing ⊤ p, ContinuousLinearMap.map_add, add_apply]

/-- A recursive Leibniz sum of Lp classes; repeated directions keep their
binomial multiplicities. This is a construction, not an assumed product rule. -/
def sobolevWordProduct {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (F : MultiIndex d → DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    List (Fin d) → WholeTests d 𝕜 → MultiIndex d → DomainLp 𝕜 (⊤ : Opens (Space d)) p
  | [], a, β => testMulLp a (F β)
  | i :: l, a, β => sobolevWordProduct F l (testPartialWord ⊤ [i] a) β +
      sobolevWordProduct F l a ({i} + β)

/-- The above Lp sum represents the distributional iterated Leibniz expansion. -/
theorem sobolevWordProduct_distribution {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (m : ℕ)
    (F : MultiIndex d → DomainLp 𝕜 (⊤ : Opens (Space d)) p)
    (T : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hF : ∀ β : MultiIndex d, β.card ≤ m →
      regularDistribution ⊤ (F β) = distributionPartial β T)
    (l : List (Fin d)) (a : WholeTests d 𝕜) (β : MultiIndex d)
    (hbound : l.length + β.card ≤ m) :
    regularDistribution ⊤ (sobolevWordProduct F l a β) =
      leibnizExpansion testMultiplier l (testCoefficient a) (distributionPartial β T) := by
  induction l generalizing a β with
  | nil =>
    rw [sobolevWordProduct, regularLp_testMul, hF β (by simpa using hbound)]
    rfl
  | cons i l ih =>
    have hcoef : testCoefficient (testPartialWord ⊤ [i] a) =
        coefficientPartial i (testCoefficient a) := by
      apply Subtype.ext
      exact testPartialWord_coe ⊤ [i] a
    rw [sobolevWordProduct, regularLp_add, ih _ β (by simp only [List.length_cons] at hbound; omega),
      ih a ({i} + β) (by simp only [List.length_cons, Multiset.card_add,
        Multiset.card_singleton] at *; omega), hcoef]
    rw [leibnizExpansion, derivative_add]

/-- General membership under multiplication by a smooth test. This supplies the
weak-product construction needed before estimating a dilated cutoff. -/
theorem sobolev_testMul {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) m p) (a : WholeTests d 𝕜) :
    ∃ v : Sobolev 𝕜 (⊤ : Opens (Space d)) m p,
      sobolevUnderlying v = testMulLp a (sobolevUnderlying u) := by
  classical
  let F : MultiIndex d → DomainLp 𝕜 (⊤ : Opens (Space d)) p := fun β =>
    if h : β.card ≤ m then sobolevDerivative u ⟨β, h⟩ else 0
  have hF (β : MultiIndex d) (hβ : β.card ≤ m) :
      regularDistribution ⊤ (F β) =
        distributionPartial β (regularDistribution ⊤ (sobolevUnderlying u)) := by
    simpa only [F, dite_eq_left hβ] using (sobolev_derivative_distribution ⊤ m p u ⟨β, hβ⟩).symm
  apply (Set.ext_iff.mp (sobolev_range (𝕜 := 𝕜) ⊤ m p) _).mpr
  intro α hα
  refine ⟨sobolevWordProduct F (α.sort (· ≤ ·)) a 0, ?_⟩
  rw [regularLp_testMul, distributionMultiplier_iteratedProductRule,
    sobolevWordProduct_distribution m F _ hF _ a 0 (by simpa using hα), derivative_zero]

/-- Dominated convergence in each finite Lp seminorm. -/
theorem eLpNorm_tendsto_zero_of_dominated {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hptop : p ≠ ⊤) {f : ℕ → X → E} {g : X → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖g x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) p μ) atTop (𝓝 0) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hi := tendsto_lintegral_of_dominated_convergence'
    (fun x => ‖g x‖ₑ ^ p.toReal)
    (fun n => (hf n).enorm.pow_const p.toReal)
    (fun n => (hbound n).mono fun x hx => ENNReal.rpow_le_rpow
      (enorm_le_iff_norm_le.mpr hx) hp.le)
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop hg.eLpNorm_lt_top).ne
    (hlim.mono fun x hx => by
      have he := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto (0 : ℝ≥0∞)
      have hn : Tendsto (fun n => ‖f n x‖ₑ) atTop (𝓝 0) := by
        simpa only [enorm_zero] using hx.enorm
      simpa only [Function.comp_def, enorm_zero, ENNReal.zero_rpow_of_pos hp] using he.comp hn)
  simp only [lintegral_zero] at hi
  have ho := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto (0 : ℝ≥0∞)
  have ht := ho.comp hi
  simpa only [Function.comp_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (hf _),
    ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)] using ht

/-- Uniformly bounded smooth multipliers converging pointwise to a constant
converge strongly on Lp, for finite p. -/
theorem testMulLp_tendsto {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (a : ℕ → WholeTests d 𝕜) (c : 𝕜)
    (hbound : ∃ C : ℝ, ∀ n x, ‖a n x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => a n x) atTop (𝓝 c))
    (f : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    Tendsto (fun n => testMulLp (a n) f) atTop (𝓝 (c • f)) := by
  obtain ⟨C, hC⟩ := hbound
  have hC0 : 0 ≤ C := (norm_nonneg (a 0 0)).trans (hC 0 0)
  have hf : MemLp (f : Space d → 𝕜) p volume := by simpa using Lp.memLp f
  have hh (n : ℕ) : AEStronglyMeasurable (fun x => (a n x - c) * f x) volume :=
    ((a n).continuous.aestronglyMeasurable.sub aestronglyMeasurable_const).mul
      hf.aestronglyMeasurable
  have he := eLpNorm_tendsto_zero_of_dominated
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp hh
    (hf.const_smul (C + ‖c‖))
    (fun n => Eventually.of_forall fun x => by
      change ‖(a n x - c) * f x‖ ≤ ‖(C + ‖c‖) • f x‖
      rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ C + ‖c‖)]
      exact mul_le_mul_of_nonneg_right ((norm_sub_le (a n x) c).trans
        (add_le_add (hC n x) le_rfl)) (norm_nonneg _))
    (Eventually.of_forall fun x => by
      simpa using ((hlim x).sub_const c).mul_const (f x))
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
  simp only [ENNReal.toReal_zero] at hr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply hr.congr'
  exact Eventually.of_forall fun n => by
    dsimp only [Function.comp_apply]
    rw [wholeLp_norm_sub]
    congr 1
    apply eLpNorm_congr_ae
    have hc : (c • f : DomainLp 𝕜 (⊤ : Opens (Space d)) p) =ᵐ[volume]
        fun x => c * f x := by
      have h := Lp.coeFn_smul c f
      simp only [Opens.coe_top, Measure.restrict_univ] at h
      exact h
    filter_upwards [testMulLp_ae (a n) f, hc] with x hx hcx
    rw [hx, hcx]
    ring

/-- Coordinate words obey the usual dilation chain rule, including the empty word. -/
theorem partialWord_dilate {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (c : ℝ) (l : List (Fin d)) :
    partialWord (fun x => f (c • x)) l = fun x => c ^ l.length • partialWord f l (c • x) := by
  induction l with
  | nil => simp [partialWord]
  | cons i l ih =>
    ext x
    change fderiv ℝ (partialWord (fun x => f (c • x)) l) x (coordinateVector d i) = _
    rw [ih]
    have hd := ((partialWord_contDiff hf l).differentiable (by simp) (c • x)).hasFDerivAt
    have hc := (hd.comp x ((hasFDerivAt_id x).const_smul c)).const_smul (c ^ l.length)
    have heq : fderiv ℝ (fun x => c ^ l.length • partialWord f l (c • x)) x =
        (c ^ l.length) • (fderiv ℝ (partialWord f l) (c • x)).comp
          (c • ContinuousLinearMap.id ℝ (Space d)) := hc.fderiv
    rw [heq]
    simp [partialWord, pow_succ, smul_smul]

/-- Dilation by 1/(n+1) preserves the test space. -/
def dilatedCutoff {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (χ : WholeTests d 𝕜)
    (n : ℕ) : WholeTests d 𝕜 where
  toFun x := χ (((n + 1 : ℕ) : ℝ)⁻¹ • x)
  contDiff' := χ.contDiff.comp (contDiff_id.const_smul _)
  hasCompactSupport' := χ.hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity))
  tsupport_subset' := subset_univ _

/-- Every derivative of a dilated cutoff is uniformly bounded. Its order-zero
limit is the central value; each positive-order derivative tends to zero. -/
theorem dilatedCutoff_word_limits {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (χ : WholeTests d 𝕜) (l : List (Fin d)) :
    (∃ C : ℝ, ∀ n x, ‖testPartialWord ⊤ l (dilatedCutoff χ n) x‖ ≤ C) ∧
    ∀ x, Tendsto (fun n => testPartialWord ⊤ l (dilatedCutoff χ n) x) atTop
      (𝓝 (if l = [] then χ 0 else 0)) := by
  have heq (n : ℕ) (x : Space d) :
      testPartialWord ⊤ l (dilatedCutoff χ n) x =
        (((n + 1 : ℕ) : ℝ)⁻¹) ^ l.length •
          testPartialWord ⊤ l χ (((n + 1 : ℕ) : ℝ)⁻¹ • x) := by
    simp only [testPartialWord_coe]
    exact congrFun (partialWord_dilate χ.contDiff _ l) x
  obtain ⟨C, hC⟩ := (testPartialWord ⊤ l χ).continuous.bounded_above_of_compact_support
    (testPartialWord ⊤ l χ).hasCompactSupport
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨⟨C, fun n x => ?_⟩, fun x => ?_⟩
  · rw [heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹) _)]
    have hle : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    calc
      _ ≤ 1 * ‖testPartialWord ⊤ l χ (((n + 1 : ℕ) : ℝ)⁻¹ • x)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) hle) (norm_nonneg _)
      _ ≤ C := by simpa only [one_mul] using hC (((n + 1 : ℕ) : ℝ)⁻¹ • x)
  · have hx : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ • x) atTop (𝓝 0) := by
      simpa only [zero_smul] using hinv.smul_const x
    have ht := (testPartialWord ⊤ l χ).continuous.continuousAt.tendsto.comp hx
    have hs := (hinv.pow l.length).smul ht
    by_cases hl : l = []
    · subst l
      simpa only [List.length_nil, pow_zero, one_smul, testPartialWord,
        ContinuousLinearMap.id_apply, ite_true] using hs.congr (fun n => (heq n x).symm)
    · have hlen : l.length ≠ 0 := fun hz => hl (List.length_eq_zero_iff.mp hz)
      simpa only [zero_pow hlen, zero_smul, ite_eq_right hl] using
        hs.congr (fun n => (heq n x).symm)

/-- Strong convergence of the recursive Leibniz sum, from bounded convergence
of every coefficient derivative. No derivative is discarded from the expansion. -/
theorem sobolevWordProduct_tendsto {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (F : MultiIndex d → DomainLp 𝕜 (⊤ : Opens (Space d)) p)
    (l : List (Fin d)) (a : ℕ → WholeTests d 𝕜) (c : 𝕜)
    (hb : ∀ k : List (Fin d), ∃ C : ℝ, ∀ n x,
      ‖testPartialWord ⊤ k (a n) x‖ ≤ C)
    (ht : ∀ (k : List (Fin d)) x,
      Tendsto (fun n => testPartialWord ⊤ k (a n) x) atTop
        (𝓝 (if k = [] then c else 0))) (β : MultiIndex d) :
    Tendsto (fun n => sobolevWordProduct F l (a n) β) atTop
      (𝓝 (c • F ((l : Multiset (Fin d)) + β))) := by
  induction l generalizing a c β with
  | nil =>
    simpa only [sobolevWordProduct, Multiset.coe_nil, zero_add] using
      testMulLp_tendsto hp a c (hb []) (by simpa only [ite_true, testPartialWord,
        ContinuousLinearMap.id_apply] using ht []) (F β)
  | cons i l ih =>
    let b : ℕ → WholeTests d 𝕜 := fun n => testPartialWord ⊤ [i] (a n)
    have hb' (k : List (Fin d)) : ∃ C : ℝ, ∀ n x,
        ‖testPartialWord ⊤ k (b n) x‖ ≤ C := by
      simpa only [testPartialWord_append, b] using hb (k ++ [i])
    have ht' (k : List (Fin d)) (x : Space d) :
        Tendsto (fun n => testPartialWord ⊤ k (b n) x) atTop (𝓝 (if k = [] then (0 : 𝕜) else 0)) := by
      simpa only [testPartialWord_append, List.append_eq_nil_iff, List.cons_ne_nil, and_false, ite_false, ite_self, b] using ht (k ++ [i]) x
    have hs := (ih b 0 hb' ht' β).add (ih a c hb ht ({i} + β))
    change Tendsto (fun n => sobolevWordProduct F l (b n) β +
      sobolevWordProduct F l (a n) ({i} + β)) atTop
        (𝓝 (c • F ((i ::ₘ (l : Multiset (Fin d))) + β)))
    simpa only [zero_smul, zero_add, Multiset.cons_add, Multiset.singleton_add,
      Multiset.add_cons] using hs

/-- Conditional draft of smooth-cutoff convergence. The proof constructs the
weak derivative tuple by the iterated product rule, then applies dominated
convergence to every term. No new mathematical premise is added. -/
theorem wholeSpace_cutoff_conditional
    (_hConvolution : DistributionConvolutionExpected.Convolution)
    (_hConstruction : DistributionConvolutionExpected.Construction)
    (_hExtension : DistributionConvolutionExpected.ExtensionPairing)
    (_hOperator : DistributionConvolutionExpected.InnerOperator)
    (_hInner : DistributionConvolutionExpected.InnerTest)
    (_hRegular : DistributionConvolutionExpected.RegularInner) :
    WholeSpaceDensityExpected.Cutoff := by
  intro d 𝕜 _ m p _ hp χ _hχ hχone u
  classical
  let a : WholeTests d 𝕜 := TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) χ
  have ha0 : a (0 : Space d) = 1 := by
    change (χ (0 : Space d) : 𝕜) = 1
    rw [hχone 0 (by simp)]
    simp
  let A : ℕ → WholeTests d 𝕜 := dilatedCutoff a
  choose v hv using fun n => sobolev_testMul m p u (A n)
  let F : MultiIndex d → DomainLp 𝕜 (⊤ : Opens (Space d)) p := fun β =>
    if h : β.card ≤ m then sobolevDerivative u ⟨β, h⟩ else 0
  have hF (β : MultiIndex d) (hβ : β.card ≤ m) :
      regularDistribution ⊤ (F β) =
        distributionPartial β (regularDistribution ⊤ (sobolevUnderlying u)) := by
    simpa only [F, dite_eq_left hβ] using
      (sobolev_derivative_distribution ⊤ m p u ⟨β, hβ⟩).symm
  have hder (n : ℕ) (α : SobolevIndex d m) :
      sobolevDerivative (v n) α = sobolevWordProduct F (α.val.sort (· ≤ ·)) (A n) 0 := by
    apply (sobolev_derivative_unique ⊤ m p (v n) α _ ?_).symm
    rw [hv n, regularLp_testMul, distributionMultiplier_iteratedProductRule,
      sobolevWordProduct_distribution m F _ hF _ (A n) 0 (by simpa using α.property),
      derivative_zero]
  have ht (α : SobolevIndex d m) :
      Tendsto (fun n => sobolevDerivative (v n) α) atTop (𝓝 (sobolevDerivative u α)) := by
    have hb (l : List (Fin d)) := (dilatedCutoff_word_limits a l).1
    have hl (l : List (Fin d)) (x : Space d) :
        Tendsto (fun n => testPartialWord ⊤ l (A n) x) atTop
          (𝓝 (if l = [] then (1 : 𝕜) else 0)) := by
      simpa only [ha0] using (dilatedCutoff_word_limits a l).2 x
    have hw := sobolevWordProduct_tendsto hp F (α.val.sort (· ≤ ·)) A 1 hb hl 0
    have he : F (((α.val.sort (· ≤ ·)) : Multiset (Fin d)) + 0) = sobolevDerivative u α := by
      simp only [add_zero, Multiset.sort_eq, F, dite_eq_left α.property]
      rfl
    rw [one_smul, he] at hw
    exact hw.congr fun n => (hder n α).symm
  refine ⟨v, fun n => ?_, fun n => ?_, ?_⟩
  · rw [hv n]
    exact testMulLp_ae (A n) (sobolevUnderlying u)
  · refine ⟨⟨tsupport (A n), (A n).hasCompactSupport⟩, ?_⟩
    rw [hv n]
    filter_upwards [testMulLp_ae (A n) (sobolevUnderlying u)] with x hx
    intro hxout
    rw [hx, image_eq_zero_of_notMem_tsupport hxout, zero_mul]
  · have hn (α : SobolevIndex d m) :
        Tendsto (fun n => ‖sobolevDerivative (v n) α - sobolevDerivative u α‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using ((ht α).sub_const (sobolevDerivative u α)).norm
    simpa only [sobolevSumError, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun α _ => hn α)

/-- Conditional whole-space density in the exact sum norm. All six frozen
premises occur in their required order; no original closed target is defined. -/
theorem wholeSpace_density_conditional
    (hConvolution : DistributionConvolutionExpected.Convolution)
    (hConstruction : DistributionConvolutionExpected.Construction)
    (hExtension : DistributionConvolutionExpected.ExtensionPairing)
    (hOperator : DistributionConvolutionExpected.InnerOperator)
    (hInner : DistributionConvolutionExpected.InnerTest)
    (hRegular : DistributionConvolutionExpected.RegularInner) :
    WholeSpaceDensityExpected.Density :=
  wholeSpace_density_of_cutoff hConvolution hConstruction hExtension hOperator hInner hRegular
    (wholeSpace_cutoff_conditional hConvolution hConstruction hExtension hOperator hInner hRegular)

end P102.U4

theorem _root_.«P102».«U4».«wholeSpace_cutoff» : _root_.«P102».«U4».«WholeSpaceDensityExpected».«Cutoff» :=
  @_root_.«P102».«U4».«wholeSpace_cutoff_conditional» (@_root_.«P102».«U4».«distributionConvolution») (@_root_.«P102».«U4».«distributionConvolution_construction») (@_root_.«P102».«U4».«distributionConvolution_extensionPairing») (@_root_.«P102».«U4».«distributionConvolution_innerOperator») (@_root_.«P102».«U4».«distributionConvolution_innerTest») (@_root_.«P102».«U4».«distributionConvolution_regularInner»)
theorem _root_.«P102».«U4».«wholeSpace_density» : _root_.«P102».«U4».«WholeSpaceDensityExpected».«Density» :=
  @_root_.«P102».«U4».«wholeSpace_density_conditional» (@_root_.«P102».«U4».«distributionConvolution») (@_root_.«P102».«U4».«distributionConvolution_construction») (@_root_.«P102».«U4».«distributionConvolution_extensionPairing») (@_root_.«P102».«U4».«distributionConvolution_innerOperator») (@_root_.«P102».«U4».«distributionConvolution_innerTest») (@_root_.«P102».«U4».«distributionConvolution_regularInner»)
theorem _root_.«P102».«U4».«wholeSpace_mollification» : _root_.«P102».«U4».«WholeSpaceDensityExpected».«Mollification» :=
  @_root_.«P102».«U4».«wholeSpace_mollification_conditional» (@_root_.«P102».«U4».«distributionConvolution») (@_root_.«P102».«U4».«distributionConvolution_construction») (@_root_.«P102».«U4».«distributionConvolution_extensionPairing») (@_root_.«P102».«U4».«distributionConvolution_innerOperator») (@_root_.«P102».«U4».«distributionConvolution_innerTest») (@_root_.«P102».«U4».«distributionConvolution_regularInner»)
theorem _root_.«P102».«U4».«wholeSpace_mollifierExistence» : _root_.«P102».«U4».«WholeSpaceDensityExpected».«MollifierExistence» :=
  @_root_.«P102».«U4».«wholeSpace_mollifierExistence_conditional» (@_root_.«P102».«U4».«distributionConvolution») (@_root_.«P102».«U4».«distributionConvolution_construction») (@_root_.«P102».«U4».«distributionConvolution_extensionPairing») (@_root_.«P102».«U4».«distributionConvolution_innerOperator») (@_root_.«P102».«U4».«distributionConvolution_innerTest») (@_root_.«P102».«U4».«distributionConvolution_regularInner»)
theorem _root_.«P102».«U4».«wholeSpace_smoothTests» : _root_.«P102».«U4».«WholeSpaceDensityExpected».«SmoothTests» :=
  @_root_.«P102».«U4».«wholeSpace_smoothTests_conditional» (@_root_.«P102».«U4».«distributionConvolution») (@_root_.«P102».«U4».«distributionConvolution_construction») (@_root_.«P102».«U4».«distributionConvolution_extensionPairing») (@_root_.«P102».«U4».«distributionConvolution_innerOperator») (@_root_.«P102».«U4».«distributionConvolution_innerTest») (@_root_.«P102».«U4».«distributionConvolution_regularInner»)
theorem _root_.«P102».«U4».«wholeSpace_weakMollification» : _root_.«P102».«U4».«WholeSpaceDensityExpected».«WeakMollification» :=
  @_root_.«P102».«U4».«wholeSpace_weakMollification_conditional» (@_root_.«P102».«U4».«distributionConvolution») (@_root_.«P102».«U4».«distributionConvolution_construction») (@_root_.«P102».«U4».«distributionConvolution_extensionPairing») (@_root_.«P102».«U4».«distributionConvolution_innerOperator») (@_root_.«P102».«U4».«distributionConvolution_innerTest») (@_root_.«P102».«U4».«distributionConvolution_regularInner»)
