import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DistributionMollification
import MathGenome.Internal.FourierSobolev.P102.U4.LocalConvolution
import MathGenome.Internal.FourierSobolev.P102.U2.ApproximateIdentities
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions Topology Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace P102.U4.Mollification

abbrev scaled : Expected.ScaledKernelType := @scaledKernel
abbrev reflected : Expected.ReflectedKernelType := @reflectedKernel
abbrev smoothTestFunction : Expected.ReflectedSmoothingType := @reflectedSmoothing

@[simp] theorem scaledKernel_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) {ε : ℝ} (hε : ε ≠ 0) (x : Space d) :
    scaledKernel ρ ε x = (ε ^ d)⁻¹ • ρ (ε⁻¹ • x) := by
  simp only [scaledKernel, dite_eq_right hε]
  rfl

theorem scalingFormula : Expected.ScalingFormula := by
  intro d 𝕜 _ ρ ε hε x
  exact scaledKernel_apply ρ hε.ne' x

theorem scalingSupport : Expected.ScalingSupport := by
  intro d 𝕜 _ ρ ε hε
  have heq : (scaledKernel ρ ε : Space d → 𝕜) =
      (ε ^ d)⁻¹ • ((ρ : Space d → 𝕜) ∘
        (Homeomorph.smul (Units.mk0 ε⁻¹ (inv_ne_zero hε.ne')) : Space d ≃ₜ Space d)) := by
    ext x
    exact scaledKernel_apply ρ hε.ne' x
  rw [heq]
  change closure (Function.support _) = _
  rw [Function.support_const_smul_of_ne_zero _ _ (inv_ne_zero (pow_ne_zero _ hε.ne'))]
  change tsupport ((ρ : Space d → 𝕜) ∘ _) = _
  rw [tsupport_comp_eq_preimage]
  ext x
  change ε⁻¹ • x ∈ tsupport ρ ↔ x ∈ ε • tsupport ρ
  exact (Set.mem_smul_set_iff_inv_smul_mem₀ hε.ne' _ x).symm

theorem scalingIntegrals : Expected.ScalingIntegrals := by
  intro d 𝕜 _ ρ ε hε
  have hdim : Module.finrank ℝ (Space d) = d := by simp [Space]
  have hpow : ε ^ d ≠ 0 := pow_ne_zero _ hε.ne'
  constructor
  · simp_rw [scaledKernel_apply ρ hε.ne']
    rw [integral_smul, Measure.integral_comp_inv_smul_of_nonneg volume _ hε.le,
      hdim, smul_smul, inv_mul_cancel₀ hpow, one_smul]
  · simp_rw [scaledKernel_apply ρ hε.ne', norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _))]
    rw [integral_const_mul]
    have hi := Measure.integral_comp_inv_smul_of_nonneg volume
      (fun x : Space d => ‖ρ x‖) hε.le
    rw [hdim] at hi
    rw [hi, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpow, one_mul]

/-- Shrinking is a compactness argument and does not use normalization. -/
theorem shrinkingSupport : Expected.ShrinkingSupport := by
  intro d 𝕜 _ ρ δ hδ
  obtain ⟨R, hR⟩ := ρ.hasCompactSupport.isBounded.exists_norm_le
  have hpos : 0 < max R 0 + 1 := by positivity
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hpos)] with ε hε
  rw [scalingSupport d 𝕜 ρ ε hε.1]
  rintro x ⟨z, hz, rfl⟩
  rw [Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_of_nonneg hε.1.le]
  have hzR : ‖z‖ ≤ max R 0 + 1 := (hR z hz).trans (by linarith [le_max_left R 0])
  exact (mul_le_mul_of_nonneg_left hzR hε.1.le).trans_lt
    ((lt_div_iff₀ hpos).mp hε.2)

/-- A compact subset stays admissible when the kernel support is small. -/
theorem eventuallyAdmissible : Expected.EventuallyAdmissible := by
  intro d 𝕜 _ Ω ρ K hK
  obtain ⟨δ, hδ, hδΩ⟩ := K.isCompact.exists_thickening_subset_open Ω.isOpen hK
  filter_upwards [shrinkingSupport d 𝕜 ρ δ hδ] with ε hε
  have hKU : (K : Set (Space d)) ⊆ convolutionDomain Ω (scaledKernel ρ ε) := by
    intro x hx z hz
    apply hδΩ
    apply Metric.mem_thickening_iff.mpr
    refine ⟨x, hx, ?_⟩
    simpa [dist_eq_norm] using hε hz
  exact ⟨⟨convolutionDomain Ω (scaledKernel ρ ε),
    localConvolution_openDomain d 𝕜 Ω (scaledKernel ρ ε)⟩, hKU, Subset.rfl⟩

theorem relativelyCompactDomain : Expected.RelativelyCompactDomain := by
  intro d 𝕜 _ Ω V ρ hVc hVΩ
  filter_upwards [eventuallyAdmissible d 𝕜 Ω ρ ⟨closure (V : Set (Space d)), hVc⟩ hVΩ]
    with ε hε
  obtain ⟨W, hW, hWU⟩ := hε
  exact subset_closure.trans (hW.trans hWU)

/-- The full unnormalized local theorem is reused without restricting its domain. -/
theorem completeLocalConvolution : Expected.CompleteLocalConvolution :=
  ⟨localConvolution_openDomain, localConvolution_admissibleTest,
    localConvolution_pairing, localConvolution_smooth, localConvolution_kernelDerivative,
    localConvolution_derivativeDomain, localConvolution_derivative, localConvolution_regularIntegral⟩

/-- The inner integral is the usual convolution with the reflected kernel. -/
theorem reflectedSmoothing_eq_convolution {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (φ : Space d → 𝕜) :
    reflectedSmoothing ρ φ =
      convolution φ (reflectedKernel ρ) (ContinuousLinearMap.mul ℝ 𝕜) volume := by
  funext y
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp [reflectedKernel, mul_comm]

/-- Compactness of all supports appearing in the transpose formula. -/
def smoothingSupport {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (φ : TestSpace 𝕜 Ω) : Compacts (Space d) :=
  ⟨(fun p : Space d × Space d => p.1 - p.2) '' (tsupport φ ×ˢ tsupport ρ),
    (φ.hasCompactSupport.prod ρ.hasCompactSupport).image
      (continuous_fst.sub continuous_snd)⟩

theorem reflectedSmoothing_smooth {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (φ : TestSpace 𝕜 Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (reflectedSmoothing ρ φ) := by
  rw [reflectedSmoothing_eq_convolution]
  exact (reflectedKernel ρ).hasCompactSupport.contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ 𝕜) φ.continuous.locallyIntegrable
    (reflectedKernel ρ).contDiff

theorem reflectedSmoothing_support {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (φ : TestSpace 𝕜 Ω) :
    tsupport (reflectedSmoothing ρ φ) ⊆ smoothingSupport ρ φ := by
  apply closure_minimal _ (smoothingSupport ρ φ).isCompact.isClosed
  intro y hy
  by_contra hn
  apply hy
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro x
  change ρ (x - y) * φ x = 0
  by_cases hφ : φ x = 0
  · rw [hφ, mul_zero]
  · have hρ : ρ (x - y) = 0 := by
      by_contra hρ
      apply hn
      exact ⟨(x, x - y), ⟨subset_tsupport _ hφ, subset_tsupport _ hρ⟩,
        sub_sub_cancel x y⟩
    rw [hρ, zero_mul]

theorem smoothingSupport_subset {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (φ : TestSpace 𝕜 Ω)
    (hφ : tsupport φ ⊆ convolutionDomain Ω ρ) :
    (smoothingSupport ρ φ : Set (Space d)) ⊆ Ω := by
  rintro y ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
  exact hφ hx z hz

/-- A concrete fixed-support representative of the reflected smoothing. -/
def smoothingStage {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (φ : TestSpace 𝕜 Ω) :
    FixedSupport d 𝕜 (smoothingSupport ρ φ) :=
  ContDiffMapSupportedIn.of_support_subset (reflectedSmoothing_smooth ρ φ)
    ((subset_tsupport _).trans (reflectedSmoothing_support ρ φ))

theorem scaled_conditions {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (hρ : (∫ x, ρ x) = 1) :
    U2.ApproximateIdentitiesExpected.Conditions volume (fun ε x => scaledKernel ρ ε x) := by
  refine ⟨fun ε _ => (scaledKernel ρ ε).continuous.integrable_of_hasCompactSupport
    (scaledKernel ρ ε).hasCompactSupport, ?_, ?_, ?_⟩
  · intro ε hε
    rw [(scalingIntegrals d 𝕜 ρ ε hε).1, hρ]
  · exact ⟨∫ x, ‖ρ x‖, integral_nonneg (fun _ => norm_nonneg _),
      fun ε hε => (scalingIntegrals d 𝕜 ρ ε hε).2.le⟩
  · intro δ hδ
    apply tendsto_const_nhds.congr'
    filter_upwards [shrinkingSupport d 𝕜 ρ δ hδ] with ε hε
    symm
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    apply norm_eq_zero.mpr
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have h := hε hs
    have ht : dist x 0 < δ := h
    exact (not_lt_of_gt hx) ht

theorem reflected_conditions {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (hρ : (∫ x, ρ x) = 1) :
    U2.ApproximateIdentitiesExpected.Conditions volume
      (fun ε x => reflectedKernel (scaledKernel ρ ε) x) := by
  have hk := scaled_conditions ρ hρ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε hε
    exact (reflectedKernel (scaledKernel ρ ε)).continuous.integrable_of_hasCompactSupport
      (reflectedKernel (scaledKernel ρ ε)).hasCompactSupport
  · intro ε hε
    change (∫ x, scaledKernel ρ ε (-x)) = 1
    rw [integral_neg_eq_self]
    exact hk.2.1 ε hε
  · obtain ⟨A, hA, hb⟩ := hk.2.2.1
    refine ⟨A, hA, fun ε hε => ?_⟩
    change (∫ x, ‖scaledKernel ρ ε (-x)‖) ≤ A
    rw [integral_neg_eq_self (fun x : Space d => ‖scaledKernel ρ ε x‖)]
    exact hb ε hε
  · intro δ hδ
    apply tendsto_const_nhds.congr'
    filter_upwards [shrinkingSupport d 𝕜 ρ δ hδ] with ε hε
    symm
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    change ‖scaledKernel ρ ε (-x)‖ = 0
    apply norm_eq_zero.mpr
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have ht := hε hs
    have ht' : dist x 0 < δ := by simpa using ht
    exact (not_lt_of_gt hx) ht'

/-- Uniform approximation of any bounded uniformly continuous representative. -/
theorem reflectedSmoothing_uniform {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (hρ : (∫ x, ρ x) = 1)
    (f : Space d → 𝕜) (hf : UniformContinuous f) (hb : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) :
    TendstoUniformly (fun ε => reflectedSmoothing (scaledKernel ρ ε) f) f (𝓝[>] (0 : ℝ)) := by
  have h := (U2.ApproximateIdentities.uniform_recovery volume
    (fun ε x => reflectedKernel (scaledKernel ρ ε) x) (reflected_conditions ρ hρ) f hf hb).2
  convert h using 1
  funext ε y
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp [reflectedKernel]

/-- The whole-space domain imposes no support constraint. -/
theorem mem_convolutionDomain_top {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (x : Space d) :
    x ∈ convolutionDomain ⊤ ρ := by intro z hz; trivial

/-- Put the reflected kernel in the regular distribution, so derivatives act on φ. -/
theorem reflectedSmoothing_eq_local_left {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ φ : TestSpace 𝕜 (⊤ : Opens (Space d))) :
    reflectedSmoothing ρ φ = localConvolution (regularDistribution ⊤ (reflectedKernel ρ)) φ := by
  funext y
  rw [localConvolution_regularIntegral d 𝕜 ⊤ (reflectedKernel ρ)
    ((reflectedKernel ρ).continuous.locallyIntegrable.locallyIntegrableOn _) φ y
    (mem_convolutionDomain_top φ y)]
  simp only [Opens.coe_top, setIntegral_univ]
  rw [← integral_sub_left_eq_self (fun x : Space d => reflectedKernel ρ x * φ (y - x)) volume y]
  simp only [sub_sub_cancel]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp [reflectedKernel]

/-- Put φ in the regular distribution, so derivatives act on the reflected kernel. -/
theorem reflectedSmoothing_eq_local_right {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ φ : TestSpace 𝕜 (⊤ : Opens (Space d))) :
    reflectedSmoothing ρ φ = localConvolution (regularDistribution ⊤ φ) (reflectedKernel ρ) := by
  funext y
  rw [localConvolution_regularIntegral d 𝕜 ⊤ φ
    (φ.continuous.locallyIntegrable.locallyIntegrableOn _) (reflectedKernel ρ) y
    (mem_convolutionDomain_top _ y)]
  simp only [Opens.coe_top, setIntegral_univ]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp [reflectedKernel, mul_comm]

theorem reflectedSmoothing_partialWord_left {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ φ : TestSpace 𝕜 (⊤ : Opens (Space d))) (l : List (Fin d)) :
    partialWord (reflectedSmoothing ρ φ) l = reflectedSmoothing ρ (testPartialWord ⊤ l φ) := by
  rw [reflectedSmoothing_eq_local_left]
  funext y
  rw [localConvolution_partialWord _ φ l y (mem_convolutionDomain_top φ y)]
  exact congrFun (reflectedSmoothing_eq_local_left ρ (testPartialWord ⊤ l φ)).symm y

/-- Coordinate derivatives of the inner integral, in the form needed for finite jets. -/
theorem reflectedSmoothing_partialWord_right {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ φ : TestSpace 𝕜 (⊤ : Opens (Space d))) (l : List (Fin d)) (y : Space d) :
    partialWord (reflectedSmoothing ρ φ) l y =
      ∫ x, φ x * ((-1 : 𝕜) ^ l.length * partialWord ρ l (x - y)) := by
  rw [reflectedSmoothing_eq_local_right,
    localConvolution_partialWord _ _ l y (mem_convolutionDomain_top _ y),
    localConvolution_regularIntegral d 𝕜 ⊤ φ
      (φ.continuous.locallyIntegrable.locallyIntegrableOn _) _ y (mem_convolutionDomain_top _ y)]
  simp only [Opens.coe_top, setIntegral_univ]
  have hrefl : (reflectedKernel ρ : Space d → 𝕜) = fun z => ρ (0 - z) := by
    ext z; simp [reflectedKernel]
  simp only [testPartialWord_coe, hrefl, partialWord_const_sub ρ.contDiff]
  simp only [zero_sub, neg_sub]

theorem reflectedSmoothing_partialWord_uniform {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ φ : TestSpace 𝕜 (⊤ : Opens (Space d))) (hρ : (∫ x, ρ x) = 1)
    (l : List (Fin d)) :
    TendstoUniformly (fun ε => partialWord (reflectedSmoothing (scaledKernel ρ ε) φ) l)
      (partialWord φ l) (𝓝[>] (0 : ℝ)) := by
  let θ := testPartialWord ⊤ l φ
  have hb : ∃ M : ℝ, ∀ x, ‖θ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := θ.continuous.norm.bddAbove_range_of_hasCompactSupport θ.hasCompactSupport.norm
    exact ⟨M, fun x => hM (mem_range_self x)⟩
  have hu := reflectedSmoothing_uniform ρ hρ θ
    (θ.hasCompactSupport.uniformContinuous_of_continuous θ.continuous) hb
  simp only [reflectedSmoothing_partialWord_left, ← testPartialWord_coe ⊤ l φ]
  exact hu

/-- A fixed compact neighborhood of the input support contains all small smoothings. -/
theorem smoothingSupport_eventually_subset {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (φ : TestSpace 𝕜 Ω) (K : Compacts (Space d))
    (hφK : tsupport φ ⊆ interior (K : Set (Space d))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (smoothingSupport (scaledKernel ρ ε) φ : Set (Space d)) ⊆ K := by
  obtain ⟨δ, hδ, hb⟩ := φ.hasCompactSupport.exists_thickening_subset_open isOpen_interior hφK
  filter_upwards [shrinkingSupport d 𝕜 ρ δ hδ] with ε hε
  rintro y ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
  apply interior_subset (hb _)
  apply Metric.mem_thickening_iff.mpr
  refine ⟨x, hx, ?_⟩
  simpa [dist_eq_norm] using hε hz

/-- Use zero at irrelevant parameters where the chosen common support is too small. -/
def approximateStage {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (φ : TestSpace 𝕜 Ω)
    (K : Compacts (Space d)) (ε : ℝ) : FixedSupport d 𝕜 K := by
  classical
  exact if h : (smoothingSupport (scaledKernel ρ ε) φ : Set (Space d)) ⊆ K then
    ContDiffMapSupportedIn.of_support_subset (reflectedSmoothing_smooth _ φ)
      ((subset_tsupport _).trans ((reflectedSmoothing_support _ φ).trans h))
    else 0

theorem approximateStage_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (φ : TestSpace 𝕜 Ω)
    (K : Compacts (Space d)) (ε : ℝ)
    (h : (smoothingSupport (scaledKernel ρ ε) φ : Set (Space d)) ⊆ K) :
    (approximateStage ρ φ K ε : Space d → 𝕜) = reflectedSmoothing (scaledKernel ρ ε) φ := by
  simp only [approximateStage, dite_eq_left h]
  rfl

theorem fixedSupportApproximation : Expected.FixedSupportApproximation := by
  intro d 𝕜 _ Ω ρ hρ φ
  obtain ⟨Kset, hKc, hφK, hKΩ⟩ := exists_compact_between φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  let K : Compacts (Space d) := ⟨Kset, hKc⟩
  let φK : FixedSupport d 𝕜 K := ContDiffMapSupportedIn.of_support_subset φ.contDiff
    ((subset_tsupport _).trans (hφK.trans interior_subset))
  let φ₀ : TestSpace 𝕜 (⊤ : Opens (Space d)) := zeroExtension 𝕜 (le_top : Ω ≤ ⊤) φ
  let ψ := approximateStage ρ φ K
  have hev := smoothingSupport_eventually_subset ρ φ K hφK
  refine ⟨K, hKΩ, φK, ψ, ?_, ?_, ?_⟩
  · ext y; rfl
  · apply (coordinateStageTopology d 𝕜 K).tendsto_nhds ψ φK |>.mpr
    intro m η hη
    have hu (a : FiniteJets.Word d m) :
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y,
          ‖partialWord (reflectedSmoothing (scaledKernel ρ ε) φ₀) (List.ofFn a.2) y -
            partialWord φ₀ (List.ofFn a.2) y‖ < η / 2 := by
      have ht := Metric.tendstoUniformly_iff.mp
        (reflectedSmoothing_partialWord_uniform ρ φ₀ hρ (List.ofFn a.2))
        (η / 2) (half_pos hη)
      filter_upwards [ht] with ε hε
      intro y
      simpa only [dist_eq_norm, norm_sub_rev] using hε y
    have hall := Filter.eventually_all.mpr hu
    filter_upwards [hev, hall] with ε hε hεu
    apply lt_of_le_of_lt _ (half_lt_self hη)
    apply (coordinateSeminormFormula d 𝕜 K m (ψ ε - φK) (η / 2) (half_pos hη).le).mpr
    intro k hk a y hy
    change ‖iteratedFDeriv ℝ k ((ψ ε : Space d → 𝕜) - (φK : Space d → 𝕜)) y
      (fun j => coordinateVector d (a j))‖ ≤ η / 2
    rw [iteratedFDeriv_sub_apply ((ψ ε).contDiff.of_le (by simp)).contDiffAt
      (φK.contDiff.of_le (by simp)).contDiffAt, sub_apply,
      ← partialWord_ofFn (ψ ε).contDiff a, ← partialWord_ofFn φK.contDiff a,
      approximateStage_apply ρ φ K ε hε]
    have hφKf : (φK : Space d → 𝕜) = φ := rfl
    have hφ₀f : (φ₀ : Space d → 𝕜) = φ := by
      funext x
      exact (zeroExtensionProperties d 𝕜 Ω ⊤ le_top φ).1 x
    rw [hφKf]
    simpa only [hφ₀f] using (hεu ⟨⟨k, by omega⟩, a⟩ y).le
  · filter_upwards [hev] with ε hε
    exact congrFun (approximateStage_apply ρ φ K ε hε)

/-- The jet integrand has compact support in the integration variable. -/
theorem weightedJet_integrable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (φ : TestSpace 𝕜 Ω)
    (K : Compacts (Space d)) (m : ℕ) :
    Integrable (fun x => φ x • translationJet K m ρ x) := by
  have hc : Continuous (fun x => φ x • translationJet K m ρ x) :=
    φ.continuous.smul (contDiff_translationJet K m ρ).continuous
  exact hc.integrable_of_hasCompactSupport (φ.hasCompactSupport.smul_right)

/-- Bochner integration in the Banach space of finitely many continuous jets.
This is the precise replacement for the source's seminorm Riemann sums. -/
theorem integral_weightedJet {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (φ : TestSpace 𝕜 Ω) (m : ℕ) :
    (∫ x, φ x • translationJet (smoothingSupport ρ φ) m ρ x) =
      FiniteJets.jet 𝕜 (smoothingSupport ρ φ) m (smoothingStage ρ φ) := by
  let K := smoothingSupport ρ φ
  let φ₀ : TestSpace 𝕜 (⊤ : Opens (Space d)) := zeroExtension 𝕜 (le_top : Ω ≤ ⊤) φ
  have hφ₀f : (φ₀ : Space d → 𝕜) = φ := by
    funext x
    exact (zeroExtensionProperties d 𝕜 Ω ⊤ le_top φ).1 x
  funext a
  ext y
  let ev : FiniteJets.Jets 𝕜 K m →L[𝕜] 𝕜 :=
    (ContinuousMap.evalCLM 𝕜 y).comp (ContinuousLinearMap.proj a)
  have heval := ev.integral_comp_comm (weightedJet_integrable ρ φ K m)
  change (∫ x, φ x • translationJet K m ρ x) a y = _
  change ev (∫ x, φ x • translationJet K m ρ x) = _
  rw [← heval, FiniteJets.jet_apply,
    ← partialWord_ofFn (smoothingStage ρ φ).contDiff a.2]
  have hsf : (smoothingStage ρ φ : Space d → 𝕜) = reflectedSmoothing ρ φ := rfl
  rw [hsf, ← hφ₀f, reflectedSmoothing_partialWord_right ρ φ₀ (List.ofFn a.2)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  simp only [List.length_ofFn]
  rfl

/-- The local transpose identity for an arbitrary compact smooth kernel. -/
theorem integralPairing : Expected.IntegralPairing := by
  intro d 𝕜 _ Ω T ρ φ hφ
  let K := smoothingSupport ρ φ
  have hKΩ : (K : Set (Space d)) ⊆ Ω := smoothingSupport_subset ρ φ hφ
  let θ := smoothingStage ρ φ
  let ψ := stageInclusion 𝕜 hKΩ θ
  obtain ⟨m, L, hL⟩ := FiniteJets.distribution_factorization 𝕜 T K hKΩ
  let H : Space d → FiniteJets.Jets 𝕜 K m := fun x => φ x • translationJet K m ρ x
  have hi : Integrable H := weightedJet_integrable ρ φ K m
  have heq : (fun x => localConvolution T ρ x * φ x) = fun x => L (H x) := by
    funext x
    by_cases hx : φ x = 0
    · simp only [H, hx, zero_smul, map_zero, mul_zero]
    · have hxs : x ∈ tsupport φ := subset_tsupport _ hx
      have hxU := hφ hxs
      have hs : tsupport (translatedKernel ρ x) ⊆ K := by
        intro y hy
        have hz : x - y ∈ tsupport ρ :=
          tsupport_comp_subset_preimage ρ (continuous_const.sub continuous_id) hy
        exact ⟨(x, x - y), ⟨hxs, hz⟩, sub_sub_cancel x y⟩
      rw [localConvolution_eq_jetPairing T ρ K hKΩ m L hL x hxU hs]
      simp only [H, map_smul, smul_eq_mul, mul_comm]
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro y
    change stageInclusion 𝕜 hKΩ θ y = reflectedSmoothing ρ φ y
    rfl
  · rw [heq]
    exact L.integrable_comp hi
  · rw [heq, L.integral_comp_comm hi, integral_weightedJet ρ φ m, hL]

theorem eventuallyPairing : Expected.EventuallyPairing := by
  intro d 𝕜 _ Ω T ρ φ
  filter_upwards [eventuallyAdmissible d 𝕜 Ω ρ
    ⟨tsupport φ, φ.hasCompactSupport⟩ φ.tsupport_subset] with ε hε
  obtain ⟨V, hφV, hVU⟩ := hε
  obtain ⟨ψ, hψ, hi, hp⟩ := integralPairing d 𝕜 Ω T (scaledKernel ρ ε) φ (hφV.trans hVU)
  exact ⟨V, ψ, hφV, hVU, hψ, hi, hp⟩

theorem distributionLimit : Expected.DistributionLimit := by
  intro d 𝕜 _ Ω T ρ hρ φ
  obtain ⟨K, hK, φK, ψ, hφK, ht, heval⟩ := fixedSupportApproximation d 𝕜 Ω ρ hρ φ
  have hlim : Tendsto (fun ε => T (stageInclusion 𝕜 hK (ψ ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (T φ)) := by
    have h := ((T.comp (stageInclusion 𝕜 hK)).continuous.tendsto φK).comp ht
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, hφK] using h
  apply hlim.congr'
  filter_upwards [eventuallyPairing d 𝕜 Ω T ρ φ, heval] with ε hp he
  obtain ⟨V, θ, _, _, hθ, _, hp⟩ := hp
  have htests : stageInclusion 𝕜 hK (ψ ε) = θ := by
    ext y
    change ψ ε y = θ y
    rw [he y, hθ y]
  rw [htests]
  exact hp.symm

end P102.U4.Mollification
