import MathGenome.Internal.LinearPDE.P201Specs.Potential.WeakHarmonicBoundary
import MathGenome.Internal.LinearPDE.P201.Potential.ContinuousHarmonicLift
import MathGenome.Internal.LinearPDE.P201.Potential.Weyl
import MathGenome.Internal.LinearPDE.P201.Elliptic.WeakComparison
import MathGenome.Internal.LinearPDE.P201.Common.ExactTrace
import MathGenome.Internal.LinearPDE.P201.Common.InteriorTesting
import MathGenome.Internal.FourierSobolev.P102.U4.MeyersSerrin

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace MeasureTheory Filter Metric
open scoped ENNReal InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise

namespace P201.WeakHarmonicBoundary

/-- Smoothness on a neighborhood, without conditions away from the closure. -/
def SmoothNearClosure {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (f : Space n → 𝕜) : Prop :=
  ∃ U : Set (Space n), IsOpen U ∧ closure (Ω : Set _) ⊆ U ∧
    ContDiffOn ℝ (⊤ : ℕ∞) f U

abbrev WeakHarmonic {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) : Prop :=
  ∀ v : H10 ℝ Ω,
    ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) u v.val = 0

theorem identity_elliptic {n : ℕ} (Ω : Domain n) :
    P201Specs.Dirichlet.Elliptic Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) 1 := by
  filter_upwards [] with x ξ
  rw [EuclideanSpace.norm_sq_eq]
  simp [Matrix.one_apply, pow_two]


theorem continuousOn_closure_memLp {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (hb : Bornology.IsBounded (Ω : Set (Space n)))
    {f : Space n → 𝕜} (hf : ContinuousOn f (closure (Ω : Set _))) :
    MemLp f 2 (domainMeasure Ω) := by
  have hc : IsCompact (closure (Ω : Set (Space n))) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hb.closure⟩
  let : IsFiniteMeasure (domainMeasure Ω) :=
    ⟨by
      simpa [domainMeasure, P201Specs.domainMeasure] using
        (measure_mono (μ := volume) subset_closure).trans_lt hc.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hc.bddAbove_image hf.norm
  apply MemLp.of_bound ((hf.mono subset_closure).aestronglyMeasurable Ω.isOpen.measurableSet) C
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact hC ⟨x, subset_closure hx, rfl⟩

theorem smooth_hilbert_representative {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (f : Space n → 𝕜) (hf : SmoothNearClosure Ω f) (k : ℕ) :
    ∃ u : H 𝕜 Ω k, (hUnderlying Ω k u : Space n → 𝕜) =ᵐ[domainMeasure Ω] f := by
  obtain ⟨U, hU, hsub, hdiff⟩ := hf
  have hΩU : (Ω : Set (Space n)) ⊆ U := subset_closure.trans hsub
  have h0 := continuousOn_closure_memLp Ω hb (hdiff.continuousOn.mono hsub)
  have hα (α : MultiIndex n) : MemLp (multiPartial f α) 2 (domainMeasure Ω) := by
    have hfinite : ContDiffOn ℝ (α.card : ℕ) f U := hdiff.of_le (by simp)
    have hd : ContDiffOn ℝ (0 : ℕ) (multiPartial f α) U :=
      P102.U4.partialWord_contDiffOn ⟨U, hU⟩
        hfinite
        (α.sort (· ≤ ·)) 0 (by simp)
    exact continuousOn_closure_memLp Ω hb (hd.continuousOn.mono hsub)
  have heq (g : Space n → 𝕜) (hg : MemLp g 2 (domainMeasure Ω)) :
      regularDistribution Ω (hg.toLp g) = regularDistribution Ω g := by
    apply (P102.U4.regular_injectivity n 𝕜 Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω 2 _) (locallyIntegrableOn_of_locallyIntegrable_restrict
        (hg.locallyIntegrable (by norm_num)))).mpr
    exact hg.coeFn_toLp
  have hder : P102.U4.HasSobolevDerivatives Ω k 2 (h0.toLp f) := by
    intro α hcard
    refine ⟨(hα α).toLp (multiPartial f α), ?_⟩
    change distributionDerivative α (regularDistribution Ω (h0.toLp f)) =
      regularDistribution Ω ((hα α).toLp (multiPartial f α))
    rw [heq f h0, heq (multiPartial f α) (hα α)]
    apply P102.U4.derivative_classicalCompatibility n 𝕜 Ω α f
    exact (hdiff.of_le (by simp)).mono hΩU
  obtain ⟨w, hw⟩ := (Set.ext_iff.mp (P102.U4.sobolev_range Ω k 2) (h0.toLp f)).mpr hder
  refine ⟨(hToW 𝕜 Ω k).symm w, ?_⟩
  have hh : hUnderlying Ω k ((hToW 𝕜 Ω k).symm w) = h0.toLp f := by
    change P102.U4.sobolevUnderlying ((hToW 𝕜 Ω k) ((hToW 𝕜 Ω k).symm w)) = _
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  rw [hh]
  exact h0.coeFn_toLp

theorem identity_energy {n : ℕ} (Ω : Domain n) (u v : H ℝ Ω 1) :
    ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) u v =
      ∫ x in Ω, inner ℝ (hGradient u x) (hGradient v x) := by
  change (∫ x in Ω, ∑ i, ∑ j,
    (1 : Matrix (Fin n) (Fin n) ℝ) i j * hFirstDerivative u j x *
      star (hFirstDerivative v i x)) = _
  apply integral_congr_ae
  filter_upwards [Dirichlet.gradient_ae Ω u, Dirichlet.gradient_ae Ω v] with x hu hv
  rw [hu, hv]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

/-- The variational harmonic equation tests every compact smooth function. -/
theorem weak_harmonic_equation {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1)
    (hu : WeakHarmonic Ω u) :
    ∀ φ : Test ℝ Ω, (∫ x in Ω, inner ℝ (hGradient u x) (gradient φ x)) = 0 := by
  intro φ
  obtain ⟨v, hv⟩ := InteriorTesting.exists_test_class Ω φ
  have hg := InteriorTesting.smooth_gradient_ae Ω v.val φ hv
  have he : (∫ x in Ω, inner ℝ (hGradient u x) (gradient φ x)) = 0 := by
    calc
      _ = ∫ x in Ω, inner ℝ (hGradient u x) (hGradient v.val x) :=
        integral_congr_ae (hg.mono fun x hx =>
          congrArg (fun q : Space n => inner ℝ (hGradient u x) q) hx.symm)
      _ = ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) u v.val :=
        (identity_energy Ω u v.val).symm
      _ = 0 := hu v
  exact he

theorem weak_harmonic_distribution {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1)
    (hu : WeakHarmonic Ω u) :
    distributionLaplacian (regularDistribution Ω (hUnderlying Ω 1 u)) = 0 := by
  have heq := weak_harmonic_equation Ω u hu
  have hdiv : negativeDivergenceDistribution Ω (hGradient u) = 0 := by
    ext φ
    rw [InteriorTesting.negativeDivergenceDistribution_pairing]
    have hφ := heq φ
    change (∫ x in Ω, inner ℝ (hGradient u x) (gradient φ x)) = _ at hφ ⊢
    exact hφ
  have hg (i : Fin n) : regularDistribution Ω (fun x => hGradient u x i) =
      regularDistribution Ω (hFirstDerivative u i) := by
    apply (P102.U4.regular_injectivity n ℝ Ω _ _
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        (((Lp.memLp (hGradient u)).eval_piLp i).locallyIntegrable (by norm_num)))
      (P102.U4.domainLp_locallyIntegrable Ω 2 _)).mpr
    exact (Dirichlet.gradient_ae Ω u).mono fun x hx => congrArg (fun v : Space n => v i) hx
  have hid : negativeDivergenceDistribution Ω (hGradient u) =
      -distributionLaplacian (regularDistribution Ω (hUnderlying Ω 1 u)) := by
    change -(∑ i : Fin n, distributionDerivative {i}
      (regularDistribution Ω (fun x => hGradient u x i))) =
        -(∑ i : Fin n, distributionDerivative {i, i} (regularDistribution Ω (hUnderlying Ω 1 u)))
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hg]
    have hd : distributionDerivative {i} (regularDistribution Ω (hUnderlying Ω 1 u)) =
        regularDistribution Ω (hFirstDerivative u i) :=
      hilbertDerivativeDistribution Ω 1 u ⟨{i}, by simp⟩
    rw [← hd]
    change P102.U4.distributionPartial {i} (P102.U4.distributionPartial {i} _) = _
    rw [← P102.U4.derivative_add n ℝ Ω]
    rfl
  rw [hid] at hdiv
  exact neg_eq_zero.mp hdiv

/-- Every real weak harmonic class has a smooth harmonic interior
representative equal to its actual L² values almost everywhere. -/
theorem weak_harmonic_representative {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (u : H ℝ Ω 1) (hu : WeakHarmonic Ω u) :
    ∃ h : Space n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) h Ω ∧
      P201Specs.MeanValues.IsHarmonic Ω h ∧
      (hUnderlying Ω 1 u : Space n → ℝ) =ᵐ[domainMeasure Ω] h := by
  obtain ⟨h, hs, hh, hreg, _⟩ := Weyl.weyl hn Ω
    (regularDistribution Ω (hUnderlying Ω 1 u)) (weak_harmonic_distribution Ω u hu)
  refine ⟨h, hs, hh, ?_⟩
  exact ((P102.U4.regular_injectivity n ℝ Ω _ _
    (hs.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
    (P102.U4.domainLp_locallyIntegrable Ω 2 _)).mp hreg).symm

theorem smooth_compact_extension {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (f : Space n → 𝕜) (hf : SmoothNearClosure Ω f) :
    ∃ F : Space n → 𝕜, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      EqOn F f (closure (Ω : Set (Space n))) := by
  obtain ⟨U, hU, hsub, hdiff⟩ := hf
  have hc : IsCompact (closure (Ω : Set (Space n))) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hb.closure⟩
  obtain ⟨V, hV, hKV, hVU, hcV⟩ := exists_open_between_and_isCompact_closure hc hU hsub
  obtain ⟨χ, hχ, _, hsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hKV
  have hcompact : HasCompactSupport χ := by
    change IsCompact (closure (Function.support χ))
    rw [hsupp]
    exact hcV
  have hsχ : tsupport χ ⊆ U := by
    change closure (Function.support χ) ⊆ U
    rwa [hsupp]
  refine ⟨fun x => χ x • f x, ?_, hcompact.smul_right, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hdiff.contDiffAt (hU.mem_nhds hx))
    · have hzero : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsχ h))
      apply contDiffAt_const.congr_of_eventuallyEq
      exact hzero.mono fun y hy => by
        change χ y • f y = (0 : 𝕜)
        change χ y = (0 : ℝ) at hy
        rw [hy, zero_smul]
  · intro x hx
    change χ x • f x = f x
    rw [(hχone x).mp hx, one_smul]


/-- The geometric chart interface already includes Lipschitz graph charts. -/
theorem boundedC2_isLipschitz {m : ℕ} (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hc : HasCkBoundary Ω 2) : IsBoundedLipschitzOpen Ω := by
  refine ⟨Ω.isOpen.preimage (graphFrame m).continuous, ?_, ?_⟩
  · change Bornology.IsBounded ((graphFrame m) ⁻¹' (Ω : Set (Space (m + 1))))
    have he : (graphFrame m) ⁻¹' (Ω : Set (Space (m + 1))) =
        (graphFrame m).symm '' (Ω : Set (Space (m + 1))) := by
      ext x
      constructor
      · intro hx
        exact ⟨(graphFrame m) x, hx, (graphFrame m).symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        change (graphFrame m) ((graphFrame m).symm y) ∈ Ω
        rwa [(graphFrame m).apply_symm_apply]
    rw [he]
    exact (graphFrame m).symm.isometry.lipschitzWith.isBounded_image hb
  · intro p hp
    obtain ⟨C, hC, _⟩ := hc p hp
    exact ⟨C, hC⟩

/-- Smooth agreement for neighborhood-smooth representatives follows by
localizing to a globally smooth function before applying the trace theorem. -/
theorem trace_smooth_near {m : ℕ} (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hLip : IsBoundedLipschitzOpen Ω)
    (T : H ℝ Ω 1 →L[ℝ] P201Specs.Hhalf Ω hLip)
    (hT : P201Specs.Trace.AgreesWithSmooth T)
    (u : H ℝ Ω 1) (f : Space (m + 1) → ℝ) (hf : SmoothNearClosure Ω f)
    (hu : (hUnderlying Ω 1 u : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] f) :
    (P201Specs.Trace.inclusion Ω hLip (T u) : Space (m + 1) → ℝ)
      =ᵐ[boundaryMeasure Ω] f := by
  obtain ⟨F, hF, _, he⟩ := smooth_compact_extension Ω hb f hf
  have huF : (hUnderlying Ω 1 u : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] F := by
    filter_upwards [hu, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    exact hx.trans (he (subset_closure hxΩ)).symm
  filter_upwards [hT u F hF huF, P102.Trace.Ordinary.boundaryMeasure_ae_frontier Ω]
    with x hx hxf
  exact hx.trans (he (frontier_subset_closure hxf))

/-- The actual kernel of the exact trace carries the affine boundary data. -/
theorem trace_affine {m : ℕ} (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hLip : IsBoundedLipschitzOpen Ω)
    (T : H ℝ Ω 1 →L[ℝ] P201Specs.Hhalf Ω hLip)
    (hT : P201Specs.Trace.AgreesWithSmooth T)
    (hker : T.ker = P201Specs.hZeroSubmodule ℝ Ω)
    (u : H ℝ Ω 1) (f : Space (m + 1) → ℝ) (hf : SmoothNearClosure Ω f)
    (hu : ∃ z : H10 ℝ Ω, (hUnderlying Ω 1 u : Space (m + 1) → ℝ)
      =ᵐ[domainMeasure Ω] fun x => f x + hZeroUnderlying Ω z x) :
    (P201Specs.Trace.inclusion Ω hLip (T u) : Space (m + 1) → ℝ)
      =ᵐ[boundaryMeasure Ω] f := by
  obtain ⟨z, hz⟩ := hu
  obtain ⟨G, hG⟩ := smooth_hilbert_representative Ω hb f hf 1
  have he : u = G + z.val := by
    apply hilbertUnderlyingInjective Ω 1
    apply Lp.ext
    rw [map_add]
    filter_upwards [hz, hG, Lp.coeFn_add (hUnderlying Ω 1 G)
      (hUnderlying Ω 1 z.val)] with x hx hGx hadd
    exact hx.trans (by rw [hadd, Pi.add_apply, hGx]; rfl)
  have hzT : T z.val = 0 := by
    change z.val ∈ T.ker
    rw [hker]
    exact z.property
  rw [he, map_add, hzT, add_zero]
  exact trace_smooth_near Ω hb hLip T hT G f hf hG

/-- A.e. order between continuous representatives holds throughout an open set. -/
theorem leOn_of_ae {n : ℕ} (Ω : Domain n) (f g : Space n → ℝ)
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω)
    (h : ∀ᵐ x ∂domainMeasure Ω, f x ≤ g x) : ∀ x ∈ Ω, f x ≤ g x := by
  have he : (fun x => max (f x) (g x)) =ᵐ[domainMeasure Ω] g :=
    h.mono fun x hx => max_eq_right hx
  have hp := MeasureTheory.Measure.eqOn_open_of_ae_eq he Ω.isOpen (fun x hx => Filter.Tendsto.max (hf x hx) (hg x hx)) hg
  intro x hx
  exact (le_max_left _ _).trans_eq (hp hx)

/-- All orders of the radial primitive are smooth away from zero. -/
theorem radialPrimitive_smooth (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (HarmonicBarriers.radialPrimitive n) (Ioi (0 : ℝ)) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun x hx => (HarmonicBarriers.radialPrimitive_hasDerivAt n hx).differentiableAt.differentiableWithinAt, ?_⟩
  apply (show ContDiffOn ℝ (⊤ : ℕ∞) (HarmonicBarriers.radialWeight n) (Ioi (0 : ℝ)) from
    fun x hx => (HarmonicBarriers.radialWeight_contDiffAt n hx _).contDiffWithinAt).congr
  intro x hx
  exact (HarmonicBarriers.radialPrimitive_hasDerivAt n hx).deriv

/-- Smooth representatives have their classical first derivatives in the
canonical weak gradient, with the same L² quotient and bulk measure. -/
theorem gradient_of_smooth {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1)
    (f : Space n → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hu : (hUnderlying Ω 1 u : Space n → ℝ) =ᵐ[domainMeasure Ω] f) :
    (hGradient u : Space n → Space n) =ᵐ[domainMeasure Ω] gradient f := by
  have hd := P102.U4.representsSobolevOn_of_underlying hf (hToW ℝ Ω 1 u) hu
  have hdi (i : Fin n) : (hFirstDerivative u i : Space n → ℝ)
      =ᵐ[domainMeasure Ω] fun x => fderiv ℝ f x (coordinate n i) := by
    simpa only [P102.U4.multiPartial, Multiset.sort_singleton,
      P102.U4.partialWord] using hd ⟨{i}, by simp⟩
  filter_upwards [Dirichlet.gradient_ae Ω u, ae_all_iff.mpr hdi] with x hx hxi
  rw [hx]
  exact PiLp.ext fun i => hxi i

/-- The comparison theorem's test integral is the gradient pairing for the
identity matrix and zero zeroth-order term. -/
theorem testEnergy_identity {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1)
    (φ : Test ℝ Ω) :
    P201Specs.WeakComparison.testEnergy Ω (fun _ => 1) (fun _ => 0) u φ =
      ∫ x in Ω, inner ℝ (hGradient u x) (gradient φ x) := by
  unfold P201Specs.WeakComparison.testEnergy
  apply integral_congr_ae
  filter_upwards [Dirichlet.gradient_ae Ω u] with x hx
  rw [hx]
  simp only [zero_mul, add_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

abbrev TestHarmonic {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) : Prop :=
  ∀ φ : Test ℝ Ω,
    P201Specs.WeakComparison.testEnergy Ω (fun _ => 1) (fun _ => 0) u φ = 0

theorem weak_test_harmonic {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1)
    (hu : WeakHarmonic Ω u) : TestHarmonic Ω u := by
  intro φ
  rw [testEnergy_identity]
  exact weak_harmonic_equation Ω u hu φ

/-- Classical harmonicity implies the smooth-test weak equation. Only
interior smoothness is used for integration by parts. -/
theorem smooth_test_harmonic {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1)
    (f : Space n → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hu : (hUnderlying Ω 1 u : Space n → ℝ) =ᵐ[domainMeasure Ω] f)
    (hh : P201Specs.MeanValues.IsHarmonic Ω f) : TestHarmonic Ω u := by
  intro φ
  rw [testEnergy_identity]
  have he : (∫ x in Ω, inner ℝ (hGradient u x) (gradient φ x)) =
      P201Specs.weakNegativeDivergence Ω (gradient f) φ :=
    integral_congr_ae ((gradient_of_smooth Ω u f hf hu).mono fun x hx => congrArg (fun v : Space n => inner ℝ v (gradient φ x)) hx)
  rw [he, InteriorTesting.flux_testing_identity Ω (MeanValues.gradient_contDiffOn Ω f hh.1)]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  rw [MeanValues.divergence_gradient, hh.2 x hx, neg_zero, zero_mul]

/-- Ordered physical traces compare harmonic H¹ classes, with no boundary
continuity assumption on either class. -/
theorem harmonic_trace_comparison {m : ℕ} (Ω : Domain (m + 1))
    (hLip : IsBoundedLipschitzOpen Ω)
    (T : H ℝ Ω 1 →L[ℝ] P201Specs.Hhalf Ω hLip)
    (hT : P201Specs.Trace.AgreesWithSmooth T)
    (u v : H ℝ Ω 1) (hu : TestHarmonic Ω u) (hv : TestHarmonic Ω v)
    (huv : ∀ᵐ x ∂boundaryMeasure Ω,
      P201Specs.Trace.inclusion Ω hLip (T u) x ≤
        P201Specs.Trace.inclusion Ω hLip (T v) x) :
    ∀ᵐ x ∂domainMeasure Ω, hUnderlying Ω 1 u x ≤ hUnderlying Ω 1 v x := by
  apply WeakComparison.ordered_trace Ω hLip T hT (fun _ => 1) (memLp_top_const _)
    1 (by norm_num) (identity_elliptic Ω) (fun _ => 0) MemLp.zero (by simp)
    (fun _ => 0) u v huv
  · intro φ _
    exact (hu φ).le
  · intro φ _
    exact (hv φ).ge

/-- Exterior-sphere barriers are smooth on a whole neighborhood of the
closed domain. This supplies the H¹ class needed by weak comparison. -/
theorem c2_smooth_barrier {m : ℕ} (Ω : Domain (m + 1))
    (hC : HasCkBoundary Ω 2) (z : Space (m + 1))
    (hz : z ∈ frontier (Ω : Set (Space (m + 1)))) :
    ∃ b : Space (m + 1) → ℝ,
      P201Specs.MeanValues.IsHarmonic Ω b ∧ SmoothNearClosure Ω b ∧ b z = 0 ∧
        ∀ x ∈ closure (Ω : Set (Space (m + 1))), x ≠ z → 0 < b x := by
  obtain ⟨y, r, hr, hzy, hsep⟩ := HarmonicBarriers.c2_exterior_sphere Ω hC hz
  have hne : ∀ x ∈ closure (Ω : Set (Space (m + 1))), x ≠ y := by
    intro x hx heq
    have hd : r ≤ dist x y := by
      by_cases he : x = z
      · simpa only [he, hzy] using le_rfl (a := r)
      · exact (hsep x hx he).le
    rw [heq, dist_self] at hd
    linarith
  let U : Set (Space (m + 1)) := {y}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hsub : closure (Ω : Set (Space (m + 1))) ⊆ U := hne
  let q : Space (m + 1) → ℝ := fun x =>
    HarmonicBarriers.radialPrimitive (m + 1) (‖x - y‖ ^ 2)
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q U := by
    intro x hx
    have hp : 0 < ‖x - y‖ ^ 2 := sq_pos_of_pos
      (norm_pos_iff.mpr (sub_ne_zero.mpr hx))
    exact (((radialPrimitive_smooth (m + 1)).contDiffAt (Ioi_mem_nhds hp)).comp x
      ((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ)).contDiffWithinAt
  let b : Space (m + 1) → ℝ := fun x =>
    q x - HarmonicBarriers.radialPrimitive (m + 1) (r ^ 2)
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) b U := hq.sub contDiffOn_const
  have hqh : P201Specs.MeanValues.IsHarmonic Ω q :=
    ⟨(hq.of_le (by simp)).mono (subset_closure.trans hsub),
      fun x hx => HarmonicBarriers.radialPrimitive_laplacian y x
        (hne x (subset_closure hx))⟩
  refine ⟨b, ?_, ⟨U, hU, hsub, hb⟩, ?_, ?_⟩
  · exact (MeanValues.harmonic_bridge Ω b).mpr
      (((MeanValues.harmonic_bridge Ω q).mp hqh).sub
        (InnerProductSpace.harmonicOnNhd_const _))
  · change HarmonicBarriers.radialPrimitive (m + 1) (‖z - y‖ ^ 2) -
      HarmonicBarriers.radialPrimitive (m + 1) (r ^ 2) = 0
    rw [← dist_eq_norm, hzy, sub_self]
  · intro x hx hxz
    apply sub_pos.mpr
    apply HarmonicBarriers.radialPrimitive_strictMonoOn (m + 1) (sq_pos_of_pos hr)
      (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne x hx))))
    simpa only [dist_eq_norm] using
      (sq_lt_sq₀ hr.le dist_nonneg).mpr (hsep x hx hxz)

/-- Smoothness on a neighborhood is preserved by affine scalar combinations. -/
theorem smooth_near_affine {n : ℕ} (Ω : Domain n) (b : Space n → ℝ)
    (hb : SmoothNearClosure Ω b) (a c : ℝ) :
    SmoothNearClosure Ω (fun x => a + c * b x) := by
  obtain ⟨U, hU, hs, hd⟩ := hb
  exact ⟨U, hU, hs, contDiffOn_const.add (contDiffOn_const.mul hd)⟩

theorem harmonic_affine {n : ℕ} (Ω : Domain n) (b : Space n → ℝ)
    (hb : P201Specs.MeanValues.IsHarmonic Ω b) (a c : ℝ) :
    P201Specs.MeanValues.IsHarmonic Ω (fun x => a + c * b x) := by
  apply (MeanValues.harmonic_bridge Ω _).mpr
  convert (InnerProductSpace.harmonicOnNhd_const a).add
    (((MeanValues.harmonic_bridge Ω b).mp hb).const_smul (c := c)) using 1

/-- Boundary domination transfers to the weak solution through the physical
trace and weak comparison, then holds pointwise for its Weyl representative. -/
theorem weak_barrier_squeeze {m : ℕ} (Ω : Domain (m + 1))
    (hbΩ : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hLip : IsBoundedLipschitzOpen Ω)
    (G₀ : Space (m + 1) → ℝ) (hG₀ : SmoothNearClosure Ω G₀)
    (u : H ℝ Ω 1)
    (hua : ∃ w : H10 ℝ Ω, (hUnderlying Ω 1 u : Space (m + 1) → ℝ)
      =ᵐ[domainMeasure Ω] fun x => G₀ x + hZeroUnderlying Ω w x)
    (hu : WeakHarmonic Ω u)
    (f : Space (m + 1) → ℝ) (hfc : ContinuousOn f Ω)
    (huf : (hUnderlying Ω 1 u : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] f)
    (z : Space (m + 1)) (hz : z ∈ frontier (Ω : Set (Space (m + 1))))
    (b : Space (m + 1) → ℝ) (hbh : P201Specs.MeanValues.IsHarmonic Ω b)
    (hbs : SmoothNearClosure Ω b) (hbz : b z = 0)
    (hbpos : ∀ x ∈ closure (Ω : Set (Space (m + 1))), x ≠ z → 0 < b x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Ω, |f x - G₀ z| ≤ ε + M * b x := by
  have hbcont : ContinuousOn b (closure (Ω : Set (Space (m + 1)))) :=
    hbs.choose_spec.2.2.continuousOn.mono hbs.choose_spec.2.1
  have hGcont : ContinuousOn G₀ (frontier (Ω : Set (Space (m + 1)))) :=
    hG₀.choose_spec.2.2.continuousOn.mono
      (frontier_subset_closure.trans hG₀.choose_spec.2.1)
  have hK : IsCompact (frontier (Ω : Set (Space (m + 1)))) :=
    hbΩ.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨M, hM, hdom⟩ := ContinuousHarmonicLift.barrier_domination hK hz G₀ b
    hGcont (hbcont.mono frontier_subset_closure) hbz
    (fun x hx hne => hbpos x (frontier_subset_closure hx) hne) hε
  let L : Space (m + 1) → ℝ := fun x => G₀ z - ε + (-M) * b x
  let H : Space (m + 1) → ℝ := fun x => G₀ z + ε + M * b x
  have hLs : SmoothNearClosure Ω L := smooth_near_affine Ω b hbs _ _
  have hHs : SmoothNearClosure Ω H := smooth_near_affine Ω b hbs _ _
  obtain ⟨l, hl⟩ := smooth_hilbert_representative Ω hbΩ L hLs 1
  obtain ⟨v, hv⟩ := smooth_hilbert_representative Ω hbΩ H hHs 1
  obtain ⟨T, _, hT, _, _, hker⟩ := Trace.exact_trace m Ω hLip
  have hTu := trace_affine Ω hbΩ hLip T hT hker u G₀ hG₀ hua
  have hTl := trace_smooth_near Ω hbΩ hLip T hT l L hLs hl
  have hTv := trace_smooth_near Ω hbΩ hLip T hT v H hHs hv
  have hlu : ∀ᵐ x ∂boundaryMeasure Ω,
      P201Specs.Trace.inclusion Ω hLip (T l) x ≤
        P201Specs.Trace.inclusion Ω hLip (T u) x := by
    filter_upwards [hTl, hTu, P102.Trace.Ordinary.boundaryMeasure_ae_frontier Ω]
      with x hxl hxu hxf
    rw [hxl, hxu]
    have hd := hdom x hxf
    dsimp [L]
    linarith [neg_abs_le (G₀ x - G₀ z)]
  have huv : ∀ᵐ x ∂boundaryMeasure Ω,
      P201Specs.Trace.inclusion Ω hLip (T u) x ≤
        P201Specs.Trace.inclusion Ω hLip (T v) x := by
    filter_upwards [hTu, hTv, P102.Trace.Ordinary.boundaryMeasure_ae_frontier Ω]
      with x hxu hxv hxf
    rw [hxu, hxv]
    have hd := hdom x hxf
    dsimp [H]
    linarith [le_abs_self (G₀ x - G₀ z)]
  have hlt : TestHarmonic Ω l := smooth_test_harmonic Ω l L
    (hLs.choose_spec.2.2.mono (subset_closure.trans hLs.choose_spec.2.1)) hl
    (harmonic_affine Ω b hbh _ _)
  have hvt : TestHarmonic Ω v := smooth_test_harmonic Ω v H
    (hHs.choose_spec.2.2.mono (subset_closure.trans hHs.choose_spec.2.1)) hv
    (harmonic_affine Ω b hbh _ _)
  have hut := weak_test_harmonic Ω u hu
  have hlow := harmonic_trace_comparison Ω hLip T hT l u hlt hut hlu
  have hupp := harmonic_trace_comparison Ω hLip T hT u v hut hvt huv
  have hlow' : ∀ᵐ x ∂domainMeasure Ω, L x ≤ f x := by
    filter_upwards [hlow, hl, huf] with x hx hlx hux
    simpa only [hlx, hux] using hx
  have hupp' : ∀ᵐ x ∂domainMeasure Ω, f x ≤ H x := by
    filter_upwards [hupp, hv, huf] with x hx hvx hux
    simpa only [hvx, hux] using hx
  have hLc : ContinuousOn L Ω :=
    hLs.choose_spec.2.2.continuousOn.mono (subset_closure.trans hLs.choose_spec.2.1)
  have hHc : ContinuousOn H Ω :=
    hHs.choose_spec.2.2.continuousOn.mono (subset_closure.trans hHs.choose_spec.2.1)
  have hlo := leOn_of_ae Ω L f hLc hfc hlow'
  have hup := leOn_of_ae Ω f H hfc hHc hupp'
  refine ⟨M, hM, fun x hx => abs_le.mpr ?_⟩
  have hhlo := hlo x hx
  have hhup := hup x hx
  dsimp [L] at hhlo
  dsimp [H] at hhup
  constructor <;> linarith

/-- The weak barrier bounds force the full interior boundary limit, before
any continuous representative on the closed domain has been constructed. -/
theorem weak_boundary_limit {m : ℕ} (Ω : Domain (m + 1))
    (hbΩ : Bornology.IsBounded (Ω : Set (Space (m + 1))))
    (hC : HasCkBoundary Ω 2)
    (G₀ : Space (m + 1) → ℝ) (hG₀ : SmoothNearClosure Ω G₀)
    (u : H ℝ Ω 1)
    (hua : ∃ w : H10 ℝ Ω, (hUnderlying Ω 1 u : Space (m + 1) → ℝ)
      =ᵐ[domainMeasure Ω] fun x => G₀ x + hZeroUnderlying Ω w x)
    (hu : WeakHarmonic Ω u)
    (f : Space (m + 1) → ℝ) (hfc : ContinuousOn f Ω)
    (huf : (hUnderlying Ω 1 u : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] f)
    (z : Space (m + 1)) (hz : z ∈ frontier (Ω : Set (Space (m + 1)))) :
    Tendsto f (𝓝[Ω] z) (𝓝 (G₀ z)) := by
  obtain ⟨b, hbh, hbs, hbz, hbpos⟩ := c2_smooth_barrier Ω hC z hz
  have hbcont : ContinuousOn b (closure (Ω : Set (Space (m + 1)))) :=
    hbs.choose_spec.2.2.continuousOn.mono hbs.choose_spec.2.1
  have hbt : Tendsto b (𝓝[Ω] z) (𝓝 (0 : ℝ)) := by
    have ht := ((hbcont z hz.1).mono subset_closure).tendsto
    rwa [hbz] at ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨M, _, hs⟩ := weak_barrier_squeeze Ω hbΩ
    (boundedC2_isLipschitz Ω hbΩ hC) G₀ hG₀ u hua hu f hfc huf
    z hz b hbh hbs hbz hbpos (half_pos hε)
  have ht : Tendsto (fun x => ε / 2 + M * b x) (𝓝[Ω] z) (𝓝 (ε / 2)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hbt))
  have he : ∀ᶠ x in 𝓝[Ω] z, ε / 2 + M * b x < ε :=
    ht.eventually (gt_mem_nhds (by linarith : ε / 2 < ε))
  filter_upwards [self_mem_nhdsWithin, he] with x hx he
  simpa only [Real.dist_eq] using (hs x hx).trans_lt he

/-- Real affine weak harmonic solutions coincide with the continuous
harmonic lift, in every dimension covered by the source. -/
theorem boundary_identification :
    P201Specs.WeakHarmonicBoundary.BoundaryIdentificationStatement := by
  classical
  intro m hm Ω hbΩ hC g G₀ hG₀ hGg u hua hu h hh
  obtain ⟨f, _, hfh, huf⟩ := weak_harmonic_representative (by omega) Ω u hu
  have hfc : ContinuousOn f Ω := hfh.1.continuousOn
  have hGcont : ContinuousOn G₀ (frontier (Ω : Set (Space (m + 1)))) :=
    hG₀.choose_spec.2.2.continuousOn.mono
      (frontier_subset_closure.trans hG₀.choose_spec.2.1)
  have hlim : ∀ z ∈ frontier (Ω : Set (Space (m + 1))),
      Tendsto f (𝓝[Ω] z) (𝓝 (G₀ z)) :=
    fun z hz => weak_boundary_limit Ω hbΩ hC G₀ hG₀ u hua hu f hfc huf z hz
  let F : Space (m + 1) → ℝ := fun x => if x ∈ Ω then f x else G₀ x
  have hF : P201Specs.ContinuousHarmonicLift.IsExtension Ω g F := by
    refine ⟨PerronReplacement.harmonic_congr Ω hfh ?_, ?_, ?_⟩
    · intro x hx
      change x ∈ Ω at hx
      simp only [F, ite_eq_left hx]
    · exact ContinuousHarmonicLift.continuousOn_extension Ω.isOpen hfc hGcont hlim
    · intro z
      have hz : (z : Space (m + 1)) ∉ Ω := by
        intro hzΩ
        exact z.property.2 (by rwa [Ω.isOpen.interior_eq])
      simpa only [F, ite_eq_right hz] using hGg z
  have he := ContinuousHarmonicLift.uniqueness (by omega) Ω hbΩ g F h hF hh
  filter_upwards [huf, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  exact hx.trans ((show f x = F x by exact (ite_eq_left (show x ∈ Ω from hxΩ)).symm).trans
    (he (subset_closure hxΩ)))

end P201.WeakHarmonicBoundary
