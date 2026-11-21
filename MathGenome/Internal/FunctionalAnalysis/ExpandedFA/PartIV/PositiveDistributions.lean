import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.PositiveDistributions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions CompactlySupported ContDiff Topology Manifold

namespace ExpandedFA.PartIV.PositiveDistributions
open ExpandedFA.Distributions
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

local instance : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace

@[simp] theorem realTest_apply (φ : Tests ℝ Ω) (x) :
    realTest (𝕜 := 𝕜) φ x = (φ x : 𝕜) := rfl

@[simp] theorem testToCc_apply (φ : Tests 𝕜 Ω) (x : Ω) :
    testToCc φ x = φ x.val := rfl

theorem testToCc_injective : Function.Injective (testToCc (𝕜 := 𝕜) (Ω := Ω)) := by
  intro φ ψ h
  ext x
  by_cases hx : x ∈ Ω
  · exact DFunLike.congr_fun h ⟨x, hx⟩
  · rw [φ.zero_on_compl hx, ψ.zero_on_compl hx]

/-- A nonnegative smooth compact cutoff equals one on the given compact.
The ambient compact support is contained strictly inside Ω. -/
theorem exists_cutoff (K : Set (Domain d)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : Tests ℝ Ω, (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨L, hL, hLc, hKL, hLΩ⟩ := exists_compact_closed_between hK Ω.isOpen hKΩ
  obtain ⟨f, hf1, hf0, hf⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, Domain d)) hK.isClosed hKL (n := ⊤)
  have hs : tsupport f ⊆ L :=
    closure_minimal (fun x hx => by by_contra hxL; exact hx (hf0 x hxL)) hLc
  let χ : Tests ℝ Ω := ⟨f, contMDiff_iff_contDiff.mp f.contMDiff,
    hL.of_isClosed_subset isClosed_closure hs, hs.trans hLΩ⟩
  exact ⟨χ, fun x => (hf x).1, fun x => (hf x).2,
    fun x hx => hf1.self_of_nhdsSet x hx⟩

/-- The real part of the restriction to real tests, as an algebraic functional. -/
def realFunctional (u : ScalarDistribution 𝕜 Ω) : Tests ℝ Ω →ₗ[ℝ] ℝ :=
  RCLike.reCLM.toLinearMap.comp ((u.restrictScalars ℝ).toLinearMap.comp
    (TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜)).toLinearMap)

@[simp] theorem realFunctional_apply (u : ScalarDistribution 𝕜 Ω) (φ : Tests ℝ Ω) :
    realFunctional u φ = RCLike.re (u (realTest φ)) := rfl

theorem realFunctional_positive (u : ScalarDistribution 𝕜 Ω) (hu : IsPositive u)
    (φ : Tests ℝ Ω) (hφ : ∀ x, 0 ≤ φ x) : 0 ≤ realFunctional u φ := by
  obtain ⟨r, hr, heq⟩ := hu φ hφ
  simp [realFunctional_apply, heq, hr]

/-- Real positive functionals have positive extensions to C_c. Smooth cutoffs
majorize every continuous compactly supported function; M. Riesz extension
requires no global bound and no compactness of Ω. -/
theorem real_positive_extension (v : Tests ℝ Ω →ₗ[ℝ] ℝ)
    (hv : ∀ φ : Tests ℝ Ω, (∀ x, 0 ≤ φ x) → 0 ≤ v φ) :
    ∃ I : C_c(Ω, ℝ) →ₗ[ℝ] ℝ,
      (∀ f : C_c(Ω, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ I f) ∧
      ∀ φ : Tests ℝ Ω, I (testToCc φ) = v φ := by
  let e := LinearEquiv.ofInjective (testToCc (𝕜 := ℝ) (Ω := Ω)) testToCc_injective
  let p : C_c(Ω, ℝ) →ₗ.[ℝ] ℝ := ⟨_, v.comp e.symm.toLinearMap⟩
  let cone : PointedCone ℝ C_c(Ω, ℝ) :=
    { carrier := {f | ∀ x, 0 ≤ f x}
      zero_mem' := fun _ => le_rfl
      add_mem' := fun hf hg x => add_nonneg (hf x) (hg x)
      smul_mem' := fun c f hf x => mul_nonneg c.property (hf x) }
  obtain ⟨I, hext, hpos⟩ := riesz_extension cone p
    (fun f hf => hv (e.symm f) (by
      intro x
      by_cases hx : x ∈ Ω
      · have he : testToCc (e.symm f) = f.val := LinearEquiv.ofInjective_symm_apply _ _
        have h := DFunLike.congr_fun he ⟨x, hx⟩
        change (e.symm f) x = f.val ⟨x, hx⟩ at h
        rw [h]
        exact hf ⟨x, hx⟩
      · exact le_of_eq ((e.symm f).zero_on_compl hx).symm))
    (by
      intro f
      let K : Set (Domain d) := Subtype.val '' tsupport f
      have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
      obtain ⟨χ, hχ0, _, hχ1⟩ := exists_cutoff K hK (Subtype.coe_image_subset _ _)
      obtain ⟨M, hM⟩ := f.continuous.norm.bddAbove_range_of_hasCompactSupport
        (f.hasCompactSupport.norm)
      let N := max M 0
      let ψ : Tests ℝ Ω := N • χ
      refine ⟨e ψ, ?_⟩
      change ∀ x : Ω, 0 ≤ (testToCc ψ) x + f x
      intro x
      by_cases hx : x ∈ tsupport f
      · have hxK : x.val ∈ K := mem_image_of_mem _ hx
        change 0 ≤ N * χ x.val + f x
        rw [hχ1 _ hxK]
        have hb : ‖f x‖ ≤ M := hM (mem_range_self x)
        have hab : -‖f x‖ ≤ f x := neg_abs_le (f x)
        dsimp [N]
        nlinarith [le_max_left M 0]
      · have hzero : f x = 0 := image_eq_zero_of_notMem_tsupport hx
        change 0 ≤ N * χ x.val + f x
        rw [hzero, add_zero]
        exact mul_nonneg (le_max_right _ _) (hχ0 _))
  refine ⟨I, fun f hf => hpos f hf, fun φ => ?_⟩
  have h := hext (e φ)
  change I (testToCc φ) = v (e.symm (e φ)) at h
  simpa using h

/-- Uniform smooth approximation with a fixed compact support. The stronger
pointwise error estimate is useful for uniqueness of positive extensions. -/
theorem exists_smooth_approximation (f : C_c(Ω, ℝ)) :
    ∃ χ : Tests ℝ Ω, (∀ x, 0 ≤ χ x) ∧
      ∀ ε : ℝ, 0 < ε → ∃ φ : Tests ℝ Ω,
        tsupport φ ⊆ tsupport χ ∧
        ∀ x : Ω, |φ x.val - f x| ≤ ε * χ x.val := by
  let F : Domain d → ℝ := Subtype.val.extend f 0
  have hFc : Continuous F := HasCompactSupport.continuous_extend_zero Ω.isOpen f.continuous f.hasCompactSupport
  have hFcomp : HasCompactSupport F := f.hasCompactSupport.extend_zero continuous_subtype_val
  have hext (x : Ω) : F x.val = f x := by
    exact congrFun (Function.extend_comp Subtype.val_injective f 0) x
  let K := Subtype.val '' tsupport f
  obtain ⟨χ, hχ0, hχle, hχ1⟩ := exists_cutoff K
    (f.hasCompactSupport.image continuous_subtype_val) (Subtype.coe_image_subset _ _)
  refine ⟨χ, hχ0, fun ε hε => ?_⟩
  obtain ⟨g, hgs, hg⟩ := (hFcomp.uniformContinuous_of_continuous hFc).exists_contDiff_dist_le hε
  let φ : Tests ℝ Ω := ⟨fun x => χ x * g x, χ.contDiff.mul hgs,
    χ.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans χ.tsupport_subset⟩
  refine ⟨φ, tsupport_mul_subset_left, fun x => ?_⟩
  have hχf : χ x.val * f x = f x := by
    by_cases hx : x ∈ tsupport f
    · rw [hχ1 _ (mem_image_of_mem _ hx), one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  change |χ x.val * g x.val - f x| ≤ _
  calc
    |χ x.val * g x.val - f x| = |χ x.val * (g x.val - F x.val)| := by rw [hext]; congr 1; nlinarith [hχf]
    _ = χ x.val * |g x.val - F x.val| := by rw [abs_mul, abs_of_nonneg (hχ0 _)]
    _ ≤ χ x.val * ε := mul_le_mul_of_nonneg_left (by simpa [Real.dist_eq] using (hg x.val).le) (hχ0 _)
    _ = ε * χ x.val := mul_comm _ _

/-- Smooth tests determine a positive functional on C_c, even when that
functional is not bounded for the global uniform norm. -/
theorem positive_extensions_unique (I J : C_c(Ω, ℝ) →ₗ[ℝ] ℝ)
    (hI : ∀ f : C_c(Ω, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ I f)
    (hJ : ∀ f : C_c(Ω, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ J f)
    (hagree : ∀ φ : Tests ℝ Ω, I (testToCc φ) = J (testToCc φ)) : I = J := by
  let Λ : C_c(Ω, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ I hI
  let Γ : C_c(Ω, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ J hJ
  ext f
  obtain ⟨χ, hχ0, happ⟩ := exists_smooth_approximation f
  let a := I (testToCc χ) + J (testToCc χ)
  have ha : 0 ≤ a := add_nonneg (hI _ (fun x => hχ0 _)) (hJ _ (fun x => hχ0 _))
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm ?_ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := δ / (a + 1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  obtain ⟨φ, _, hφ⟩ := happ ε hε
  have hfφ : f ≤ testToCc φ + ε • testToCc χ := by
    intro x
    have h := (abs_le.mp (hφ x)).1
    change f x ≤ φ x.val + ε * χ x.val
    linarith
  have hφf : testToCc φ ≤ f + ε • testToCc χ := by
    intro x
    have h := (abs_le.mp (hφ x)).2
    change φ x.val ≤ f x + ε * χ x.val
    linarith
  have h1 : I f ≤ I (testToCc φ) + ε * I (testToCc χ) := by
    simpa [Λ, PositiveLinearMap.mk₀] using Λ.monotone hfφ
  have h2 : I (testToCc φ) ≤ I f + ε * I (testToCc χ) := by
    simpa [Λ, PositiveLinearMap.mk₀] using Λ.monotone hφf
  have h3 : J f ≤ J (testToCc φ) + ε * J (testToCc χ) := by
    simpa [Γ, PositiveLinearMap.mk₀] using Γ.monotone hfφ
  have h4 : J (testToCc φ) ≤ J f + ε * J (testToCc χ) := by
    simpa [Γ, PositiveLinearMap.mk₀] using Γ.monotone hφf
  have hb : |I f - J f| ≤ ε * a := abs_le.mpr ⟨by rw [hagree φ] at h2; dsimp [a]; nlinarith,
    by rw [hagree φ] at h1; dsimp [a]; nlinarith⟩
  have heq : ε * (a + 1) = δ := div_mul_cancel₀ δ (by linarith)
  linarith

/-- Positivity forces the restriction to every real test to be real-valued. -/
theorem real_value (u : ScalarDistribution 𝕜 Ω) (hu : IsPositive u)
    (φ : Tests ℝ Ω) : u (realTest φ) = (realFunctional u φ : 𝕜) := by
  obtain ⟨χ, hχ0, _, hχ1⟩ := exists_cutoff (tsupport φ) φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨B, hB⟩ := φ.continuous.norm.bddAbove_range_of_hasCompactSupport φ.hasCompactSupport.norm
  let M := max B 0
  have hpos : ∀ x, 0 ≤ (M • χ + φ) x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · change 0 ≤ M * χ x + φ x
      rw [hχ1 x hx]
      have hb : ‖φ x‖ ≤ B := hB (mem_range_self x)
      have hab : -‖φ x‖ ≤ φ x := neg_abs_le (φ x)
      dsimp [M]
      nlinarith [le_max_left B 0]
    · change 0 ≤ M * χ x + φ x
      rw [image_eq_zero_of_notMem_tsupport hx, add_zero]
      exact mul_nonneg (le_max_right _ _) (hχ0 x)
  obtain ⟨r, _, hr⟩ := hu χ hχ0
  obtain ⟨s, _, hs⟩ := hu (M • χ + φ) hpos
  have hlin : u (realTest (M • χ + φ)) = (M : 𝕜) * u (realTest χ) + u (realTest φ) := by
    have heq : realTest (𝕜 := 𝕜) (M • χ + φ) = (M : 𝕜) • realTest χ + realTest φ := by
      ext x
      simp [realTest_apply, RCLike.ofReal_add, RCLike.ofReal_mul]
    rw [heq, map_add, map_smul, smul_eq_mul]
  have heq : u (realTest φ) = ((s - M * r : ℝ) : 𝕜) := by
    rw [hs, hr] at hlin
    push_cast
    linear_combination hlin.symm
  rw [heq, realFunctional_apply, heq]
  simp

/-- The positive extension is unique and agrees with the original scalar-linear
functional, including its imaginary part on real-valued tests. -/
theorem positive_extension : Specs.ExpandedFA.PartIV.PositiveDistributions.extensionType := by
  intro 𝕜 _ d Ω u hu
  obtain ⟨I, hI, hext⟩ := real_positive_extension (realFunctional u) (realFunctional_positive u hu)
  have hpair (φ : Tests ℝ Ω) : u (realTest φ) = (I (testToCc φ) : 𝕜) := by
    rw [hext]
    exact real_value u hu φ
  refine ⟨I, ⟨hI, hpair⟩, ?_⟩
  intro J hJ
  exact positive_extensions_unique J I hJ.1 hI (fun φ =>
    RCLike.ofReal_injective ((hJ.2 φ).symm.trans (hpair φ)))

/-- The real and imaginary parts of a scalar test are again genuine smooth
tests on the same domain. Their usual scalar decomposition has no conjugation. -/
theorem test_re_add_im (φ : Tests 𝕜 Ω) :
    φ = realTest (TestFunction.postcompCLM (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) φ) +
      (RCLike.I : 𝕜) • realTest (TestFunction.postcompCLM (RCLike.imCLM : 𝕜 →L[ℝ] ℝ) φ) := by
  ext x
  change φ x = (RCLike.re (φ x) : 𝕜) + RCLike.I * (RCLike.im (φ x) : 𝕜)
  rw [mul_comm, RCLike.re_add_im]

/-- A positive distribution has a unique positive Radon representative.
The measure is on Ω itself and is only required to be finite on compacts. -/
theorem exists_unique_representing_measure (u : ScalarDistribution 𝕜 Ω) (hu : IsPositive u) :
    ∃! μ : Measure Ω, Represents μ u := by
  obtain ⟨I, ⟨hIpos, hItest⟩, hIunique⟩ := positive_extension 𝕜 d Ω u hu
  obtain ⟨μ, ⟨hμ, hμrep⟩, hμunique⟩ :=
    ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positive_radon_representation Ω I hIpos
  have : μ.Regular :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular μ).mp hμ
  have hrep : Represents μ u := by
    refine ⟨hμ, fun φ => ⟨(testToCc φ).integrable, ?_⟩⟩
    let r := TestFunction.postcompCLM (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) φ
    let i := TestFunction.postcompCLM (RCLike.imCLM : 𝕜 →L[ℝ] ℝ) φ
    have hp : u φ = u (realTest r) + (RCLike.I : 𝕜) * u (realTest i) := by
      conv_lhs => rw [test_re_add_im φ]
      rw [map_add, map_smul, smul_eq_mul]
    rw [hp, hItest r, hItest i, (hμrep (testToCc r)).2, (hμrep (testToCc i)).2, mul_comm]
    exact integral_re_add_im (testToCc φ).integrable
  refine ⟨μ, hrep, fun ν hν => ?_⟩
  have : ν.Regular :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular ν).mp hν.1
  let J : C_c(Ω, ℝ) →ₗ[ℝ] ℝ := (CompactlySupportedContinuousMap.integralPositiveLinearMap ν).toLinearMap
  have hJ : J = I := hIunique J ⟨fun f hf => integral_nonneg hf, fun φ => by
    rw [(hν.2 (realTest φ)).2]
    change (∫ x : Ω, (φ x.val : 𝕜) ∂ν) = (∫ x : Ω, φ x.val ∂ν : ℝ)
    exact integral_ofReal⟩
  apply hμunique ν
  refine ⟨hν.1, fun f => ⟨f.integrable, ?_⟩⟩
  change I f = J f
  rw [hJ]

/-- The local integral estimate uses only the mass of the support compact. -/
theorem norm_test_integral_le (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ]
    (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω)
    (φ : Tests 𝕜 Ω) (hs : tsupport φ ⊆ K) (M : ℝ) (hM : ∀ x, ‖φ x‖ ≤ M) :
    ‖∫ x : Ω, φ x.val ∂μ‖ ≤ μ.real (Subtype.val ⁻¹' (K : Set (Domain d))) * M := by
  let S : Set Ω := Subtype.val ⁻¹' (K : Set (Domain d))
  have hSc : IsCompact S := Topology.IsInducing.subtypeVal.isCompact_preimage'
    K.isCompact (by simpa using hK)
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hSc.measure_lt_top.ne
  have heq : (∫ x in S, φ x.val ∂μ) = ∫ x : Ω, φ x.val ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
  rw [← heq]
  have h := norm_integral_le_of_norm_le_const (μ := μ.restrict S)
    (Eventually.of_forall fun x : Ω => hM x.val)
  simpa only [measureReal_restrict_apply_univ, mul_comm] using h

/-- The actual integral is scalar-linear on the original test space. -/
def measureTestLM (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ] : Tests 𝕜 Ω →ₗ[𝕜] 𝕜 where
  toFun φ := ∫ x : Ω, φ x.val ∂μ
  map_add' φ ψ := integral_add (testToCc φ).integrable (testToCc ψ).integrable
  map_smul' c φ := integral_smul c (fun x : Ω => φ x.val)

/-- A compact-finite measure gives an LF-continuous scalar-linear distribution.
The zero-order compact-step bound establishes continuity, not an assumed bound
or a finite-total-mass restriction. -/
def measureDistribution (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ] : ScalarDistribution 𝕜 Ω :=
  { measureTestLM μ with
    cont := (finite_order_criterion 𝕜 d Ω (measureTestLM μ)).mpr (fun K hK =>
      ⟨μ.real (Subtype.val ⁻¹' (K : Set (Domain d))), ENNReal.toReal_nonneg, 0, fun φ => by
        apply norm_test_integral_le μ K hK (TestFunction.ofSupportedIn hK φ) φ.tsupport_subset
        intro x
        have h := (step_seminorm_formula 𝕜 d K 0 φ _ (apply_nonneg _ _)).mp le_rfl
          0 le_rfl Fin.elim0 x
        simpa using h⟩) }

@[simp] theorem measureDistribution_apply (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ]
    (φ : Tests 𝕜 Ω) : measureDistribution μ φ = ∫ x : Ω, φ x.val ∂μ := rfl

/-- Positivity of the integral, with an explicitly real nonnegative value. -/
theorem positive_of_represents {μ : Measure Ω} {u : ScalarDistribution 𝕜 Ω}
    (hu : Represents μ u) : IsPositive u := by
  intro φ hφ
  refine ⟨∫ x : Ω, φ x.val ∂μ, integral_nonneg (fun x => hφ x.val), ?_⟩
  rw [(hu.2 (realTest φ)).2]
  exact integral_ofReal

theorem measure_distribution : Specs.ExpandedFA.PartIV.PositiveDistributions.converseType := by
  intro 𝕜 _ d Ω μ hμ
  have : μ.Regular :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular μ).mp hμ
  let u : ScalarDistribution 𝕜 Ω := measureDistribution μ
  have hrep : Represents μ u := ⟨hμ, fun φ => ⟨(testToCc φ).integrable, rfl⟩⟩
  exact ⟨u, positive_of_represents hrep, hrep⟩

/-- The manuscript's complete characterization. -/
theorem positivity_iff_unique_measure :
    Specs.ExpandedFA.PartIV.PositiveDistributions.characterizationType := by
  intro 𝕜 _ d Ω u
  exact ⟨exists_unique_representing_measure u, fun h => positive_of_represents h.choose_spec.1⟩

/-- The constant is exactly the measure of the support compact (in Ω). -/
theorem local_order_zero : Specs.ExpandedFA.PartIV.PositiveDistributions.localOrderZeroType := by
  intro 𝕜 _ d Ω u hu K hK
  obtain ⟨μ, hμ, _⟩ := exists_unique_representing_measure u hu
  have : μ.Regular :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular μ).mp hμ.1
  refine ⟨μ.real (Subtype.val ⁻¹' (K : Set (Domain d))), ENNReal.toReal_nonneg, ?_⟩
  intro φ hs M _ hM
  rw [(hμ.2 φ).2]
  exact norm_test_integral_le μ K hK φ hs M hM

/-- Integration against the representing measure gives the full scalar-linear
extension to C_c. This also covers complex-valued continuous functions. -/
theorem scalar_extension : Specs.ExpandedFA.PartIV.PositiveDistributions.scalarExtensionType := by
  intro 𝕜 _ d Ω u hu
  obtain ⟨μ, hμ, _⟩ := exists_unique_representing_measure u hu
  have : μ.Regular :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular μ).mp hμ.1
  let I : C_c(Ω, 𝕜) →ₗ[𝕜] 𝕜 :=
    { toFun f := ∫ x, f x ∂μ
      map_add' f g := integral_add f.integrable g.integrable
      map_smul' c f := integral_smul c f }
  refine ⟨I, fun φ => (hμ.2 φ).2.symm, fun f hf => ?_⟩
  exact ⟨∫ x, f x ∂μ, integral_nonneg hf, integral_ofReal⟩

end ExpandedFA.PartIV.PositiveDistributions
