import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionLocalizationAndGluing
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionCalculus

open Set TopologicalSpace Function
open scoped Distributions Topology ContDiff NNReal

set_option maxHeartbeats 1000000

namespace ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

theorem seminorm_sum_apply {E : Type*} [AddCommGroup E] [Module 𝕜 E] {ι : Type*}
    (s : Finset ι) (p : ι → Seminorm 𝕜 E) (x : E) :
    (∑ i ∈ s, p i) x = ∑ i ∈ s, p i x :=
  map_sum (show Seminorm 𝕜 E →+ ℝ from
    ⟨⟨fun p => p x, rfl⟩, fun _ _ => rfl⟩) p s

theorem smooth_withSeminorms : WithSeminorms (smoothSeminorm 𝕜 Ω) := ⟨rfl⟩

instance : IsTopologicalAddGroup (SmoothFunctions 𝕜 Ω) := smooth_withSeminorms.isTopologicalAddGroup
instance : ContinuousSMul 𝕜 (SmoothFunctions 𝕜 Ω) := smooth_withSeminorms.continuousSMul
instance : ContinuousSMul ℝ (SmoothFunctions 𝕜 Ω) :=
  ⟨by
    have heq : (fun p : ℝ × SmoothFunctions 𝕜 Ω => p.1 • p.2) =
        (fun p => (p.1 : 𝕜) • p.2) := by
      funext p
      apply Subtype.ext
      funext x
      exact RCLike.real_smul_eq_coe_mul _ _
    rw [heq]
    exact (show Continuous (fun p : ℝ × SmoothFunctions 𝕜 Ω => (p.1 : 𝕜)) from
      RCLike.continuous_ofReal.comp continuous_fst).smul continuous_snd⟩
instance : LocallyConvexSpace ℝ (SmoothFunctions 𝕜 Ω) :=
  smooth_withSeminorms.toLocallyConvexSpace

/-- A derivative evaluation is bounded by its compact-local seminorm. -/
theorem norm_smooth_derivative_le (q : SmoothJetIndex Ω) (f : SmoothFunctions 𝕜 Ω)
    (x : Domain d) (hx : x ∈ q.1.val) :
    ‖iteratedFDeriv ℝ q.2 f.val x‖ ≤ smoothSeminorm 𝕜 Ω q f :=
  ContinuousMap.norm_coe_le_norm (smoothJetLM 𝕜 Ω q f) ⟨x, hx⟩

/-- All locally smooth functions have a unique normalized representative. -/
theorem smooth_representatives :
    Specs.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual.representativesType := by
  classical
  intro 𝕜 _ d Ω f hf
  let g : Domain d → 𝕜 := fun x => if x ∈ Ω then f x else 0
  have hgf : EqOn g f Ω := fun x hx => ite_eq_left hx
  let G : SmoothFunctions 𝕜 Ω := ⟨g, hf.congr hgf, fun x hx => ite_eq_right hx⟩
  refine ⟨G, hgf, ?_⟩
  intro H hH
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ Ω
  · exact (hH hx).trans (hgf hx).symm
  · exact (H.property.2 hx).trans (G.property.2 hx).symm

/-- A coordinate partial is bounded by the full operator derivative. -/
theorem smoothCoordinateSeminorm_le (a : SmoothCoordinateIndex Ω) :
    smoothCoordinateSeminorm 𝕜 Ω a ≤ smoothSeminorm 𝕜 Ω a.1 := by
  intro f
  apply (ContinuousMap.norm_le _ (apply_nonneg _ _)).mpr
  intro x
  change ‖iteratedFDeriv ℝ a.1.2 f.val x (fun j => coordinateVector (a.2 j))‖ ≤ _
  calc
    _ ≤ ‖iteratedFDeriv ℝ a.1.2 f.val x‖ * ∏ j, ‖coordinateVector (a.2 j)‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ a.1.2 f.val x‖ := by simp [coordinateVector, Pi.norm_single]
    _ ≤ _ := norm_smooth_derivative_le a.1 f x x.property

/-- Coordinate partials generate precisely the natural local smooth topology. -/
theorem smooth_coordinate_topology :
    Specs.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual.coordinateTopologyType := by
  classical
  intro 𝕜 _ d Ω
  apply (smooth_withSeminorms (𝕜 := 𝕜) (Ω := Ω)).congr
  · intro a
    refine ⟨{a.1}, 1, ?_⟩
    rw [one_smul, Finset.sup_singleton]
    exact smoothCoordinateSeminorm_le a
  · intro q
    let s : Finset (SmoothCoordinateIndex Ω) :=
      Finset.univ.image fun a : Fin q.2 → Fin d => ⟨q, a⟩
    refine ⟨s, (d : ℝ≥0) ^ q.2, ?_⟩
    intro f
    change ‖smoothJetLM 𝕜 Ω q f‖ ≤
      (d : ℝ) ^ q.2 * (s.sup (smoothCoordinateSeminorm 𝕜 Ω)) f
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    apply norm_multilinear_le_coordinate_bound _ _ (apply_nonneg _ _)
    intro a
    calc
      _ ≤ smoothCoordinateSeminorm 𝕜 Ω ⟨q, a⟩ f :=
        ContinuousMap.norm_coe_le_norm
          (((coordinateEvaluation 𝕜 a).compLeftContinuous 𝕜 q.1.val) (smoothJetLM 𝕜 Ω q f)) x
      _ ≤ _ := Seminorm.le_finset_sup_apply (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)

/-- The inclusion from any compact test step is continuous for all local derivatives. -/
noncomputable def stepToSmoothCLM (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω) :
    Step 𝕜 K →L[𝕜] SmoothFunctions 𝕜 Ω where
  toLinearMap := (testToSmoothLM 𝕜 Ω).comp (TestFunction.ofSupportedInCLM 𝕜 hK).toLinearMap
  cont := by
    apply WithSeminorms.continuous_of_continuous_comp smooth_withSeminorms
    intro q
    apply Seminorm.continuous_of_le
      ((ContDiffMapSupportedIn.withSeminorms 𝕜 (Domain d) 𝕜 ⊤ K).continuous_seminorm q.2)
    intro φ
    change ‖smoothJetLM 𝕜 Ω q (testToSmoothLM 𝕜 Ω (TestFunction.ofSupportedIn hK φ))‖ ≤ _
    apply (ContinuousMap.norm_le _ (apply_nonneg _ _)).mpr
    intro x
    exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜

/-- The LF inclusion into the space of smooth functions is continuous. -/
noncomputable def testToSmoothCLM : Tests 𝕜 Ω →L[𝕜] SmoothFunctions 𝕜 Ω :=
  TestFunction.limitCLM 𝕜 (testToSmoothLM 𝕜 Ω)
    (fun K hK => stepToSmoothCLM K hK) (fun _ _ _ => rfl)

@[simp] theorem testToSmoothCLM_apply (φ : Tests 𝕜 Ω) :
    testToSmoothCLM φ = testToSmoothLM 𝕜 Ω φ := rfl

/-- A smooth function zero near a compact set has zero derivative seminorm there. -/
theorem smoothSeminorm_eq_zero_of_eqOn (q : SmoothJetIndex Ω) (f : SmoothFunctions 𝕜 Ω)
    (V : Set (Domain d)) (hV : IsOpen V) (hKV : (q.1.val : Set (Domain d)) ⊆ V)
    (hf : EqOn f.val 0 V) : smoothSeminorm 𝕜 Ω q f = 0 := by
  change ‖smoothJetLM 𝕜 Ω q f‖ = 0
  have hz : smoothJetLM 𝕜 Ω q f = 0 := by
    apply ContinuousMap.ext
    intro x
    change iteratedFDeriv ℝ q.2 f.val x = 0
    have heq : f.val =ᶠ[𝓝 (x : Domain d)] 0 :=
      Filter.eventuallyEq_of_mem (hV.mem_nhds (hKV x.property)) hf
    rw [(heq.iteratedFDeriv ℝ q.2).self_of_nhds]
    simp
  rw [hz]
  change dist (0 : C(q.1.val, (Domain d) [×q.2]→L[ℝ] 𝕜)) 0 = 0
  exact dist_self _

/-- Every continuous smooth functional depends on the germ near one compact subset
of Ω. This is derived from continuity, without a finite-order assumption. -/
theorem smooth_functional_locality (L : SmoothFunctions 𝕜 Ω →L[𝕜] 𝕜) :
    ∃ K : Compacts (Domain d), (K : Set (Domain d)) ⊆ Ω ∧
      ∀ (f : SmoothFunctions 𝕜 Ω) (V : Set (Domain d)), IsOpen V →
        (K : Set (Domain d)) ⊆ V → EqOn f.val 0 V → L f = 0 := by
  classical
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous smooth_withSeminorms
    ((normSeminorm 𝕜 𝕜).comp L.toLinearMap) L.continuous.norm
  let K : Compacts (Domain d) := s.sup fun q => q.1.val
  have hq (q : SmoothJetIndex Ω) (hq : q ∈ s) : q.1.val ≤ K :=
    Finset.le_sup (f := fun q : SmoothJetIndex Ω => q.1.val) hq
  have hKO : (K : Set (Domain d)) ⊆ Ω := by
    intro x hx
    simp only [K, Compacts.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion] at hx
    obtain ⟨q, hq, hx⟩ := hx
    exact q.1.property hx
  refine ⟨K, hKO, ?_⟩
  intro f V hV hKV hf
  have hz : (s.sup (smoothSeminorm 𝕜 Ω)) f = 0 := by
    apply le_antisymm _ (apply_nonneg _ _)
    exact Seminorm.finset_sup_apply_le (by norm_num) fun q hqs => by
      rw [smoothSeminorm_eq_zero_of_eqOn q f V hV (fun x hx => hKV (hq q hqs hx)) hf]
  have hb := hC f
  change ‖L f‖ ≤ (C : ℝ) * (s.sup (smoothSeminorm 𝕜 Ω)) f at hb
  rw [hz, mul_zero] at hb
  exact norm_le_zero_iff.mp hb

/-- Restricting a continuous smooth functional gives a compactly supported distribution. -/
theorem compact_dual_converse :
    Specs.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual.converseType := by
  intro 𝕜 _ d Ω L
  let u : ScalarDistribution 𝕜 Ω := L.comp testToSmoothCLM
  obtain ⟨K, hKO, hK⟩ := smooth_functional_locality L
  have hs : distributionSupport u ⊆ K := by
    intro x hx
    by_contra hxK
    apply hx.2
    let V : Set (Domain d) := (Ω : Set (Domain d)) ∩ (K : Set (Domain d))ᶜ
    have hV : IsOpen V := Ω.isOpen.inter K.isCompact.isClosed.isOpen_compl
    refine Set.mem_sUnion.mpr ⟨V, ⟨hV, inter_subset_left, ?_⟩, hx.1, hxK⟩
    intro φ hφ
    change L (testToSmoothLM 𝕜 Ω φ) = 0
    apply hK _ (tsupport φ)ᶜ isClosed_closure.isOpen_compl
    · intro y hy hyφ
      exact (hφ hyφ).2 hy
    · intro y hy
      exact image_eq_zero_of_notMem_tsupport hy
  have heq : distributionSupport u = (K : Set (Domain d)) \ vanishingRegion u := by
    ext x
    exact ⟨fun hx => ⟨hs hx, hx.2⟩, fun hx => ⟨hKO hx.1, hx.2⟩⟩
  refine ⟨u, fun _ => rfl, ?_⟩
  rw [heq]
  exact K.isCompact.diff (support_vanishing 𝕜 d Ω u).1

/-- Multiplication by a fixed scalar test places any locally smooth function in
one fixed compact step. -/
noncomputable def smoothCutoffLM (χ : Tests 𝕜 Ω) :
    SmoothFunctions 𝕜 Ω →ₗ[𝕜] Step 𝕜 ⟨tsupport χ, χ.hasCompactSupport⟩ where
  toFun f := .of_support_subset (smooth_mul_test ⟨f.val, f.property.1⟩ χ)
    ((support_mul_subset_right (f := f.val) (g := (χ : Domain d → 𝕜))).trans subset_closure)
  map_add' f g := by ext x; exact add_mul _ _ _
  map_smul' c f := by ext x; exact mul_assoc _ _ _

@[simp] theorem smoothCutoffLM_apply (χ : Tests 𝕜 Ω) (f : SmoothFunctions 𝕜 Ω) (x) :
    smoothCutoffLM χ f x = f.val x * χ x := rfl

/-- A fixed cutoff is a continuous operator from the local smooth topology to
its compact step. The finite Leibniz bound controls every derivative. -/
theorem continuous_smoothCutoffLM (χ : Tests 𝕜 Ω) : Continuous (smoothCutoffLM χ) := by
  classical
  let K : Compacts (Domain d) := ⟨tsupport χ, χ.hasCompactSupport⟩
  let q (i : ℕ) : SmoothJetIndex Ω := (⟨K, χ.tsupport_subset⟩, i)
  let B := (ContinuousLinearMap.mul 𝕜 𝕜).bilinearRestrictScalars ℝ
  apply WithSeminorms.continuous_of_continuous_comp
    (ContDiffMapSupportedIn.withSeminorms 𝕜 (Domain d) 𝕜 ⊤ K)
  intro n
  let A (i : ℕ) : ℝ≥0 :=
    ⟨‖B‖ * (n.choose i : ℝ) *
      ContDiffMapSupportedIn.seminorm 𝕜 (Domain d) 𝕜 ⊤ K (n-i)
        (ContDiffMapSupportedIn.of_support_subset χ.contDiff subset_closure), by positivity⟩
  let P : Seminorm 𝕜 (SmoothFunctions 𝕜 Ω) :=
    ∑ i ∈ Finset.range (n+1), A i • smoothSeminorm 𝕜 Ω (q i)
  have hP : Continuous P := by
    change Continuous (fun f => P f)
    simp only [P, seminorm_sum_apply, _root_.smul_apply]
    exact continuous_finsetSum _ fun i _ =>
      (smooth_withSeminorms.continuous_seminorm (q i)).const_smul (A i)
  apply Seminorm.continuous_of_le hP
  intro f
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff 𝕜 (apply_nonneg P f) n _).mpr
  intro x hx
  have hbound := B.norm_iteratedFDerivWithin_le_of_bilinear f.property.1
    χ.contDiff.contDiffOn Ω.isOpen.uniqueDiffOn (χ.tsupport_subset hx) (n := n) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ Ω.isOpen (χ.tsupport_subset hx)] at hbound
  change ‖iteratedFDeriv ℝ n (fun y => f.val y * χ y) x‖ ≤ P f
  calc
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f.val x‖ * ‖iteratedFDeriv ℝ (n-i) χ x‖ := hbound
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        smoothSeminorm 𝕜 Ω (q i) f *
        ContDiffMapSupportedIn.seminorm 𝕜 (Domain d) 𝕜 ⊤ K (n-i)
          (ContDiffMapSupportedIn.of_support_subset χ.contDiff subset_closure) := by
      gcongr with i hi
      · exact norm_smooth_derivative_le (q i) f x hx
      · exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜
          (f := (ContDiffMapSupportedIn.of_support_subset χ.contDiff subset_closure : Step 𝕜 K))
    _ = P f := by
      simp only [P, seminorm_sum_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      change ‖B‖ * ((n.choose i : ℝ) * smoothSeminorm 𝕜 Ω (q i) f *
        ContDiffMapSupportedIn.seminorm 𝕜 (Domain d) 𝕜 ⊤ K (n-i)
          (ContDiffMapSupportedIn.of_support_subset χ.contDiff subset_closure)) =
        (‖B‖ * (n.choose i : ℝ) *
        ContDiffMapSupportedIn.seminorm 𝕜 (Domain d) 𝕜 ⊤ K (n-i)
          (ContDiffMapSupportedIn.of_support_subset χ.contDiff subset_closure)) *
        smoothSeminorm 𝕜 Ω (q i) f
      ring

noncomputable def smoothCutoffCLM (χ : Tests 𝕜 Ω) : SmoothFunctions 𝕜 Ω →L[𝕜] Tests 𝕜 Ω :=
  (TestFunction.ofSupportedInCLM 𝕜 χ.tsupport_subset).comp
    ⟨smoothCutoffLM χ, continuous_smoothCutoffLM χ⟩

@[simp] theorem smoothCutoffCLM_apply (χ : Tests 𝕜 Ω) (f : SmoothFunctions 𝕜 Ω) (x) :
    smoothCutoffCLM χ f x = f.val x * χ x := rfl

/-- A real cutoff regarded as a scalar test function. -/
noncomputable def scalarCutoff (𝕜 : Type) [RCLike 𝕜] (χ : Tests ℝ Ω) : Tests 𝕜 Ω where
  toFun x := (χ x : 𝕜)
  contDiff' := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp χ.contDiff
  hasCompactSupport' := χ.hasCompactSupport.comp_left (by simp)
  tsupport_subset' := (tsupport_comp_subset (g := (RCLike.ofReal : ℝ → 𝕜))
    (by simp) χ).trans χ.tsupport_subset

@[simp] theorem scalarCutoff_apply (χ : Tests ℝ Ω) (x) : scalarCutoff 𝕜 χ x = (χ x : 𝕜) := rfl

/-- A compactly supported distribution acts on every smooth function by cutting
it off. All cutoffs equal to one near the support give the same value. -/
theorem compact_dual_cutoff_formula :
    Specs.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual.cutoffFormulaType := by
  intro 𝕜 _ d Ω u hu
  obtain ⟨χ, V, hV, huV, hχ⟩ := cutoff_existence d Ω (distributionSupport u) hu sdiff_subset
  let L : SmoothFunctions 𝕜 Ω →L[𝕜] 𝕜 := u.comp (smoothCutoffCLM (scalarCutoff 𝕜 χ))
  have hext (φ : Tests 𝕜 Ω) : L (testToSmoothLM 𝕜 Ω φ) = u φ := by
    apply pairing_locality 𝕜 d Ω u _ φ V hV huV
    intro x hx
    change φ x * (χ x : 𝕜) = φ x
    rw [hχ hx]
    simp
  refine ⟨L, hext, ?_⟩
  intro η W hW huW hη f
  refine ⟨smoothCutoffCLM η f, fun x => mul_comm _ _, ?_⟩
  apply pairing_locality 𝕜 d Ω u _ _ (V ∩ W) (hV.inter hW) (subset_inter huV huW)
  intro x hx
  change f.val x * (χ x : 𝕜) = f.val x * η x
  rw [hχ hx.1, hη hx.2]
  simp

/-- The extension is unique among all continuous smooth functionals. Continuity
of a competing functional supplies a compact controlling its kernel. -/
theorem compact_dual_extension :
    Specs.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual.extensionType := by
  intro 𝕜 _ d Ω u hu
  obtain ⟨L, hL, hformula⟩ := compact_dual_cutoff_formula 𝕜 d Ω u hu
  refine ⟨L, hL, ?_⟩
  intro M hM
  obtain ⟨K, hKO, hK⟩ := smooth_functional_locality M
  obtain ⟨η, W, hW, hSW, hη⟩ := cutoff_existence d Ω
    (distributionSupport u ∪ (K : Set (Domain d))) (hu.union K.isCompact)
    (union_subset sdiff_subset hKO)
  have huW : distributionSupport u ⊆ W := subset_union_left.trans hSW
  have hKW : (K : Set (Domain d)) ⊆ W := subset_union_right.trans hSW
  ext f
  let ψ := smoothCutoffCLM (scalarCutoff 𝕜 η) f
  have hz : M (f - testToSmoothLM 𝕜 Ω ψ) = 0 := by
    apply hK _ W hW hKW
    intro x hx
    change f.val x - f.val x * (η x : 𝕜) = 0
    rw [hη hx]
    simp
  have hMf : M f = u ψ := by
    rw [map_sub, sub_eq_zero] at hz
    rw [hz, hM]
  have hηscalar : EqOn (scalarCutoff 𝕜 η) 1 W := by
    intro x hx
    change (η x : 𝕜) = 1
    rw [hη hx]
    simp
  obtain ⟨ψ', hψ', hLf⟩ := hformula (scalarCutoff 𝕜 η) W hW huW hηscalar f
  have hψ : ψ' = ψ := by
    ext x
    exact (hψ' x).trans (mul_comm _ _)
  rw [hMf, hLf, hψ]

/-- Point evaluation, linear in the original scalar field. -/
noncomputable def scalarDirac (a : Domain d) : ScalarDistribution 𝕜 Ω where
  toFun φ := φ a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const a

@[simp] theorem scalarDirac_apply (a : Domain d) (φ : Tests 𝕜 Ω) :
    scalarDirac a φ = φ a := rfl

/-- The actual coordinate derivative of the Dirac distribution at zero on ℝ. -/
noncomputable def scalarDiracPrime (𝕜 : Type) [RCLike 𝕜] :
    ScalarDistribution 𝕜 (⊤ : Opens (Domain 1)) :=
  -(scalarDirac (𝕜 := 𝕜) (Ω := ⊤) 0).comp (testPartialCLM [0])

@[simp] theorem scalarDiracPrime_apply (φ : Tests 𝕜 (⊤ : Opens (Domain 1))) :
    scalarDiracPrime 𝕜 φ = -fderiv ℝ φ 0 (coordinateVector 0) := by
  change -(testPartialCLM [0] φ) 0 = _
  rw [testPartial_single_apply]

noncomputable def coordinateScalarCLM (𝕜 : Type) [RCLike 𝕜] : Domain 1 →L[ℝ] 𝕜 :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).comp (ContinuousLinearMap.proj 0)

@[simp] theorem coordinateScalarCLM_apply (x : Domain 1) : coordinateScalarCLM 𝕜 x = (x 0 : 𝕜) := rfl

/-- Exact multiplication identity, using the ordinary product derivative. -/
theorem coordinate_mul_diracPrime :
    (scalarDiracPrime 𝕜).comp
      (multiplyTest (coordinateScalarCLM 𝕜) (coordinateScalarCLM 𝕜).contDiff) =
    -(scalarDirac (𝕜 := 𝕜) (Ω := (⊤ : Opens (Domain 1))) 0) := by
  ext φ
  change -fderiv ℝ (fun x => φ x * coordinateScalarCLM 𝕜 x) 0 (coordinateVector 0) = -φ 0
  rw [show (fun x => φ x * coordinateScalarCLM 𝕜 x) =
    (φ : Domain 1 → 𝕜) * coordinateScalarCLM 𝕜 from rfl]
  rw [fderiv_mul (φ.contDiff.differentiable (by simp) 0)
    ((coordinateScalarCLM 𝕜).differentiable 0)]
  simp [coordinateScalarCLM, coordinateVector]

/-- Every point of an open set admits a scalar test equal to one at that point. -/
theorem exists_test_eq_one (a : Domain d) (ha : a ∈ Ω) :
    ∃ φ : Tests 𝕜 Ω, φ a = 1 := by
  obtain ⟨χ, V, hV, hKV, hχ⟩ := cutoff_existence d Ω {a} isCompact_singleton
    (singleton_subset_iff.mpr ha)
  exact ⟨scalarCutoff 𝕜 χ, by change (χ a : 𝕜) = 1; rw [hχ (hKV (mem_singleton a))]; simp⟩

/-- The derivative of delta has the exact support {0}. -/
theorem scalarDiracPrime_support : distributionSupport (scalarDiracPrime 𝕜) = {0} := by
  apply subset_antisymm
  · intro x hx
    by_contra hx0
    apply hx.2
    refine Set.mem_sUnion.mpr ⟨({0} : Set (Domain 1))ᶜ,
      ⟨isClosed_singleton.isOpen_compl, subset_univ _, ?_⟩, hx0⟩
    intro φ hφ
    have h0 : (0 : Domain 1) ∉ tsupport φ := fun h => hφ h (mem_singleton 0)
    have heq : (φ : Domain 1 → 𝕜) =ᶠ[𝓝 0] 0 := notMem_tsupport_iff_eventuallyEq.mp h0
    rw [scalarDiracPrime_apply, heq.fderiv_eq]
    simp
  · intro x hx
    have hx0 : x = 0 := mem_singleton_iff.mp hx
    subst x
    refine ⟨mem_univ _, ?_⟩
    intro h0
    let U : Opens (Domain 1) :=
      ⟨vanishingRegion (scalarDiracPrime 𝕜), (support_vanishing 𝕜 1 ⊤ (scalarDiracPrime 𝕜)).1⟩
    obtain ⟨χ, hχ⟩ := exists_test_eq_one (𝕜 := 𝕜) (Ω := U) 0 h0
    let χ₀ : Tests 𝕜 (⊤ : Opens (Domain 1)) := rehomeTest χ (subset_univ _)
    let ψ := multiplyTest (coordinateScalarCLM 𝕜) (coordinateScalarCLM 𝕜).contDiff χ₀
    have hψ : tsupport ψ ⊆ vanishingRegion (scalarDiracPrime 𝕜) :=
      (tsupport_mul_subset_left).trans χ.tsupport_subset
    have hz := (support_vanishing 𝕜 1 ⊤ (scalarDiracPrime 𝕜)).2.2 ψ hψ
    have hv : scalarDiracPrime 𝕜 ψ = -1 := by
      have hid := congrArg (fun T : ScalarDistribution 𝕜 (⊤ : Opens (Domain 1)) => T χ₀)
        (coordinate_mul_diracPrime (𝕜 := 𝕜))
      change scalarDiracPrime 𝕜 ψ = -χ 0 at hid
      simpa [hχ] using hid
    rw [hv] at hz
    exact neg_ne_zero.mpr one_ne_zero hz

/-- Vanishing pointwise on the support does not suffice to annihilate a distribution. -/
theorem delta_support_counterexample :
    Specs.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual.deltaCounterexampleType := by
  intro 𝕜 _
  refine ⟨scalarDirac 0, scalarDiracPrime 𝕜, coordinateScalarCLM 𝕜,
    (coordinateScalarCLM 𝕜).contDiff, fun _ => rfl, scalarDiracPrime_apply,
    fun _ => rfl, scalarDiracPrime_support, ?_, coordinate_mul_diracPrime, ?_⟩
  · intro x hx
    rw [scalarDiracPrime_support] at hx
    rw [mem_singleton_iff.mp hx]
    simp
  · intro hz
    obtain ⟨φ, hφ⟩ := exists_test_eq_one (𝕜 := 𝕜) (Ω := (⊤ : Opens (Domain 1))) 0 (mem_univ _)
    have hv := congrArg (fun T : ScalarDistribution 𝕜 (⊤ : Opens (Domain 1)) => T φ) hz
    change φ 0 = 0 at hv
    rw [hφ] at hv
    exact one_ne_zero hv

end ExpandedFA.Distributions
