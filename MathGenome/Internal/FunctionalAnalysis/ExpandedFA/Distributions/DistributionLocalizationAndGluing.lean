import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.SmoothPartitionOfUnity

open Set TopologicalSpace Function
open scoped Distributions Topology ContDiff Manifold

set_option maxHeartbeats 1000000

universe u

namespace ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- A real smooth multiplier preserves compact support and smoothness. -/
noncomputable def realMultiplyTest (a : Domain d → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (φ : Tests 𝕜 Ω) : Tests 𝕜 Ω where
  toFun x := a x • φ x
  contDiff' := ha.smul φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport.mono
    (support_smul_subset_right a (φ : Domain d → 𝕜))
  tsupport_subset' := (tsupport_smul_subset_right a (φ : Domain d → 𝕜)).trans φ.tsupport_subset

@[simp] theorem realMultiplyTest_apply (a : Domain d → ℝ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (φ : Tests 𝕜 Ω) (x : Domain d) :
    realMultiplyTest a ha φ x = a x • φ x := rfl

/-- Every test admits a finite decomposition subordinate to any open cover of
its support. The original cover need not be countable. -/
theorem finite_test_decomposition {ι : Type u} (V : ι → Set (Domain d))
    (hV : ∀ i, IsOpen (V i)) (φ : Tests 𝕜 Ω) (hc : tsupport φ ⊆ ⋃ i, V i) :
    ∃ (s : Finset ι) (ψ : ι → Tests 𝕜 Ω),
      (∀ i, tsupport (ψ i) ⊆ V i) ∧ φ = ∑ i ∈ s, ψ i := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, Domain d))
    isClosed_closure V hV hc
  let s := (ρ.locallyFinite.finite_nonempty_inter_compact φ.hasCompactSupport).toFinset
  let ψ : ι → Tests 𝕜 Ω := fun i => realMultiplyTest (ρ i)
    (contMDiff_iff_contDiff.mp (ρ i).contMDiff) φ
  refine ⟨s, ψ, fun i => ?_, ?_⟩
  · exact (tsupport_smul_subset_left (ρ i) φ).trans (hρ i)
  · ext x
    have hev : (∑ i ∈ s, ψ i) x = ∑ i ∈ s, ψ i x := by
      exact map_sum (show Tests 𝕜 Ω →+ 𝕜 from
        ⟨⟨fun f => f x, rfl⟩, fun _ _ => rfl⟩) ψ s
    rw [hev]
    change φ x = ∑ i ∈ s, (ρ i x) • φ x
    by_cases hx : x ∈ tsupport φ
    · have hsum : ∑ i ∈ s, ρ i x = 1 := by
        rw [← ρ.sum_eq_one hx]
        symm
        apply finsum_eq_sum_of_support_subset
        intro i hi
        exact (ρ.locallyFinite.finite_nonempty_inter_compact
          φ.hasCompactSupport).mem_toFinset.mpr ⟨x, hi, hx⟩
      rw [← Finset.sum_smul, hsum, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp

noncomputable def support :
    Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing.supportType :=
  fun _ _ _ _ u => distributionSupport u

/-- A distribution vanishing on open patches vanishes on their union. -/
theorem vanishing_union :
    Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing.vanishingUnionType := by
  intro 𝕜 _ d Ω u ι V hV hu φ hφ
  obtain ⟨s, ψ, hψ, heq⟩ := finite_test_decomposition V hV φ hφ
  rw [heq, map_sum]
  exact Finset.sum_eq_zero fun i _ => hu i (ψ i) (hψ i)

/-- The union used to define support really is an open vanishing set. -/
theorem support_vanishing :
    Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing.supportVanishingType := by
  intro 𝕜 _ d Ω u
  refine ⟨isOpen_sUnion fun V hV => hV.1, ?_, ?_⟩
  · rintro x ⟨V, hV, hx⟩
    exact hV.2.1 hx
  · let A := {V : Set (Domain d) // IsOpen V ∧ V ⊆ Ω ∧
        ∀ φ : Tests 𝕜 Ω, tsupport φ ⊆ V → u φ = 0}
    have heq : vanishingRegion u = ⋃ V : A, (V : Set (Domain d)) := by
      ext x
      simp [vanishingRegion, A]
    intro φ hφ
    exact vanishing_union 𝕜 d Ω u A (fun V => V.val) (fun V => V.property.1)
      (fun V => V.property.2.2) φ (heq ▸ hφ)

/-- Agreement on a neighborhood of the support suffices for equality of pairings. -/
theorem pairing_locality :
    Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing.pairingLocalityType := by
  intro 𝕜 _ d Ω u φ ψ V hV hs hEq
  have hz : tsupport (φ - ψ) ⊆ Vᶜ := by
    apply closure_minimal _ hV.isClosed_compl
    intro x hx hxV
    exact hx (sub_eq_zero.mpr (hEq hxV))
  have hvan : tsupport (φ - ψ) ⊆ vanishingRegion u := by
    intro x hx
    by_contra hn
    exact hz hx (hs ⟨(φ - ψ).tsupport_subset hx, hn⟩)
  have heq := (support_vanishing 𝕜 d Ω u).2.2 (φ - ψ) hvan
  rwa [map_sub, sub_eq_zero] at heq

/-- Multiplying by a cutoff equal to one near the support preserves every pairing. -/
theorem cutoff_locality :
    Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing.cutoffLocalityType := by
  intro 𝕜 _ d Ω u a ha V hV hs hEq φ
  apply pairing_locality 𝕜 d Ω u (multiplyTest a ha φ) φ V hV hs
  intro x hx
  change φ x * a x = φ x
  rw [hEq hx]
  exact mul_one _

/-- A compact set in an open Euclidean domain has a compactly supported smooth cutoff. -/
theorem cutoff_existence :
    Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing.cutoffExistenceType := by
  intro d Ω K hK hKO
  obtain ⟨W, hW, hKW, hWO, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hKO
  obtain ⟨f, hf0, hf1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, Domain d)) hW.isClosed_compl hK.isClosed
    (Set.disjoint_left.mpr fun x hx hxK => hx (hKW hxK))
  have hfc : ContDiff ℝ (⊤ : ℕ∞) (f : Domain d → ℝ) :=
    contMDiff_iff_contDiff.mp f.contMDiff
  have hfs : tsupport (f : Domain d → ℝ) ⊆ closure W := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hf0.self_of_nhdsSet x hn)
  let χ : Tests ℝ Ω := ⟨f, hfc, hWc.of_isClosed_subset isClosed_closure hfs,
    hfs.trans hWO⟩
  obtain ⟨V, hV, hKV, hVf⟩ := eventually_nhdsSet_iff_exists.mp hf1
  exact ⟨χ, V, hV, hKV, hVf⟩

/-- Reinterpret a test on a smaller open domain when its support lies there. -/
noncomputable def rehomeTest {U : Opens (Domain d)} (φ : Tests 𝕜 Ω) (h : tsupport φ ⊆ U) :
    Tests 𝕜 U := ⟨φ, φ.contDiff, φ.hasCompactSupport, h⟩

@[simp] theorem rehomeTest_apply {U : Opens (Domain d)} (φ : Tests 𝕜 Ω)
    (h : tsupport φ ⊆ U) (x : Domain d) : rehomeTest φ h x = φ x := rfl

/-- Changing the compact containing a function does not change derivative structure maps. -/
noncomputable def rehomeStepCLM {K L : Compacts (Domain d)}
    (T : Step 𝕜 K →L[𝕜] Step 𝕜 K) (h : ∀ φ, tsupport (T φ) ⊆ L) :
    Step 𝕜 K →L[𝕜] Step 𝕜 L where
  toFun φ := .of_support_subset (T φ).contDiff (subset_closure.trans (h φ))
  map_add' φ ψ := by ext x; exact congrArg (fun f : Step 𝕜 K => f x) (T.map_add φ ψ)
  map_smul' c φ := by ext x; exact congrArg (fun f : Step 𝕜 K => f x) (T.map_smul c φ)
  cont := by
    apply (ContDiffMapSupportedIn.continuous_iff_comp _).mpr
    intro n
    have heq : (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n ∘
        (fun φ : Step 𝕜 K => (ContDiffMapSupportedIn.of_support_subset
          (T φ).contDiff (subset_closure.trans (h φ)) : Step 𝕜 L))) =
        ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n ∘ T := by
      funext φ
      ext x
      simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_apply]
      rfl
    rw [heq]
    exact (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n).continuous.comp T.continuous

/-- Multiplication followed by changing the domain is continuous. The compact
support of the multiplier supplies the new compact step. -/
noncomputable def localizedTestCLM (U : Opens (Domain d))
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ U) : Tests 𝕜 Ω →L[𝕜] Tests 𝕜 U := by
  let T (φ : Tests 𝕜 Ω) : Tests 𝕜 U :=
    ⟨fun x => φ x * a x, φ.contDiff.mul ha,
      φ.hasCompactSupport.of_isClosed_subset isClosed_closure tsupport_mul_subset_left,
      (tsupport_mul_subset_right).trans hs⟩
  apply TestFunction.limitCLM 𝕜 T
    (fun K hK => (TestFunction.ofSupportedInCLM 𝕜 (K := ⟨tsupport a, hc⟩) hs).comp
      (rehomeStepCLM (L := ⟨tsupport a, hc⟩)
        (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul 𝕜 𝕜) ha)
        (fun φ => tsupport_mul_subset_right)))
  intro K hK φ
  ext x
  rfl

@[simp] theorem localizedTestCLM_apply (U : Opens (Domain d))
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ U) (φ : Tests 𝕜 Ω) (x : Domain d) :
    localizedTestCLM U a ha hc hs φ x = φ x * a x := rfl

/-- A sum of continuous linear functionals is continuous when only finitely
many terms survive on each compact test-function step. -/
noncomputable def compactlyFiniteSumCLM {κ : Type*}
    (F : κ → ScalarDistribution 𝕜 Ω)
    (hf : ∀ (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω),
      ∃ s : Finset κ, ∀ j ∉ s, ∀ φ : Step 𝕜 K,
        F j (TestFunction.ofSupportedIn hK φ) = 0) : ScalarDistribution 𝕜 Ω := by
  classical
  have hfin (φ : Tests 𝕜 Ω) : HasFiniteSupport (fun j => F j φ) := by
    let K : Compacts (Domain d) := ⟨tsupport φ, φ.hasCompactSupport⟩
    obtain ⟨s, hs⟩ := hf K φ.tsupport_subset
    apply s.finite_toSet.subset
    intro j hj
    by_contra hn
    let ψ : Step 𝕜 K := .of_support_subset φ.contDiff subset_closure
    have heq : TestFunction.ofSupportedIn φ.tsupport_subset ψ = φ := by ext x; rfl
    exact hj (heq ▸ hs j hn ψ)
  apply TestFunction.mkCLM 𝕜 (fun φ => ∑ᶠ j, F j φ)
  · intro φ ψ
    simp_rw [map_add]
    exact finsum_add_distrib (hfin φ) (hfin ψ)
  · intro c φ
    simp_rw [map_smul]
    exact (smul_finsum' c (hfin φ)).symm
  · intro K hK
    obtain ⟨s, hs⟩ := hf K hK
    have heq : (fun φ : Step 𝕜 K => ∑ᶠ j, F j (TestFunction.ofSupportedIn hK φ)) =
        (fun φ : Step 𝕜 K => ∑ j ∈ s, F j (TestFunction.ofSupportedIn hK φ)) := by
      funext φ
      apply finsum_eq_sum_of_support_subset
      intro j hj
      by_contra hn
      exact hj (hs j hn φ)
    change Continuous (fun φ : Step 𝕜 K => ∑ᶠ j, F j (TestFunction.ofSupportedIn hK φ))
    rw [heq]
    exact continuous_finsetSum s fun j _ =>
      (F j).continuous.comp (TestFunction.continuous_ofSupportedIn hK)

@[simp] theorem compactlyFiniteSumCLM_apply {κ : Type*}
    (F : κ → ScalarDistribution 𝕜 Ω)
    (hf : ∀ (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω),
      ∃ s : Finset κ, ∀ j ∉ s, ∀ φ : Step 𝕜 K,
        F j (TestFunction.ofSupportedIn hK φ) = 0) (φ : Tests 𝕜 Ω) :
    compactlyFiniteSumCLM F hf φ = ∑ᶠ j, F j φ := rfl

/-- A relatively locally finite family meets a compact subset of the open
domain in only finitely many members. -/
theorem finite_partition_inter {κ : Type*} (η : κ → Tests ℝ Ω)
    (hf : LocallyFinite (fun j => (Subtype.val : Ω → Domain d) ⁻¹' tsupport (η j)))
    (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω) :
    {j | (tsupport (η j) ∩ (K : Set (Domain d))).Nonempty}.Finite := by
  have hc : IsCompact ((Subtype.val : Ω → Domain d) ⁻¹' (K : Set (Domain d))) :=
    (Topology.IsEmbedding.subtypeVal.isInducing).isCompact_preimage' K.isCompact
      (by intro x hx; exact ⟨⟨x, hK hx⟩, rfl⟩)
  apply (hf.finite_nonempty_inter_compact hc).subset
  rintro j ⟨x, hxη, hxK⟩
  exact ⟨⟨x, hK hxK⟩, hxη, hxK⟩

@[simp] theorem inclusion_apply {U V : Opens (Domain d)} (h : U ≤ V)
    (φ : Tests 𝕜 U) (x : Domain d) :
    (TestFunction.monoCLM 𝕜 φ : Tests 𝕜 V) x = φ x := by
  have heq := congrFun (TestFunction.monoCLM_apply
    (𝕜 := 𝕜) (n₂ := ⊤) (Ω₂ := V) φ) x
  simp [h]

/-- A test-function sum evaluates pointwise. -/
theorem test_sum_apply {κ : Type*} (s : Finset κ) (φ : κ → Tests 𝕜 Ω) (x : Domain d) :
    (∑ j ∈ s, φ j) x = ∑ j ∈ s, φ j x :=
  map_sum (show Tests 𝕜 Ω →+ 𝕜 from ⟨⟨fun f => f x, rfl⟩, fun _ _ => rfl⟩) φ s

/-- A scalar partition of unity reconstructs each test with a finite sum.
This statement also works for a test whose domain is smaller than Ω. -/
theorem partition_reconstruct {κ : Type*} (η : κ → Tests ℝ Ω)
    (hf : LocallyFinite (fun j => (Subtype.val : Ω → Domain d) ⁻¹' tsupport (η j)))
    (hsum : ∀ x ∈ Ω, ∑ᶠ j, η j x = 1)
    {V : Opens (Domain d)} (hV : V ≤ Ω) (φ : Tests 𝕜 V) :
    ∃ s : Finset κ,
      (∀ j ∉ s, realMultiplyTest (η j) (η j).contDiff φ = 0) ∧
      φ = ∑ j ∈ s, realMultiplyTest (η j) (η j).contDiff φ := by
  classical
  let K : Compacts (Domain d) := ⟨tsupport φ, φ.hasCompactSupport⟩
  have hfin := finite_partition_inter η hf K (φ.tsupport_subset.trans hV)
  let s := hfin.toFinset
  have hzero (j : κ) (hj : j ∉ s) : realMultiplyTest (η j) (η j).contDiff φ = 0 := by
    ext x
    by_cases hφ : φ x = 0
    · simp [hφ]
    by_cases hη : η j x = 0
    · simp [hη]
    exact False.elim (hj (hfin.mem_toFinset.mpr
      ⟨x, subset_tsupport (η j) hη, subset_tsupport φ hφ⟩))
  refine ⟨s, hzero, ?_⟩
  ext x
  rw [test_sum_apply]
  simp only [realMultiplyTest_apply]
  by_cases hx : x ∈ tsupport φ
  · have hsum' : ∑ j ∈ s, η j x = 1 := by
      rw [← hsum x (hV (φ.tsupport_subset hx))]
      symm
      apply finsum_eq_sum_of_support_subset
      intro j hj
      exact hfin.mem_toFinset.mpr ⟨x, subset_tsupport (η j) hj, hx⟩
    rw [← Finset.sum_smul, hsum', one_smul]
  · rw [image_eq_zero_of_notMem_tsupport hx]
    simp

/-- Compatible distributions on arbitrary open covers glue uniquely. -/
theorem distribution_gluing :
    Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing.gluingType := by
  classical
  intro 𝕜 _ d ι U v hv
  let Ω : Opens (Domain d) := ⨆ i, U i
  have hU (i : ι) : U i ≤ Ω := le_iSup U i
  obtain ⟨κ, _, η, _, hηlf, hηsum, hηsub⟩ := smooth_partition_of_unity d Ω ι
    (fun i => (U i : Set (Domain d))) (fun i => (U i).isOpen)
    (by exact (Opens.coe_iSup U).le)
  choose ind hind using hηsub
  let a (j : κ) : Domain d → 𝕜 := fun x => (η j x : 𝕜)
  have ha (j : κ) : ContDiff ℝ (⊤ : ℕ∞) (a j) :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (η j).contDiff
  have hac (j : κ) : HasCompactSupport (a j) :=
    (η j).hasCompactSupport.comp_left (by simp)
  have has (j : κ) : tsupport (a j) ⊆ U (ind j) :=
    (tsupport_comp_subset (g := (RCLike.ofReal : ℝ → 𝕜)) (by simp) (η j)).trans (hind j)
  let T (j : κ) : Tests 𝕜 Ω →L[𝕜] Tests 𝕜 (U (ind j)) :=
    localizedTestCLM (U (ind j)) (a j) (ha j) (hac j) (has j)
  let F (j : κ) : ScalarDistribution 𝕜 Ω := (v (ind j)).comp (T j)
  have hfinite : ∀ (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω),
      ∃ s : Finset κ, ∀ j ∉ s, ∀ φ : Step 𝕜 K,
        F j (TestFunction.ofSupportedIn hK φ) = 0 := by
    intro K hK
    have hf := finite_partition_inter η hηlf K hK
    refine ⟨hf.toFinset, fun j hj φ => ?_⟩
    have hz : T j (TestFunction.ofSupportedIn hK φ) = 0 := by
      ext x
      change φ x * (η j x : 𝕜) = 0
      by_cases hφ : φ x = 0
      · simp [hφ]
      by_cases hη : η j x = 0
      · simp [hη]
      exact False.elim (hj (hf.mem_toFinset.mpr
        ⟨x, subset_tsupport (η j) hη, φ.support_subset hφ⟩))
    change v (ind j) (T j (TestFunction.ofSupportedIn hK φ)) = 0
    rw [hz, map_zero]
  let w := compactlyFiniteSumCLM F hfinite
  have hw (i : ι) (φ : Tests 𝕜 (U i)) :
      w (TestFunction.monoCLM 𝕜 φ) = v i φ := by
    let φ₀ : Tests 𝕜 Ω := TestFunction.monoCLM 𝕜 φ
    let q (j : κ) : Tests 𝕜 (U i) := realMultiplyTest (η j) (η j).contDiff φ
    have hterm (j : κ) : F j φ₀ = v i (q j) := by
      have hq : tsupport (q j) ⊆ U (ind j) :=
        (tsupport_smul_subset_left (η j) φ).trans (hind j)
      let ξ : Tests 𝕜 (U i ⊓ U (ind j)) :=
        ⟨q j, (q j).contDiff, (q j).hasCompactSupport,
          subset_inter (q j).tsupport_subset hq⟩
      have heq₁ : (TestFunction.monoCLM 𝕜 ξ : Tests 𝕜 (U i)) = q j := by
        ext x
        exact inclusion_apply inf_le_left ξ x
      have heq₂ : (TestFunction.monoCLM 𝕜 ξ : Tests 𝕜 (U (ind j))) = T j φ₀ := by
        ext x
        rw [inclusion_apply inf_le_right]
        change (η j x) • φ x = φ₀ x * (η j x : 𝕜)
        rw [inclusion_apply (hU i)]
        rw [RCLike.real_smul_eq_coe_mul, mul_comm]
      change v (ind j) (T j φ₀) = v i (q j)
      rw [← heq₂, ← hv i (ind j) ξ, heq₁]
    obtain ⟨s, hs, heq⟩ := partition_reconstruct η hηlf hηsum (hU i) φ
    change (∑ᶠ j, F j φ₀) = v i φ
    simp_rw [hterm]
    have hsum : (∑ᶠ j, v i (q j)) = ∑ j ∈ s, v i (q j) := by
      apply finsum_eq_sum_of_support_subset
      intro j hj
      by_contra hn
      exact hj (by change v i (realMultiplyTest (η j) (η j).contDiff φ) = 0
                   rw [hs j hn, map_zero])
    rw [hsum, ← map_sum]
    exact congrArg (v i) heq.symm
  refine ⟨w, hw, ?_⟩
  intro w' hw'
  apply ContinuousLinearMap.ext
  intro φ
  have hz : (w' - w) φ = 0 := vanishing_union 𝕜 d Ω (w' - w) ι
    (fun i => (U i : Set (Domain d))) (fun i => (U i).isOpen)
    (fun i ψ hψ => by
      let ψ' : Tests 𝕜 (U i) := rehomeTest ψ hψ
      have heq : (TestFunction.monoCLM 𝕜 ψ' : Tests 𝕜 Ω) = ψ := by
        ext x
        exact inclusion_apply (hU i) ψ' x
      change w' ψ - w ψ = 0
      rw [← heq, hw' i ψ', hw i ψ', sub_self]) φ
    (by simpa only [← Opens.coe_iSup] using φ.tsupport_subset)
  exact sub_eq_zero.mp hz

end ExpandedFA.Distributions
