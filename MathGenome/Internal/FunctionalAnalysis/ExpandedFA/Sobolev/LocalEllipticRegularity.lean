import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.LocalEllipticRegularity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.EllipticParametrix
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionLocalizationAndGluing

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped SchwartzMap ContDiff FourierTransform Topology
namespace ExpandedFA.Sobolev.Elliptic
open ExpandedFA.Fourier ExpandedFA.Distributions FourierScale

/-- Smooth right hand sides have arbitrarily regular compact localizations. -/
lemma locallyMemHs_of_smoothOn {d : ℕ} {U : Set (Euclidean d)}
    (hU : IsOpen U) {T : Tempered ℂ d} (hT : SmoothOn T U) (s : ℝ) :
    LocallyMemHs s U T := by
  intro a hac ha
  obtain ⟨f, hf⟩ := cutoffProduct_regular_of_tsupport_subset hU hT a hac ha
  rw [hf]
  exact memHs_regularSchwartz s f

lemma elliptic_local_step {d m : ℕ} {U : Set (Euclidean d)}
    (hU : IsOpen U) (c : Coefficients ℂ d) (hc : IsElliptic c m)
    {T : Tempered ℂ d} (hL : SmoothOn (applyOperator c T) U)
    {s : ℝ} (hT : LocallyMemHs s U T) : LocallyMemHs (s + 1) U T := by
  intro a hac ha
  have hE := operatorCommutator_memHs c hc.1 hT a hac ha
  have hA := locallyMemHs_of_smoothOn hU hL (s - (m : ℝ) + 1) a hac ha
  have he : applyOperator c (cutoffProduct a T) =
      cutoffProduct a (applyOperator c T) + operatorCommutator c a T := by
    unfold operatorCommutator
    abel
  have h := memHs_elliptic_gain c hc (hT a hac ha) (he ▸ memHs_add hA hE)
  convert h using 1
  ring

/-- Local regularity for a distribution of some initial Sobolev order. The
initial order will be obtained from compact support, rather than assumed for
the original distribution. -/
lemma smoothOn_of_elliptic_equation {d m : ℕ} {U : Set (Euclidean d)}
    (hU : IsOpen U) (c : Coefficients ℂ d) (hc : IsElliptic c m)
    {T : Tempered ℂ d} {s : ℝ} (hT : MemHs s T)
    (hL : SmoothOn (applyOperator c T) U) : SmoothOn T U := by
  have hi (n : ℕ) : LocallyMemHs (s + (n : ℝ)) U T := by
    induction n with
    | zero => simpa using locallyMemHs_of_memHs (U := U) hT
    | succ n ih =>
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
        elliptic_local_step hU c hc hL ih
  apply smoothOn_of_all_locallyMemHs hU
  intro t a hac ha
  obtain ⟨n, hn⟩ := exists_nat_ge (t - s)
  exact memHs_mono (hi n a hac ha) (by linarith)

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

@[simp] lemma testSchwartzOn_apply (φ : Tests 𝕜 Ω) (x : Euclidean d) :
    testSchwartzOn φ x = φ ((EuclideanSpace.equiv (Fin d) ℝ) x) := by
  change (TestFunction.monoCLM 𝕜 φ : Tests 𝕜 ⊤) _ = _
  simp

lemma testSchwartzOn_tsupport (φ : Tests 𝕜 Ω) :
    tsupport (testSchwartzOn φ) = (EuclideanSpace.equiv (Fin d) ℝ) ⁻¹' tsupport φ := by
  have h : (testSchwartzOn φ : Euclidean d → 𝕜) =
      (φ : Domain d → 𝕜) ∘ (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph := by
    funext x; exact testSchwartzOn_apply φ x
  rw [h, tsupport_comp_eq_preimage]
  rfl

lemma testSchwartzOn_compact (φ : Tests 𝕜 Ω) : HasCompactSupport (testSchwartzOn φ) := by
  have h : (testSchwartzOn φ : Euclidean d → 𝕜) =
      (φ : Domain d → 𝕜) ∘ (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph := by
    funext x; exact testSchwartzOn_apply φ x
  rw [h]
  exact φ.hasCompactSupport.comp_homeomorph _

/-- Every compact Schwartz test inside Ω is an original LF test. -/
def schwartzTest (φ : Schwartz 𝕜 d) (hφ : HasCompactSupport φ)
    (hΩ : tsupport φ ⊆ (EuclideanSpace.equiv (Fin d) ℝ) ⁻¹' (Ω : Set (Domain d))) :
    Tests 𝕜 Ω := by
  let e := (EuclideanSpace.equiv (Fin d) ℝ).symm
  refine ⟨(φ : Euclidean d → 𝕜) ∘ e, φ.smooth'.comp e.contDiff,
    hφ.comp_homeomorph e.toHomeomorph, ?_⟩
  change tsupport ((φ : Euclidean d → 𝕜) ∘ e.toHomeomorph) ⊆ _
  rw [tsupport_comp_eq_preimage]
  intro x hx
  have h := hΩ hx
  change (EuclideanSpace.equiv (Fin d) ℝ) ((EuclideanSpace.equiv (Fin d) ℝ).symm x) ∈ Ω at h
  rwa [ContinuousLinearEquiv.apply_symm_apply] at h

@[simp] lemma testSchwartzOn_schwartzTest (φ : Schwartz 𝕜 d) (hφ : HasCompactSupport φ)
    (hΩ : tsupport φ ⊆ (EuclideanSpace.equiv (Fin d) ℝ) ⁻¹' (Ω : Set (Domain d))) :
    testSchwartzOn (schwartzTest φ hφ hΩ) = φ := by
  ext x
  rw [testSchwartzOn_apply]
  change φ ((EuclideanSpace.equiv (Fin d) ℝ).symm ((EuclideanSpace.equiv (Fin d) ℝ) x)) = φ x
  rw [ContinuousLinearEquiv.symm_apply_apply]

lemma tsupport_schwartzTest (φ : Schwartz 𝕜 d) (hφ : HasCompactSupport φ)
    (hΩ : tsupport φ ⊆ (EuclideanSpace.equiv (Fin d) ℝ) ⁻¹' (Ω : Set (Domain d))) :
    tsupport (schwartzTest φ hφ hΩ) =
      (EuclideanSpace.equiv (Fin d) ℝ).symm ⁻¹' tsupport φ := by
  exact tsupport_comp_eq_preimage (φ : Euclidean d → 𝕜) (EuclideanSpace.equiv (Fin d) ℝ).symm.toHomeomorph

lemma testPartial_apply (i : Fin d) (φ : Tests 𝕜 Ω) (x : Domain d) :
    (TestFunction.lineDerivCLM 𝕜 (coordinateVector i) φ : Tests 𝕜 Ω) x =
      fderiv ℝ φ x (coordinateVector i) := by
  rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply]
  simp

lemma testPartial_tsupport (i : Fin d) (φ : Tests 𝕜 Ω) :
    tsupport (TestFunction.lineDerivCLM 𝕜 (coordinateVector i) φ : Tests 𝕜 Ω) ⊆ tsupport φ := by
  change tsupport (fun x => (TestFunction.lineDerivCLM 𝕜 (coordinateVector i) φ : Tests 𝕜 Ω) x) ⊆ _
  simp only [testPartial_apply]
  exact tsupport_fderiv_apply_subset ℝ (coordinateVector i)

lemma testSchwartzOn_partial (i : Fin d) (φ : Tests 𝕜 Ω) :
    testSchwartzOn (TestFunction.lineDerivCLM 𝕜 (coordinateVector i) φ : Tests 𝕜 Ω) =
      LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i) (testSchwartzOn φ) := by
  ext x
  rw [testSchwartzOn_apply, testPartial_apply]
  change _ = fderiv ℝ (testSchwartzOn φ) x (basisVector i)
  have he : (testSchwartzOn φ : Euclidean d → 𝕜) =
      (φ : Domain d → 𝕜) ∘ (EuclideanSpace.equiv (Fin d) ℝ) := by
    funext x; exact testSchwartzOn_apply φ x
  rw [he, ContinuousLinearEquiv.comp_right_fderiv]
  congr 1


/-- Agreement on every original compact test in V. -/
def RepresentsOn (T : Tempered 𝕜 d) (u : ScalarDistribution 𝕜 Ω)
    (V : Set (Domain d)) : Prop :=
  ∀ φ : Tests 𝕜 Ω, tsupport φ ⊆ V → T (testSchwartzOn φ) = u φ

lemma representsOn_partial {T : Tempered 𝕜 d} {u : ScalarDistribution 𝕜 Ω}
    {V : Set (Domain d)} (h : RepresentsOn T u V) (i : Fin d) :
    RepresentsOn (wordPartial [i] T) (localWordPartial [i] u) V := by
  intro φ hφ
  change -T (LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i) (testSchwartzOn φ)) =
    -u (TestFunction.lineDerivCLM 𝕜 (coordinateVector i) φ)
  rw [← testSchwartzOn_partial]
  exact congrArg Neg.neg (h _ ((testPartial_tsupport i φ).trans hφ))

lemma representsOn_wordPartial {T : Tempered 𝕜 d} {u : ScalarDistribution 𝕜 Ω}
    {V : Set (Domain d)} (h : RepresentsOn T u V) (w : List (Fin d)) :
    RepresentsOn (wordPartial w T) (localWordPartial w u) V := by
  induction w generalizing T u with
  | nil => exact h
  | cons i w ih => exact ih (representsOn_partial h i)

lemma representsOn_operator {T : Tempered 𝕜 d} {u : ScalarDistribution 𝕜 Ω}
    {V : Set (Domain d)} (h : RepresentsOn T u V) (c : Coefficients 𝕜 d) :
    RepresentsOn (applyOperator c T) (localOperator c u) V := by
  intro φ hφ
  simp only [applyOperator, localOperator, sum_apply,
    smul_apply]
  apply Finset.sum_congr rfl
  intro α hα
  rw [representsOn_wordPartial h (multiIndexWord α) φ hφ]

lemma smoothOn_of_representsOn {T : Tempered 𝕜 d} {u : ScalarDistribution 𝕜 Ω}
    {V : Set (Domain d)} (hVΩ : V ⊆ Ω) (h : RepresentsOn T u V)
    (hu : DistributionSmoothOn u V) :
    SmoothOn T ((EuclideanSpace.equiv (Fin d) ℝ) ⁻¹' V) := by
  obtain ⟨f, hf, hp⟩ := hu
  refine ⟨f, hf, ?_⟩
  intro φ hφ hφV
  have hφΩ := hφV.trans (preimage_mono hVΩ)
  let ψ : Tests 𝕜 Ω := schwartzTest φ hφ hφΩ
  have hψ : tsupport ψ ⊆ V := by
    rw [tsupport_schwartzTest]
    intro x hx
    have hxV := hφV hx
    change (EuclideanSpace.equiv (Fin d) ℝ) ((EuclideanSpace.equiv (Fin d) ℝ).symm x) ∈ V at hxV
    rwa [ContinuousLinearEquiv.apply_symm_apply] at hxV
  obtain ⟨hi, he⟩ := hp ψ hψ
  rw [← h ψ hψ] at he
  simpa only [ψ, testSchwartzOn_schwartzTest] using And.intro hi he

lemma distributionSmoothOn_of_representsOn {T : Tempered 𝕜 d}
    {u : ScalarDistribution 𝕜 Ω} {V : Set (Domain d)}
    (h : RepresentsOn T u V)
    (hT : SmoothOn T ((EuclideanSpace.equiv (Fin d) ℝ) ⁻¹' V)) :
    DistributionSmoothOn u V := by
  obtain ⟨f, hf, hp⟩ := hT
  refine ⟨f, hf, ?_⟩
  intro φ hφ
  obtain ⟨hi, he⟩ := hp (testSchwartzOn φ) (testSchwartzOn_compact φ)
    (by rw [testSchwartzOn_tsupport]; exact preimage_mono hφ)
  exact ⟨hi, (h φ hφ).symm.trans he⟩


lemma distributionSmoothOn_mono {u : ScalarDistribution 𝕜 Ω} {V W : Set (Domain d)}
    (hu : DistributionSmoothOn u V) (hWV : W ⊆ V) : DistributionSmoothOn u W := by
  obtain ⟨f, hf, hp⟩ := hu
  exact ⟨f, hf.mono (preimage_mono hWV), fun φ hφ => hp φ (hφ.trans hWV)⟩

/-- Multiplication by a compact test, followed by extension by zero, is a
continuous distribution on the whole space. -/
def localizeDistribution (u : ScalarDistribution 𝕜 Ω) (a : Tests 𝕜 Ω) :
    ScalarDistribution 𝕜 (⊤ : Opens (Domain d)) :=
  u.comp (localizedTestCLM Ω a a.contDiff a.hasCompactSupport a.tsupport_subset)

lemma localizeDistribution_support (u : ScalarDistribution 𝕜 Ω) (a : Tests 𝕜 Ω) :
    distributionSupport (localizeDistribution u a) ⊆ tsupport a := by
  intro x hx
  by_contra hn
  apply hx.2
  refine mem_sUnion.mpr ⟨(tsupport a)ᶜ, ⟨isClosed_closure.isOpen_compl, subset_univ _, ?_⟩, hn⟩
  intro φ hφ
  have hz : localizedTestCLM Ω a a.contDiff a.hasCompactSupport a.tsupport_subset φ = 0 := by
    ext y
    change φ y * a y = 0
    by_cases hy : y ∈ tsupport φ
    · exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport (hφ hy))
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  change u _ = 0
  exact (congrArg u hz).trans (map_zero u)

lemma localizeDistribution_compact (u : ScalarDistribution 𝕜 Ω) (a : Tests 𝕜 Ω) :
    IsCompact (distributionSupport (localizeDistribution u a)) := by
  apply a.hasCompactSupport.of_isClosed_subset _ (localizeDistribution_support u a)
  change IsClosed (univ \ vanishingRegion (localizeDistribution u a))
  have ho : IsOpen (vanishingRegion (localizeDistribution u a)) :=
    isOpen_sUnion fun V hV => hV.1
  simpa only [compl_eq_univ_sdiff] using ho.isClosed_compl

lemma localizeDistribution_eq (u : ScalarDistribution 𝕜 Ω) (a : Tests 𝕜 Ω)
    {V : Set (Domain d)} (ha : ∀ x ∈ V, a x = 1)
    (φ : Tests 𝕜 Ω) (hφ : tsupport φ ⊆ V) :
    localizeDistribution u a (TestFunction.monoCLM 𝕜 φ) = u φ := by
  change u _ = u φ
  congr 1
  ext x
  change (TestFunction.monoCLM 𝕜 φ : Tests 𝕜 ⊤) x * a x = φ x
  have hm : (TestFunction.monoCLM 𝕜 φ : Tests 𝕜 ⊤) x = φ x := by
    simp
  rw [hm]
  by_cases hx : x ∈ tsupport φ
  · rw [ha x (hφ hx), mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- A compact part of an arbitrary local distribution has a genuine negative
Sobolev representative on a neighborhood of that part. -/
lemma compact_local_representation {Ω : Opens (Domain d)} (u : ScalarDistribution ℂ Ω)
    {K : Set (Domain d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ (V : Set (Domain d)) (T : Tempered ℂ d) (N : ℕ),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      FourierScale.MemHs (-(N : ℝ)) T ∧ RepresentsOn T u V := by
  obtain ⟨a₀, V₀, hV₀, hKV₀, ha₀⟩ := cutoff_existence d Ω K hK hKΩ
  let a : Tests ℂ Ω := TestFunction.postcompCLM Complex.ofRealCLM a₀
  let v := localizeDistribution u a
  obtain ⟨N, t, ht⟩ := LocalOperations.compact_support d v (localizeDistribution_compact u a)
  refine ⟨V₀ ∩ Ω, FourierScale.realization t, N, hV₀.inter Ω.isOpen,
    subset_inter hKV₀ hKΩ, inter_subset_right, ?_, ?_⟩
  · exact (FourierScale.realization_image d _ _).mp ⟨t, rfl⟩
  · intro φ hφ
    rw [testSchwartzOn, ht]
    apply localizeDistribution_eq (V := V₀ ∩ Ω) u a ?_ φ hφ
    intro x hx
    change (a₀ x : ℂ) = 1
    rw [ha₀ hx.1]
    rfl


/-- Smooth integral representatives agree on overlaps and glue on an arbitrary
open domain. The compact-cover condition also permits a whole test to be
paired in one neighborhood. -/
lemma distributionSmoothOn_of_compact_cover {Ω : Opens (Domain d)}
    (u : ScalarDistribution ℂ Ω) {ι : Type*} (V : ι → Set (Domain d))
    (hV : ∀ i, IsOpen (V i)) (hVΩ : ∀ i, V i ⊆ Ω)
    (hcover : ∀ K : Set (Domain d), IsCompact K → K ⊆ Ω → ∃ i, K ⊆ V i)
    (h : ∀ i, DistributionSmoothOn u (V i)) : DistributionSmoothOn u Ω := by
  classical
  choose g hg hp using h
  let e := EuclideanSpace.equiv (Fin d) ℝ
  let W (i : ι) : Set (Euclidean d) := e ⁻¹' V i
  have hW (i : ι) : IsOpen (W i) := (hV i).preimage e.continuous
  have hcompat (i j : ι) : EqOn (g i) (g j) (W i ∩ W j) := by
    apply continuousOn_eq_of_test_pairing ((hW i).inter (hW j))
      ((hg i).continuousOn.mono inter_subset_left) ((hg j).continuousOn.mono inter_subset_right)
    intro φ hφ hφW
    have hφΩ : tsupport φ ⊆ e ⁻¹' (Ω : Set (Domain d)) :=
      hφW.trans (inter_subset_left.trans (preimage_mono (hVΩ i)))
    let ψ : Tests ℂ Ω := schwartzTest φ hφ hφΩ
    have hψ : tsupport ψ ⊆ V i ∩ V j := by
      rw [tsupport_schwartzTest]
      intro x hx
      have hy := hφW hx
      change e (e.symm x) ∈ V i ∩ V j at hy
      rwa [e.apply_symm_apply] at hy
    obtain ⟨hi, hei⟩ := hp i ψ (hψ.trans inter_subset_left)
    obtain ⟨hj, hej⟩ := hp j ψ (hψ.trans inter_subset_right)
    have he := hei.symm.trans hej
    simp only [ψ, testSchwartzOn_schwartzTest] at hi hj he
    exact ⟨hi, hj, he⟩
  have hex : ∀ x : (Ω : Set (Domain d)), ∃ i, x.val ∈ V i := by
    intro x
    obtain ⟨i, hi⟩ := hcover {x.val} isCompact_singleton (singleton_subset_iff.mpr x.property)
    exact ⟨i, hi (mem_singleton _)⟩
  choose j hj using hex
  let f : Euclidean d → ℂ := fun x => if hx : e x ∈ Ω then g (j ⟨e x, hx⟩) x else 0
  have hfgi (i : ι) : EqOn f (g i) (W i) := by
    intro x hx
    have hxΩ : e x ∈ Ω := hVΩ i hx
    dsimp only [f]
    rw [dite_eq_left hxΩ]
    exact hcompat (j ⟨e x, hxΩ⟩) i ⟨hj ⟨e x, hxΩ⟩, hx⟩
  refine ⟨f, ?_, ?_⟩
  · apply (Ω.isOpen.preimage e.continuous).contDiffOn_iff.mpr
    intro x hx
    let i := j ⟨e x, hx⟩
    have hxi : x ∈ W i := hj ⟨e x, hx⟩
    apply ((hg i).contDiffAt ((hW i).mem_nhds hxi)).congr_of_eventuallyEq
    exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨W i, (hW i).mem_nhds hxi, hfgi i⟩
  · intro φ hφ
    obtain ⟨i, hi⟩ := hcover (tsupport φ) φ.hasCompactSupport φ.tsupport_subset
    obtain ⟨hii, hie⟩ := hp i φ hi
    have hid : (fun x => f x * testSchwartzOn φ x) =
        (fun x => g i x * testSchwartzOn φ x) := by
      funext x
      by_cases hx : e x ∈ tsupport φ
      · rw [hfgi i (hi hx)]
      · simp only [testSchwartzOn_apply]
        change f x * φ (e x) = g i x * φ (e x)
        rw [image_eq_zero_of_notMem_tsupport hx]
        simp
    exact ⟨hid.symm ▸ hii, hie.trans (congrArg (fun F : Euclidean d → ℂ => ∫ x, F x) hid).symm⟩

lemma distributionSmoothOn_of_compact_local {Ω : Opens (Domain d)}
    (u : ScalarDistribution ℂ Ω)
    (h : ∀ K : Set (Domain d), IsCompact K → K ⊆ Ω →
      ∃ V : Set (Domain d), IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧ DistributionSmoothOn u V) :
    DistributionSmoothOn u Ω := by
  let ι := {V : Set (Domain d) // IsOpen V ∧ V ⊆ Ω ∧ DistributionSmoothOn u V}
  apply distributionSmoothOn_of_compact_cover u (fun i : ι => i.val)
    (fun i => i.property.1) (fun i => i.property.2.1) ?_ (fun i => i.property.2.2)
  intro K hK hKΩ
  obtain ⟨V, hVo, hKV, hVΩ, huV⟩ := h K hK hKΩ
  exact ⟨⟨V, hVo, hVΩ, huV⟩, hKV⟩

/-- Constant-coefficient elliptic regularity on arbitrary open sets for the
original complex-linear LF dual. -/
theorem complex_local_elliptic_regularity :
    Specs.ExpandedFA.Sobolev.LocalEllipticRegularity.regularityType ℂ := by
  intro d m c hc Ω u hL
  apply distributionSmoothOn_of_compact_local u
  intro K hK hKΩ
  obtain ⟨V, T, N, hV, hKV, hVΩ, hT, hTu⟩ := compact_local_representation u hK hKΩ
  have hLT := smoothOn_of_representsOn hVΩ (representsOn_operator hTu c)
    (distributionSmoothOn_mono hL hVΩ)
  have hTV := smoothOn_of_elliptic_equation
    (hV.preimage (EuclideanSpace.equiv (Fin d) ℝ).continuous) c hc hT hLT
  exact ⟨V, hV, hKV, hVΩ, distributionSmoothOn_of_representsOn hTu hTV⟩


section RealField
open LocalOperations
lemma postcomp_testPartial (A : ℂ →L[ℝ] ℝ) (i : Fin d) (φ : Tests ℂ Ω) :
    TestFunction.postcompCLM A (TestFunction.lineDerivCLM ℂ (coordinateVector i) φ : Tests ℂ Ω) =
      (TestFunction.lineDerivCLM ℝ (coordinateVector i) (TestFunction.postcompCLM A φ) : Tests ℝ Ω) := by
  ext x
  rw [testPartial_apply]
  change A (fderiv ℝ φ x (coordinateVector i)) = _
  rw [TestFunction.postcompCLM_apply,
    fderiv_comp x A.differentiableAt (φ.contDiff.differentiable (by simp)).differentiableAt,
    A.fderiv]
  rfl

lemma complexify_local_partial (u : ScalarDistribution ℝ Ω) (i : Fin d) :
    complexifyDistribution (localWordPartial [i] u) =
      localWordPartial [i] (complexifyDistribution u) := by
  ext φ
  simp only [localWordPartial, neg_apply, ContinuousLinearMap.comp_apply,
    complexifyDistribution, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, Complex.ofReal_neg, postcomp_testPartial]
  ring

lemma complexify_local_word (u : ScalarDistribution ℝ Ω) (w : List (Fin d)) :
    complexifyDistribution (localWordPartial w u) =
      localWordPartial w (complexifyDistribution u) := by
  induction w generalizing u with
  | nil => rfl
  | cons i w ih =>
    change complexifyDistribution (localWordPartial w (localWordPartial [i] u)) = _
    rw [ih, complexify_local_partial]
    rfl

def complexifyLocalLM : ScalarDistribution ℝ Ω →ₗ[ℝ] ScalarDistribution ℂ Ω where
  toFun := complexifyDistribution
  map_add' u v := by
    ext φ
    simp [complexifyDistribution, mul_add]
    ring
  map_smul' a u := by
    ext φ
    simp [complexifyDistribution, smul_eq_mul]
    ring

lemma complexify_local_operator (c : Coefficients ℝ d) (u : ScalarDistribution ℝ Ω) :
    complexifyDistribution (localOperator c u) =
      localOperator (scalarComplexCoefficients c) (complexifyDistribution u) := by
  classical
  change complexifyLocalLM (∑ α ∈ c.support, c α • localWordPartial (multiIndexWord α) u) = _
  rw [map_sum]
  simp only [scalarComplexCoefficients_support, localOperator]
  apply Finset.sum_congr rfl
  intro α hα
  rw [map_smul]
  change c α • complexifyDistribution (localWordPartial (multiIndexWord α) u) = _
  rw [complexify_local_word]
  ext φ
  have hc : toComplexRingHom ℝ (c α) = (c α : ℂ) := toComplexRingHom_ofReal (𝕜 := ℝ) (c α)
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ), hc]


lemma distributionSmoothOn_complexify (u : ScalarDistribution ℝ Ω)
    {V : Set (Domain d)} (hu : DistributionSmoothOn u V) :
    DistributionSmoothOn (complexifyDistribution u) V := by
  obtain ⟨f, hf, hp⟩ := hu
  refine ⟨fun x => (f x : ℂ), Complex.ofRealCLM.contDiff.comp_contDiffOn hf, ?_⟩
  intro φ hφ
  let rφ : Tests ℝ Ω := TestFunction.postcompCLM Complex.reCLM φ
  let iφ : Tests ℝ Ω := TestFunction.postcompCLM Complex.imCLM φ
  obtain ⟨hr, her⟩ := hp rφ ((tsupport_comp_subset (map_zero Complex.reCLM) φ).trans hφ)
  obtain ⟨hi, hei⟩ := hp iφ ((tsupport_comp_subset (map_zero Complex.imCLM) φ).trans hφ)
  have hid : (fun x => (f x : ℂ) * testSchwartzOn φ x) =
      fun x => ((f x * testSchwartzOn rφ x : ℝ) : ℂ) +
        Complex.I * ((f x * testSchwartzOn iφ x : ℝ) : ℂ) := by
    funext x
    apply Complex.ext <;> simp [rφ, iφ, testSchwartzOn_apply, Complex.mul_re, Complex.mul_im]
  have hrC : Integrable (fun x => ((f x * testSchwartzOn rφ x : ℝ) : ℂ)) := hr.ofReal
  have hiC : Integrable (fun x => ((f x * testSchwartzOn iφ x : ℝ) : ℂ)) := hi.ofReal
  refine ⟨hid.symm ▸ (hrC.add (hiC.const_mul Complex.I)), ?_⟩
  have hrint := Complex.ofRealCLM.integral_comp_comm hr
  have hiint := Complex.ofRealCLM.integral_comp_comm hi
  change (∫ x, ((f x * testSchwartzOn rφ x : ℝ) : ℂ)) =
    ((∫ x, f x * testSchwartzOn rφ x : ℝ) : ℂ) at hrint
  change (∫ x, ((f x * testSchwartzOn iφ x : ℝ) : ℂ)) =
    ((∫ x, f x * testSchwartzOn iφ x : ℝ) : ℂ) at hiint
  rw [hid, integral_add hrC (hiC.const_mul Complex.I), integral_const_mul,
    hrint, hiint]
  change (u rφ : ℂ) + Complex.I * (u iφ : ℂ) = _
  rw [her, hei]

lemma distributionSmoothOn_of_complexify (u : ScalarDistribution ℝ Ω)
    {V : Set (Domain d)} (hu : DistributionSmoothOn (complexifyDistribution u) V) :
    DistributionSmoothOn u V := by
  obtain ⟨f, hf, hp⟩ := hu
  refine ⟨fun x => (f x).re, Complex.reCLM.contDiff.comp_contDiffOn hf, ?_⟩
  intro φ hφ
  let ψ : Tests ℂ Ω := TestFunction.postcompCLM Complex.ofRealCLM φ
  have hψ : tsupport ψ ⊆ V :=
    (tsupport_comp_subset (map_zero Complex.ofRealCLM) φ).trans hφ
  obtain ⟨hi, he⟩ := hp ψ hψ
  have hid : (fun x => (f x * testSchwartzOn ψ x).re) =
      fun x => (f x).re * testSchwartzOn φ x := by
    funext x
    simp [ψ, testSchwartzOn_apply, Complex.mul_re]
  refine ⟨hid ▸ hi.re, ?_⟩
  have hint := Complex.reCLM.integral_comp_comm hi
  change (∫ x, (f x * testSchwartzOn ψ x).re) = (∫ x, f x * testSchwartzOn ψ x).re at hint
  rw [← hid, hint]
  have he' := congrArg Complex.re he
  rw [complexifyDistribution_apply_real] at he'
  exact he'

/-- The real result follows by complexification of both the operator and the
original LF distribution, then taking the real part of the smooth representative. -/
theorem real_local_elliptic_regularity :
    Specs.ExpandedFA.Sobolev.LocalEllipticRegularity.regularityType ℝ := by
  intro d m c hc Ω u hL
  apply distributionSmoothOn_of_complexify
  apply complex_local_elliptic_regularity d m (scalarComplexCoefficients c)
    (isElliptic_scalarComplexCoefficients c hc) Ω (complexifyDistribution u)
  rw [← complexify_local_operator]
  exact distributionSmoothOn_complexify _ hL


end RealField
/-- The Euclidean definition is exactly smoothness by ordinary Lebesgue
integration in the original coordinate space, with no boundary requirement. -/
lemma distributionSmoothOn_iff_native (u : ScalarDistribution 𝕜 Ω) (V : Set (Domain d)) :
    DistributionSmoothOn u V ↔ CoordinateSmoothOn u V := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have he : MeasurePreserving (e : Euclidean d → Domain d) volume volume :=
    PiLp.volume_preserving_ofLp (Fin d)
  have hemb : MeasurableEmbedding (e : Euclidean d → Domain d) :=
    e.toHomeomorph.measurableEmbedding
  constructor
  · rintro ⟨f, hf, hp⟩
    refine ⟨f ∘ e.symm, hf.comp e.symm.contDiff.contDiffOn ?_, ?_⟩
    · intro x hx
      change e (e.symm x) ∈ V
      rwa [e.apply_symm_apply]
    · intro φ hφ
      obtain ⟨hi, hpφ⟩ := hp φ hφ
      let F : Domain d → 𝕜 := fun x => f (e.symm x) * φ x
      have hid : (fun x => f x * testSchwartzOn φ x) = F ∘ e := by
        funext x
        rw [testSchwartzOn_apply]
        change f x * φ (e x) = f (e.symm (e x)) * φ (e x)
        rw [e.symm_apply_apply]
      have hFi : Integrable F := (he.integrable_comp_emb hemb).mp (hid ▸ hi)
      have hFint := he.integral_comp hemb F
      exact ⟨hFi, hpφ.trans ((congrArg (fun G : Euclidean d → 𝕜 => ∫ x, G x) hid).trans hFint)⟩
  · rintro ⟨f, hf, hp⟩
    refine ⟨f ∘ e, hf.comp e.contDiff.contDiffOn (fun x hx => hx), ?_⟩
    intro φ hφ
    obtain ⟨hi, hpφ⟩ := hp φ hφ
    have hid : (fun x => (f ∘ e) x * testSchwartzOn φ x) =
        (fun x => f x * φ x) ∘ e := by
      funext x
      simp only [testSchwartzOn_apply, Function.comp_apply]
      rfl
    have hFi := (he.integrable_comp_emb hemb).mpr hi
    refine ⟨hid.symm ▸ hFi, ?_⟩
    exact hpφ.trans ((he.integral_comp hemb (fun x => f x * φ x)).symm.trans
      (congrArg (fun G : Euclidean d → 𝕜 => ∫ x, G x) hid).symm)


/-- Local elliptic regularity with the original coordinate-space Lebesgue pairing. -/
theorem complex_local_elliptic_regularity_native :
    Specs.ExpandedFA.Sobolev.LocalEllipticRegularity.complexRegularityType := by
  intro d m c hc Ω u hL
  apply (distributionSmoothOn_iff_native u Ω).mp
  exact complex_local_elliptic_regularity d m c hc Ω u
    ((distributionSmoothOn_iff_native (localOperator c u) Ω).mpr hL)

/-- Real local elliptic regularity with the original coordinate-space pairing. -/
theorem real_local_elliptic_regularity_native :
    Specs.ExpandedFA.Sobolev.LocalEllipticRegularity.realRegularityType := by
  intro d m c hc Ω u hL
  apply (distributionSmoothOn_iff_native u Ω).mp
  exact real_local_elliptic_regularity d m c hc Ω u
    ((distributionSmoothOn_iff_native (localOperator c u) Ω).mpr hL)

end ExpandedFA.Sobolev.Elliptic
