import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.SubmanifoldExtension
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.BoundaryImmersion
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Extension

namespace SmoothManifolds.SubmanifoldExtension
open ModelData AtlasData MapData MapClassData FiniteRegularityData Set Filter
open scoped Topology ContDiff
universe u v

/-- A vector-valued ambient germ in one atlas chart is smooth in every chart. -/
theorem euclidean_smooth_of_chart {n k : ℕ} {a : ModelKind} {N : Type v}
    [TopologicalSpace N] {A : Set (ModelChart n a N)}
    (hA : IsContDiffAtlas (⊤ : ℕ∞) A) {d : ModelChart n a N} (hd : d ∈ A)
    {G : N → Euclidean k} {y : N} (hy : y ∈ d.source)
    (h : LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (d z).val) G y) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) A G y := by
  obtain ⟨U, hU, hyU, H, hH, heq⟩ := h
  apply (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ _).mpr
  intro j
  exact scalarContDiffAt_of_chart hA hd hy
    ⟨U, hU, hyU, fun z => H z j, (contDiffOn_pi.mp hH) j,
      heq.mono (fun _ hz => congrFun hz j)⟩

/-- Every smooth vector-valued function on an embedded manifold has actual
ambient smooth extensions near each image point. The straightening happens
in the full Euclidean target chart, even when its model is a half-space. -/
theorem local_extension {m n k : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothEmbedding S T f) (g : M → Euclidean k)
    (hg : ∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val g x)
    (p : M) :
    ∃ W : Set N, IsOpen W ∧ f p ∈ W ∧ ∃ G : N → Euclidean k,
      (∀ y ∈ W, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val G y) ∧
      ∀ x, f x ∈ W → G (f x) = g x := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  obtain ⟨U, hU, hepU, F, hF, heF⟩ := (hf.1 p).2 e he d hd hp hfp
  have hdF := ((hF.contDiffAt (hU.mem_nhds hepU)).differentiableAt
    (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hderiv : chartDerivative e d f p = fderiv ℝ F (e p).val :=
    FiniteRegularity.coordinateDerivative_eq e _ p hp _ ⟨F, hdF, heF⟩
  have hf1 : ManifoldContDiff 1 S.smoothStructure.val T.smoothStructure.val f :=
    manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf.1
  have hi : Function.Injective (fderiv ℝ F (e p).val) := by
    rw [← hderiv]
    exact ((MapClasses.chart_invariants S T f hf1 p e d he hd hp hfp).2.1).mp (hf.2.2.1 p)
  obtain ⟨_, h, hh, _, O, hO, hepO, hform⟩ :=
    BoundaryImmersion.euclidean_immersion (⊤ : ℕ∞) (by simp) F U hU hF
      (e p).val hepU _ hdF hi
  obtain ⟨A, hA, hepA, H, hH, heH⟩ := (hg p).2 e he hp
  let K : Set (Euclidean n) := h.source ∩ (fun z => (h z).1) ⁻¹' A
  have hK : IsOpen K := (continuous_fst.comp_continuousOn h.continuousOn).isOpen_inter_preimage
    h.open_source hA
  let J : Euclidean n → Euclidean k := fun z => H (h z).1
  have hJ : ContDiffOn ℝ (⊤ : ℕ∞) J K :=
    hH.comp ((contDiff_fst.comp_contDiffOn hh).mono inter_subset_left) (fun _ hz => hz.2)
  have hdpK : (d (f p)).val ∈ K := by
    rw [← heF.eq_of_nhds]
    refine ⟨(hform _ hepO).1, ?_⟩
    change (h (F (e p).val)).1 ∈ A
    rw [(hform _ hepO).2]
    exact hepA
  let W₀ : Set N := d.source ∩ (fun y => (d y).val) ⁻¹' K
  have hW₀ : IsOpen W₀ :=
    (continuous_subtype_val.comp_continuousOn d.continuousOn).isOpen_inter_preimage
      d.open_source hK
  have hfpW₀ : f p ∈ W₀ := ⟨hfp, hdpK⟩
  have hecont : ContinuousAt (fun y => (e y).val) p :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  have hnhds : ∀ᶠ x in 𝓝 p, (e x).val ∈ O ∧
      F (e x).val = (d (f x)).val ∧ H (e x).val = g x := by
    filter_upwards [hecont.preimage_mem_nhds (hO.mem_nhds hepO), heF, heH] with x hx hxF hxH
    exact ⟨hx, hxF, hxH⟩
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hnhds
  obtain ⟨E, hE⟩ := hf.2.2.2
  have hEmb : Topology.IsEmbedding f := by
    have hh : (fun x => (E x).val) = f := funext hE
    rw [← hh]
    exact Topology.IsEmbedding.subtypeVal.comp E.isEmbedding
  obtain ⟨W₁, hW₁, hpre⟩ := hEmb.isInducing.isOpen_iff.mp hV
  let G : N → Euclidean k := fun y => J (d y).val
  refine ⟨W₀ ∩ W₁, hW₀.inter hW₁, ⟨hfpW₀, ?_⟩, G, ?_, ?_⟩
  · change p ∈ f ⁻¹' W₁
    rw [hpre]
    exact hpV
  · intro y hy
    exact euclidean_smooth_of_chart T.smoothStructure.property.1 hd hy.1.1
      ⟨K, hK, hy.1.2, J, hJ, Eventually.of_forall (fun _ => rfl)⟩
  · intro x hx
    have hxV : x ∈ V := by
      rw [← hpre]
      exact hx.2
    obtain ⟨hxO, hxF, hxH⟩ := hVsub hxV
    change H (h (d (f x)).val).1 = g x
    rw [← hxF, (hform _ hxO).2]
    exact hxH

/-- Composition with a smooth map preserves Euclidean-valued smoothness. -/
theorem euclidean_smooth_comp {m n k : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    {A : Set (ModelChart m a M)} {B : Set (ModelChart n b N)}
    (hB : IsAtlas B) {f : M → N} {g : N → Euclidean k} {x : M}
    (hf : ManifoldContDiffAt (⊤ : ℕ∞) A B f x)
    (hg : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) B g (f x)) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) A (g ∘ f) x := by
  obtain ⟨d, hd, hfd⟩ := hB (f x)
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro e he hxe
  exact LocalCoordinateExtension.comp
    (LocalCoordinateExtension.precomp (hg.2 d hd hfd) hf.1 rfl)
    (hf.2 e he d hd hxe hfd)

/-- Smoothness on an open subspace is reflected by its open inclusion.
Only the ordinary restricted atlas is needed in this direction. -/
theorem euclidean_smooth_from_open {n k : ℕ} {a : ModelKind} {N : Type v}
    [TopologicalSpace N] {A : Set (ModelChart n a N)} {U : Set N} (hU : IsOpen U)
    {G : N → Euclidean k}
    (hg : ∀ x : U, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
      (openSubsetAtlas A U hU) (G ∘ Subtype.val) x) :
    ∀ y ∈ U, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) A G y := by
  intro y hy
  let x : U := ⟨y, hy⟩
  refine ⟨hU.isOpenEmbedding_subtypeVal.continuousAt_iff.mp (hg x).1, ?_⟩
  intro d hd hyd
  have hh := (hg x).2 (d.subtypeRestr (s := ⟨U, hU⟩) ⟨x⟩)
    ⟨⟨x⟩, d, hd, rfl⟩ (by simpa using hyd)
  exact (localCoordinateExtension_open_subtype_iff hU
    (fun z => (d z).val) G x).mp hh

/-- Patching on a whole manifold. Closed supports make the weighted terms
smooth even where the chosen total local extensions are arbitrary. -/
theorem patch_extensions {n k : ℕ} {a : ModelKind} {N : Type v}
    [TopologicalSpace N] (T : SmoothManifold n a N)
    {ι : Type u} (W : ι → Set N) (hW : ∀ i, IsOpen (W i))
    (hcover : ∀ y, ∃ i, y ∈ W i) (H : ι → N → Euclidean k)
    (hH : ∀ i y, y ∈ W i →
      ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val (H i) y) :
    ∃ G : N → Euclidean k,
      (∀ y, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val G y) ∧
      ∀ (y : N) (v : Euclidean k), (∀ i, y ∈ W i → H i y = v) → G y = v := by
  classical
  obtain ⟨ρ, hρ, hsub⟩ := exists_smooth_partition T W hW hcover
  obtain ⟨hsm, _, hlf, hsum⟩ := hρ
  let G : N → Euclidean k := fun y j => ∑ᶠ i, ρ i y * H i y j
  have hterm (i : ι) (j : Fin k) :
      ScalarSmooth T.smoothStructure.val (fun y => ρ i y * H i y j) := by
    apply scalarContDiff_mul_of_support_subset (hsm i) (V := W i)
    · intro y hy
      exact (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ y).mp (hH i y hy) j
    · exact hsub i
  have hsupp (j : Fin k) (i : ι) :
      sectionSupport (fun y => ρ i y * H i y j) ⊆ sectionSupport (ρ i) := by
    apply closure_mono
    intro y hy
    exact left_ne_zero_of_mul hy
  refine ⟨G, ?_, ?_⟩
  · intro y
    apply (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ _).mpr
    intro j
    exact scalarContDiff_finsum (fun i => hterm i j) (hlf.subset (hsupp j)) y
  · intro y v hv
    funext j
    have heq (i : ι) : ρ i y * H i y j = ρ i y * v j := by
      by_cases hz : ρ i y = 0
      · simp [hz]
      · rw [hv i (hsub i (subset_closure hz))]
    change (∑ᶠ i, ρ i y * H i y j) = v j
    simp_rw [heq]
    rw [← finsum_mul, hsum y, one_mul]

/-- No closedness is needed to patch the local extensions on their union. -/
theorem embedding_extension_neighborhood :
    Specs.SmoothManifolds.Ch03.SubmanifoldExtension.embedding_extension_neighborhoodType.{u,v} := by
  intro m n k a b M N _ _ S T f hf g hg
  classical
  choose W hW hpW H hH heq using local_extension S T f hf g hg
  let U : Set N := ⋃ p, W p
  have hU : IsOpen U := isOpen_iUnion hW
  have hWsub (p : M) : W p ⊆ U := subset_iUnion W p
  have hfpU (p : M) : f p ∈ U := hWsub p (hpW p)
  obtain ⟨R, _, hR, hinc⟩ := exists_openSubset_smoothManifold T U hU
  let V : M → Set U := fun p => Subtype.val ⁻¹' W p
  have hV : ∀ p, IsOpen (V p) := fun p => (hW p).preimage continuous_subtype_val
  have hcover : ∀ y : U, ∃ p, y ∈ V p := by
    intro y
    obtain ⟨p, hp⟩ := mem_iUnion.mp (show y.val ∈ ⋃ p, W p from y.property)
    exact ⟨p, hp⟩
  let J : M → U → Euclidean k := fun p y => H p y.val
  have hJ : ∀ p y, y ∈ V p →
      ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val (J p) y := by
    intro p y hy
    exact euclidean_smooth_comp T.smoothStructure.property.1.1 (hinc y) (hH p y.val hy)
  obtain ⟨G, hG, hmatch⟩ := patch_extensions R V hV hcover J hJ
  let G' : N → Euclidean k := fun y => if hy : y ∈ U then G ⟨y, hy⟩ else 0
  have hrestrict : (G' ∘ Subtype.val : U → Euclidean k) = G := by
    funext y
    simp [G', y.property]
  have hB : openSubsetAtlas T.smoothStructure.val U hU ⊆ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension
      (openSubsetAtlas_isContDiffAtlas _ _ T.smoothStructure.property.1 U hU)
  refine ⟨U, hU, ?_, G', ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact hfpU p
  · apply euclidean_smooth_from_open hU
    rw [hrestrict]
    intro y
    exact ⟨(hG y).1, fun d hd hdy => (hG y).2 d (hB hd) hdy⟩
  · intro p
    change (if hy : f p ∈ U then G ⟨f p, hy⟩ else 0) = g p
    rw [dite_eq_left (hfpU p)]
    exact hmatch ⟨f p, hfpU p⟩ (g p) (fun i hi => heq i p hi)

/-- For closed images, adding the open complement with zero local extension
makes the cover global. -/
theorem embedding_extension_closed :
    Specs.SmoothManifolds.Ch03.SubmanifoldExtension.embedding_extension_closedType.{u,v} := by
  intro m n k a b M N _ _ S T f hf hclosed g hg
  classical
  choose V hV hpV H hH heq using local_extension S T f hf g hg
  let W : Option M → Set N
    | none => (range f)ᶜ
    | some p => V p
  have hW : ∀ i, IsOpen (W i) := by
    intro i
    cases i with
    | none => exact hclosed.isOpen_compl
    | some p => exact hV p
  have hcover : ∀ y : N, ∃ i, y ∈ W i := by
    intro y
    by_cases hy : y ∈ range f
    · obtain ⟨p, rfl⟩ := hy
      exact ⟨some p, hpV p⟩
    · exact ⟨none, hy⟩
  let J : Option M → N → Euclidean k
    | none => fun _ => 0
    | some p => H p
  have hJ : ∀ i y, y ∈ W i →
      ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val (J i) y := by
    intro i y hy
    cases i with
    | none =>
      apply (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ _).mpr
      intro j
      exact ScalarContDiffAt.const _ _ 0 y
    | some p => exact hH p y hy
  obtain ⟨G, hG, hmatch⟩ := patch_extensions T W hW hcover J hJ
  refine ⟨G, hG, ?_⟩
  intro p
  apply hmatch (f p) (g p)
  intro i hi
  cases i with
  | none => exact False.elim (hi (mem_range_self p))
  | some q => exact heq q p hi

/-- The scalar assertion uses exactly the shared one-coordinate smoothness test. -/
theorem scalar_embedding_extension_neighborhood :
    Specs.SmoothManifolds.Ch03.SubmanifoldExtension.scalar_embedding_extension_neighborhoodType.{u,v} := by
  intro m n a b M N _ _ S T f hf g hg
  obtain ⟨U, hU, hsub, G, hG, heq⟩ :=
    embedding_extension_neighborhood S T f hf (fun x (_ : Fin 1) => g x) hg
  refine ⟨U, hU, hsub, fun y => G y 0, ?_, ?_⟩
  · intro y hy
    exact (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ _).mp (hG y hy) 0
  · intro x
    exact congrFun (heq x) 0

/-- Closed embedded submanifolds admit global scalar extensions. -/
theorem scalar_embedding_extension_closed :
    Specs.SmoothManifolds.Ch03.SubmanifoldExtension.scalar_embedding_extension_closedType.{u,v} := by
  intro m n a b M N _ _ S T f hf hclosed g hg
  obtain ⟨G, hG, heq⟩ :=
    embedding_extension_closed S T f hf hclosed (fun x (_ : Fin 1) => g x) hg
  refine ⟨fun y => G y 0, ?_, ?_⟩
  · intro y
    exact (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ _).mp (hG y) 0
  · intro x
    exact congrFun (heq x) 0

/-- Euclidean-valued smooth functions restrict to the canonical open atlas. -/
theorem euclidean_smooth_restrict_open {n k : ℕ} {a : ModelKind} {N : Type v}
    [TopologicalSpace N] {A : Set (ModelChart n a N)} {U : Set N} (hU : IsOpen U)
    {G : N → Euclidean k}
    (hg : ∀ y ∈ U, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) A G y) :
    ∀ y : U, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
      (openSubsetAtlas A U hU) (G ∘ Subtype.val) y := by
  intro y
  refine ⟨(hg y.val y.property).1.comp continuousAt_subtype_val, ?_⟩
  rintro _ ⟨hne, d, hd, rfl⟩ hyd
  exact LocalCoordinateExtension.precomp
    ((hg y.val y.property).2 d hd (by simpa using hyd)) continuousAt_subtype_val rfl

/-- The actual subset formulation, for every specified embedded structure on
that underlying set and every finite target dimension (also zero). -/
theorem submanifold_extension :
    Specs.SmoothManifolds.Ch03.SubmanifoldExtension.submanifold_extensionType.{v} := by
  intro m n k a b N _ T s t S hf g hg
  let := t
  have hrange : range (Subtype.val : s → N) = s := Subtype.range_val
  constructor
  · obtain ⟨U, hU, hsub, G, hG, heq⟩ :=
      embedding_extension_neighborhood S T Subtype.val hf g hg
    exact ⟨U, hU, hrange ▸ hsub, G ∘ Subtype.val,
      euclidean_smooth_restrict_open hU hG, heq⟩
  · intro hclosed
    exact embedding_extension_closed S T Subtype.val hf (hrange.symm ▸ hclosed) g hg

/-- The scalar subset statement, with a function defined on the open
neighborhood itself and a global function when the subset is closed. -/
theorem submanifold_scalar_extension :
    Specs.SmoothManifolds.Ch03.SubmanifoldExtension.submanifold_scalar_extensionType.{v} := by
  intro m n a b N _ T s t S hf g hg
  let := t
  obtain ⟨hneigh, hclosed⟩ := submanifold_extension T s t S hf
    (fun x (_ : Fin 1) => g x) hg
  constructor
  · obtain ⟨U, hU, hsub, G, hG, heq⟩ := hneigh
    refine ⟨U, hU, hsub, fun y => G y 0, ?_, ?_⟩
    · intro y
      exact (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ _).mp (hG y) 0
    · intro x
      exact congrFun (heq x) 0
  · intro hs
    obtain ⟨G, hG, heq⟩ := hclosed hs
    refine ⟨fun y => G y 0, ?_, ?_⟩
    · intro y
      exact (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ _).mp (hG y) 0
    · intro x
      exact congrFun (heq x) 0

end SmoothManifolds.SubmanifoldExtension
