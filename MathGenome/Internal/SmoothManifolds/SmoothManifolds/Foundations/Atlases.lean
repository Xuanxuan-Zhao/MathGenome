import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Models
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Atlases
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Analysis.Calculus.TangentCone.Pi
import Mathlib.Analysis.Calculus.TangentCone.Real

namespace SmoothManifolds
open Set TopologicalSpace
open scoped ContDiff

abbrev ContDiffOnModel := @AtlasData.ContDiffOnModel
abbrev ContDiffCompatible := @AtlasData.ContDiffCompatible
abbrev IsAtlas := @AtlasData.IsAtlas
abbrev IsContDiffAtlas := @AtlasData.IsContDiffAtlas
abbrev maximalExtension := @AtlasData.maximalExtension
abbrev IsMaximalContDiffAtlas := @AtlasData.IsMaximalContDiffAtlas
abbrev SmoothStructure := @AtlasData.SmoothStructure
abbrev SmoothManifold := @AtlasData.SmoothManifold
abbrev ParametrizationAtlas := @AtlasData.ParametrizationAtlas
abbrev parametrizationTopology := @AtlasData.parametrizationTopology
abbrev parametrizationChart := @AtlasData.parametrizationChart
noncomputable abbrev parametrizationAtlasOfCover := @AtlasData.parametrizationAtlasOfCover
abbrev parametrizationCharts := @AtlasData.parametrizationCharts

theorem uniqueDiffOn_halfSpaceSet (n : ℕ) : UniqueDiffOn ℝ (halfSpaceSet n) := by
  cases n with
  | zero => exact uniqueDiffOn_univ
  | succ n =>
    have h : halfSpaceSet (n + 1) =
        Set.pi {Fin.last n} (fun _ : Fin (n + 1) => Set.Ici (0 : ℝ)) := by
      ext x
      simp [halfSpaceSet, ModelData.halfSpaceSet]
    rw [h]
    exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Ici 0)

theorem uniqueDiffOn_modelSet (n : ℕ) (kind : ModelKind) :
    UniqueDiffOn ℝ (modelSet n kind) := by
  cases kind with
  | halfSpace => exact uniqueDiffOn_halfSpaceSet n
  | euclidean => exact uniqueDiffOn_univ

theorem uniqueDiffOn_modelDomain {n : ℕ} {kind : ModelKind}
    {s : Set (ModelSpace n kind)} (hs : IsOpen s) :
    UniqueDiffOn ℝ (Subtype.val '' s : Set (Euclidean n)) := by
  obtain ⟨U, hU, hEq⟩ := hs.image_val
  rw [hEq, inter_comm]
  exact (uniqueDiffOn_modelSet n kind).inter hU

theorem iteratedFDeriv_eq_of_model_extensions {n : ℕ} {kind : ModelKind}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : ℕ∞} {s : Set (ModelSpace n kind)} (hs : IsOpen s)
    {U V : Set (Euclidean n)} (hU : IsOpen U) (hV : IsOpen V)
    {f g : Euclidean n → F} (hf : ContDiffOn ℝ r f U) (hg : ContDiffOn ℝ r g V)
    (hfg : ∀ y ∈ s, (y : Euclidean n) ∈ U → (y : Euclidean n) ∈ V →
      f y = g y)
    {x : ModelSpace n kind} (hx : x ∈ s) (hxU : (x : Euclidean n) ∈ U)
    (hxV : (x : Euclidean n) ∈ V) (k : ℕ) (hk : (k : ℕ∞) ≤ r) :
    iteratedFDeriv ℝ k f (x : Euclidean n) = iteratedFDeriv ℝ k g (x : Euclidean n) := by
  let T : Set (Euclidean n) := (Subtype.val '' s) ∩ U ∩ V
  have hT : UniqueDiffOn ℝ T := ((uniqueDiffOn_modelDomain hs).inter hU).inter hV
  have hxT : (x : Euclidean n) ∈ T := ⟨⟨⟨x, hx, rfl⟩, hxU⟩, hxV⟩
  have heq : EqOn f g T := by
    rintro y ⟨⟨⟨z, hz, rfl⟩, hyU⟩, hyV⟩
    exact hfg z hz hyU hyV
  have hk' : (k : ℕ∞ω) ≤ r := by exact_mod_cast hk
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hT
      ((hf.contDiffAt (hU.mem_nhds hxU)).of_le hk') hxT,
    ← iteratedFDerivWithin_eq_iteratedFDeriv hT
      ((hg.contDiffAt (hV.mem_nhds hxV)).of_le hk') hxT]
  exact iteratedFDerivWithin_congr heq hxT k


/-- The atlas calculus uses exactly the upstream local extension convention. -/
theorem contDiffOnModel_iff_modelMapContDiffOn {n : ℕ} {kind : ModelKind}
    (r : ℕ∞) (f : ModelSpace n kind → ModelSpace n kind) (s : Set (ModelSpace n kind)) :
    ContDiffOnModel r f s ↔ ModelMapContDiffOn r s (fun x => f x.val) := by
  constructor
  · intro h x
    obtain ⟨U, hU, hx, g, hg, heq⟩ := h x.val x.property
    exact ⟨U, hU, hx, g, hg, fun y hy => heq y.val y.property hy⟩
  · intro h x hx
    obtain ⟨U, hU, hxU, g, hg, heq⟩ := h ⟨x, hx⟩
    exact ⟨U, hU, hxU, g, hg, fun y hy hyU => heq ⟨y, hy⟩ hyU⟩

theorem contDiffOnModel_mono {n : ℕ} {kind : ModelKind} {r : ℕ∞}
    {f : ModelSpace n kind → ModelSpace n kind} {s t : Set (ModelSpace n kind)}
    (h : ContDiffOnModel r f t) (hst : s ⊆ t) : ContDiffOnModel r f s := by
  intro x hx
  obtain ⟨U, hU, hxU, g, hg, heq⟩ := h x (hst hx)
  exact ⟨U, hU, hxU, g, hg, fun y hy hyU => heq y (hst hy) hyU⟩

theorem contDiffOnModel_comp {n : ℕ} {kind : ModelKind} {r : ℕ∞}
    {f g : ModelSpace n kind → ModelSpace n kind} {s t : Set (ModelSpace n kind)}
    (hf : ContDiffOnModel r f s) (hg : ContDiffOnModel r g t) :
    ContDiffOnModel r (g ∘ f) (s ∩ f ⁻¹' t) := by
  rintro x ⟨hxs, hxt⟩
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := hf x hxs
  obtain ⟨V, hV, hxV, G, hG, hGeq⟩ := hg (f x) hxt
  refine ⟨U ∩ F ⁻¹' V, hF.continuousOn.isOpen_inter_preimage hU hV,
    ⟨hxU, ?_⟩, G ∘ F, hG.comp (hF.mono inter_subset_left) (fun _ hy => hy.2), ?_⟩
  · change F x.val ∈ V
    rwa [hFeq x hxs hxU]
  · rintro y ⟨hys, hyt⟩ ⟨hyU, hyV⟩
    change G (F y.val) = (g (f y)).val
    rw [hFeq y hys hyU]
    exact hGeq (f y) hyt (by
      change F y.val ∈ V at hyV
      rwa [hFeq y hys hyU] at hyV)

theorem contDiffOnModel_locality {n : ℕ} {kind : ModelKind} {r : ℕ∞}
    {f : ModelSpace n kind → ModelSpace n kind} {s : Set (ModelSpace n kind)}
    (h : ∀ x ∈ s, ∃ v, IsOpen v ∧ x ∈ v ∧ ContDiffOnModel r f (s ∩ v)) :
    ContDiffOnModel r f s := by
  intro x hx
  obtain ⟨v, hv, hxv, hf⟩ := h x hx
  obtain ⟨W, hW, hvW⟩ := isOpen_induced_iff.mp hv
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := hf x ⟨hx, hxv⟩
  refine ⟨U ∩ W, hU.inter hW, ⟨hxU, ?_⟩, F, hF.mono inter_subset_left, ?_⟩
  · rw [← hvW] at hxv
    exact hxv
  · rintro y hy ⟨hyU, hyW⟩
    exact hFeq y ⟨hy, by rw [← hvW]; exact hyW⟩ hyU

private def modelPregroupoid (n : ℕ) (kind : ModelKind) (r : ℕ∞) :
    Pregroupoid (ModelSpace n kind) where
  property := ContDiffOnModel r
  comp := fun hf hg _ _ _ => contDiffOnModel_comp hf hg
  id_mem := by
    intro x _
    exact ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, fun _ _ _ => rfl⟩
  locality := fun _ h => contDiffOnModel_locality h
  congr := by
    intro f g s _ heq hf x hx
    obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := hf x hx
    exact ⟨U, hU, hxU, F, hF, fun y hy hyU => by rw [heq y hy]; exact hFeq y hy hyU⟩

private def modelGroupoid (n : ℕ) (kind : ModelKind) (r : ℕ∞) :=
  (modelPregroupoid n kind r).groupoid

private theorem compatible_iff_groupoid {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] (r : ℕ∞) (c d : ModelChart n kind M) :
    ContDiffCompatible r c d ↔ c.symm.trans d ∈ modelGroupoid n kind r := Iff.rfl

theorem contDiffCompatible_symm {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {c d : ModelChart n kind M}
    (h : ContDiffCompatible r c d) : ContDiffCompatible r d c := by
  apply (compatible_iff_groupoid r d c).mpr
  have h' := (modelGroupoid n kind r).symm ((compatible_iff_groupoid r c d).mp h)
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm] using h'

@[instance_reducible] private noncomputable def atlasChartedSpace {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] (A : Set (ModelChart n kind M)) (hA : IsAtlas A) :
    ChartedSpace (ModelSpace n kind) M where
  atlas := A
  chartAt p := Classical.choose (hA p)
  mem_chart_source p := (Classical.choose_spec (hA p)).2
  chart_mem_atlas p := (Classical.choose_spec (hA p)).1

theorem subset_maximalExtension {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {A : Set (ModelChart n kind M)}
    (hA : IsContDiffAtlas r A) : A ⊆ maximalExtension r A := by
  intro c hc d hd
  exact hA.2 c hc d hd

theorem atlas_subset_maximalExtension {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {A B : Set (ModelChart n kind M)}
    (hB : IsContDiffAtlas r B) (hAB : A ⊆ B) : B ⊆ maximalExtension r A := by
  intro c hc d hd
  exact hB.2 c hc d (hAB hd)

theorem maximalExtension_isContDiffAtlas {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {A : Set (ModelChart n kind M)}
    (hA : IsContDiffAtlas r A) : IsContDiffAtlas r (maximalExtension r A) := by
  refine ⟨?_, ?_⟩
  · intro p
    obtain ⟨c, hc, hpc⟩ := hA.1 p
    exact ⟨c, subset_maximalExtension hA hc, hpc⟩
  · intro c hc d hd
    let := atlasChartedSpace A hA.1
    let G := modelGroupoid n kind r
    have mem_max {c : ModelChart n kind M} (hc : c ∈ maximalExtension r A) :
        c ∈ G.maximalAtlas M := by
      intro e he
      exact ⟨(compatible_iff_groupoid r c e).mp (hc e he),
        (compatible_iff_groupoid r e c).mp (contDiffCompatible_symm (hc e he))⟩
    exact (compatible_iff_groupoid r c d).mpr
      (G.compatible_of_mem_maximalAtlas (mem_max hc) (mem_max hd))

theorem maximalExtension_isMaximal {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {A : Set (ModelChart n kind M)}
    (hA : IsContDiffAtlas r A) : IsMaximalContDiffAtlas r (maximalExtension r A) := by
  refine ⟨maximalExtension_isContDiffAtlas hA, ?_⟩
  intro B hB hAB
  exact Subset.antisymm (atlas_subset_maximalExtension hB
    ((subset_maximalExtension hA).trans hAB)) hAB

/-- Every C^r atlas, in particular every smooth atlas, has exactly one maximal extension. -/
theorem exists_unique_maximalExtension {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {A : Set (ModelChart n kind M)}
    (hA : IsContDiffAtlas r A) :
    ∃! B : Set (ModelChart n kind M), IsMaximalContDiffAtlas r B ∧ A ⊆ B := by
  refine ⟨maximalExtension r A, ⟨maximalExtension_isMaximal hA, subset_maximalExtension hA⟩, ?_⟩
  rintro B ⟨hB, hAB⟩
  exact (hB.2 (maximalExtension r A) (maximalExtension_isContDiffAtlas hA)
    (atlas_subset_maximalExtension hB.1 hAB)).symm


/-- The constructed topology is exactly the topology specified by open coordinates
in every parametrization, rather than an arbitrarily chosen compatible topology. -/
theorem isOpen_parametrizationTopology_iff {n : ℕ} {kind : ModelKind} {M : Type*}
    (A : ParametrizationAtlas n kind M) (U : Set M) :
    @IsOpen M (parametrizationTopology A) U ↔
      ∀ e ∈ A.atlas, IsOpen (e '' (U ∩ e.source)) := by
  let : TopologicalSpace M := parametrizationTopology A
  constructor
  · intro hU e he
    exact (A.openPartialHomeomorph e he).isOpen_image_of_subset_source
      (hU.inter (A.openPartialHomeomorph e he).open_source) inter_subset_right
  · intro hU
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    let e := A.openPartialHomeomorph (A.chartAt x) (A.chart_mem_atlas x)
    have hxe : x ∈ e.source := A.mem_chart_source x
    refine ⟨e.source ∩ e ⁻¹' (e '' (U ∩ e.source)), ?_,
      e.isOpen_inter_preimage (hU (A.chartAt x) (A.chart_mem_atlas x)),
      ⟨hxe, ⟨x, ⟨hx, hxe⟩, rfl⟩⟩⟩
    rintro y ⟨hye, z, ⟨hzU, hze⟩, hzy⟩
    have hzy' : z = y := e.injOn hze hye hzy
    exact hzy' ▸ hzU

/-- Every original parametrization becomes an open chart with unchanged maps,
source, and target. -/
theorem parametrizationChart_toPartialEquiv {n : ℕ} {kind : ModelKind} {M : Type*}
    (A : ParametrizationAtlas n kind M) (e : PartialEquiv M (ModelSpace n kind))
    (he : e ∈ A.atlas) :
    letI : TopologicalSpace M := parametrizationTopology A
    (parametrizationChart A e he).toPartialEquiv = e := rfl

theorem parametrizationCharts_cover {n : ℕ} {kind : ModelKind} {M : Type*}
    (A : ParametrizationAtlas n kind M) :
    letI : TopologicalSpace M := parametrizationTopology A
    IsAtlas (parametrizationCharts A) := by
  let : TopologicalSpace M := parametrizationTopology A
  intro x
  exact ⟨A.openPartialHomeomorph (A.chartAt x) (A.chart_mem_atlas x),
    A.toChartedSpace.chart_mem_atlas x, A.mem_chart_source x⟩

/-- A countable chart subcover supplies second countability of the constructed topology. -/
theorem secondCountable_parametrizationTopology {n : ℕ} {kind : ModelKind} {M : Type*}
    (A : ParametrizationAtlas n kind M)
    (B : Set (PartialEquiv M (ModelSpace n kind))) (hB : B.Countable) (hBA : B ⊆ A.atlas)
    (hcover : ∀ p : M, ∃ e ∈ B, p ∈ e.source) :
    @SecondCountableTopology M (parametrizationTopology A) := by
  let : TopologicalSpace M := parametrizationTopology A
  have := hB.to_subtype
  have : ∀ e : B, SecondCountableTopology e.val.source :=
    fun e => (A.openPartialHomeomorph e.val (hBA e.property)).secondCountableTopology_source
  apply secondCountableTopology_of_countable_cover (U := fun e : B => e.val.source)
    (fun e => (A.openPartialHomeomorph e.val (hBA e.property)).open_source)
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨e, heB, hpe⟩ := hcover p
  exact ⟨⟨e, heB⟩, hpe⟩

/-- Hausdorffness is checked separately; no separation conclusion is assumed
in the raw parametrization data. -/
theorem exists_topologicalManifold_from_parametrizations {n : ℕ} {kind : ModelKind}
    {M : Type*} (A : ParametrizationAtlas n kind M)
    (hHaus : @T2Space M (parametrizationTopology A))
    (B : Set (PartialEquiv M (ModelSpace n kind))) (hB : B.Countable) (hBA : B ⊆ A.atlas)
    (hcover : ∀ p : M, ∃ e ∈ B, p ∈ e.source) :
    letI : TopologicalSpace M := parametrizationTopology A
    ∃ T : TopologicalManifold n kind M, T.atlas = parametrizationCharts A := by
  let : TopologicalSpace M := parametrizationTopology A
  exact ⟨⟨hHaus, secondCountable_parametrizationTopology A B hB hBA hcover,
    parametrizationCharts A, parametrizationCharts_cover A⟩, rfl⟩

/-- Smooth transition compatibility gives the maximal smooth structure on the
manifold constructed from parametrizations. -/
theorem exists_smoothManifold_from_parametrizations {n : ℕ} {kind : ModelKind}
    {M : Type*} (A : ParametrizationAtlas n kind M)
    (hHaus : @T2Space M (parametrizationTopology A))
    (B : Set (PartialEquiv M (ModelSpace n kind))) (hB : B.Countable) (hBA : B ⊆ A.atlas)
    (hcover : ∀ p : M, ∃ e ∈ B, p ∈ e.source)
    (hcompat : letI : TopologicalSpace M := parametrizationTopology A
      ∀ e ∈ parametrizationCharts A, ∀ f ∈ parametrizationCharts A,
        ContDiffCompatible (⊤ : ℕ∞) e f) :
    letI : TopologicalSpace M := parametrizationTopology A
    ∃ S : SmoothManifold n kind M,
      S.topologicalManifold.atlas = parametrizationCharts A ∧
      S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (parametrizationCharts A) := by
  let : TopologicalSpace M := parametrizationTopology A
  obtain ⟨T, hT⟩ := exists_topologicalManifold_from_parametrizations A hHaus B hB hBA hcover
  have hAtlas : IsContDiffAtlas (⊤ : ℕ∞) (parametrizationCharts A) :=
    ⟨parametrizationCharts_cover A, hcompat⟩
  exact ⟨⟨T, ⟨maximalExtension (⊤ : ℕ∞) (parametrizationCharts A),
    maximalExtension_isMaximal hAtlas⟩⟩, hT, rfl⟩

end SmoothManifolds
