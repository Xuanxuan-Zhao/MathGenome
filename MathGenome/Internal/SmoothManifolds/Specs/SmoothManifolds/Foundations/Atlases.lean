import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Models
import Mathlib.Geometry.Manifold.ChartedSpace

/-! Canonical atlas objects, independent of the candidate proofs. -/
namespace SmoothManifolds.AtlasData
open Set
open ModelData
universe u

/-- Ambient local extension of a model-valued function on a model subset.
The extension need not preserve the inequalities of the target model. -/
def ContDiffOnModel {n : ℕ} {kind : ModelKind} (r : ℕ∞)
    (f : ModelSpace n kind → ModelSpace n kind) (s : Set (ModelSpace n kind)) : Prop :=
  ∀ x ∈ s, ∃ U : Set (Euclidean n), IsOpen U ∧ x.val ∈ U ∧
    ∃ g : Euclidean n → Euclidean n, ContDiffOn ℝ r g U ∧
      ∀ y ∈ s, y.val ∈ U → g y.val = (f y).val

/-- Both directions of a transition are locally extendible. -/
def ContDiffCompatible {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (r : ℕ∞) (c d : ModelChart n kind M) : Prop :=
  let e := c.symm.trans d
  ContDiffOnModel r e e.source ∧ ContDiffOnModel r e.symm e.target

/-- An atlas means a chart cover, allowing the empty cover of an empty space. -/
def IsAtlas {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (A : Set (ModelChart n kind M)) : Prop :=
  ∀ p : M, ∃ c ∈ A, p ∈ c.source

def IsContDiffAtlas {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (r : ℕ∞) (A : Set (ModelChart n kind M)) : Prop :=
  IsAtlas A ∧ ∀ c ∈ A, ∀ d ∈ A, ContDiffCompatible r c d

/-- All charts compatible with every chart of the given atlas. -/
def maximalExtension {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (r : ℕ∞) (A : Set (ModelChart n kind M)) : Set (ModelChart n kind M) :=
  {c | ∀ d ∈ A, ContDiffCompatible r c d}

/-- Maximality is inclusion maximality among compatible chart covers. -/
def IsMaximalContDiffAtlas {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (r : ℕ∞) (A : Set (ModelChart n kind M)) : Prop :=
  IsContDiffAtlas r A ∧ ∀ B, IsContDiffAtlas r B → A ⊆ B → B = A

abbrev SmoothStructure (n : ℕ) (kind : ModelKind) (M : Type u) [TopologicalSpace M] :=
  {A : Set (ModelChart n kind M) // IsMaximalContDiffAtlas (⊤ : ℕ∞) A}

/-- A topological manifold equipped with a maximal smooth atlas. -/
structure SmoothManifold (n : ℕ) (kind : ModelKind) (M : Type u) [TopologicalSpace M] where
  topologicalManifold : TopologicalManifold n kind M
  smoothStructure : SmoothStructure n kind M

/-- A cover by set theoretic charts with relatively open coordinate overlaps
and continuous transition maps. Swapping the two charts supplies the inverse. -/
abbrev ParametrizationAtlas (n : ℕ) (kind : ModelKind) (M : Type u) :=
  ChartedSpaceCore (ModelSpace n kind) M

abbrev parametrizationTopology {n : ℕ} {kind : ModelKind} {M : Type u}
    (A : ParametrizationAtlas n kind M) := A.toTopologicalSpace

abbrev parametrizationChart {n : ℕ} {kind : ModelKind} {M : Type u}
    (A : ParametrizationAtlas n kind M) (e : PartialEquiv M (ModelSpace n kind))
    (he : e ∈ A.atlas) := A.openPartialHomeomorph e he

/-- Choice of a chart from an arbitrary chart cover adds no hypotheses. -/
noncomputable def parametrizationAtlasOfCover {n : ℕ} {kind : ModelKind} {M : Type u}
    (A : Set (PartialEquiv M (ModelSpace n kind)))
    (hcover : ∀ p : M, ∃ e ∈ A, p ∈ e.source)
    (hopen : ∀ e ∈ A, ∀ f ∈ A, IsOpen (e.symm.trans f).source)
    (hcont : ∀ e ∈ A, ∀ f ∈ A, ContinuousOn (e.symm.trans f) (e.symm.trans f).source) :
    ParametrizationAtlas n kind M where
  atlas := A
  chartAt p := Classical.choose (hcover p)
  mem_chart_source p := (Classical.choose_spec (hcover p)).2
  chart_mem_atlas p := (Classical.choose_spec (hcover p)).1
  open_source e f he hf := hopen e he f hf
  continuousOn_toFun e f he hf := hcont e he f hf

abbrev parametrizationCharts {n : ℕ} {kind : ModelKind} {M : Type u}
    (A : ParametrizationAtlas n kind M) := A.toChartedSpace.atlas

end SmoothManifolds.AtlasData

namespace Specs.SmoothManifolds.Foundations.Atlases

open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
open Set TopologicalSpace
universe u

/-! Independent full definition types/values and full theorem propositions. -/

def ContDiffOnModelType :=
  {n : ℕ} → {kind : ModelKind} → ℕ∞ →
    (ModelSpace n kind → ModelSpace n kind) → Set (ModelSpace n kind) → Prop

noncomputable def ContDiffOnModelValue : ContDiffOnModelType :=
  @AtlasData.ContDiffOnModel

def ContDiffCompatibleType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    ℕ∞ → ModelChart n kind M → ModelChart n kind M → Prop

noncomputable def ContDiffCompatibleValue : ContDiffCompatibleType :=
  @AtlasData.ContDiffCompatible

def IsAtlasType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    Set (ModelChart n kind M) → Prop

noncomputable def IsAtlasValue : IsAtlasType :=
  @AtlasData.IsAtlas

def IsContDiffAtlasType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    ℕ∞ → Set (ModelChart n kind M) → Prop

noncomputable def IsContDiffAtlasValue : IsContDiffAtlasType :=
  @AtlasData.IsContDiffAtlas

def maximalExtensionType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    ℕ∞ → Set (ModelChart n kind M) → Set (ModelChart n kind M)

noncomputable def maximalExtensionValue : maximalExtensionType :=
  @AtlasData.maximalExtension

def IsMaximalContDiffAtlasType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    ℕ∞ → Set (ModelChart n kind M) → Prop

noncomputable def IsMaximalContDiffAtlasValue : IsMaximalContDiffAtlasType :=
  @AtlasData.IsMaximalContDiffAtlas

def SmoothStructureType :=
  ℕ → ModelKind → (M : Type u) → [TopologicalSpace M] → Type u

noncomputable def SmoothStructureValue : SmoothStructureType :=
  @AtlasData.SmoothStructure

def SmoothManifoldType :=
  ℕ → ModelKind → (M : Type u) → [TopologicalSpace M] → Type u

noncomputable def SmoothManifoldValue : SmoothManifoldType :=
  @AtlasData.SmoothManifold

def ParametrizationAtlasType :=
  ℕ → ModelKind → Type u → Type u

noncomputable def ParametrizationAtlasValue : ParametrizationAtlasType :=
  @AtlasData.ParametrizationAtlas

def parametrizationTopologyType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
    ParametrizationAtlas n kind M → TopologicalSpace M

noncomputable def parametrizationTopologyValue : parametrizationTopologyType :=
  @AtlasData.parametrizationTopology

def parametrizationChartType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
    (A : ParametrizationAtlas n kind M) → (e : PartialEquiv M (ModelSpace n kind)) →
    e ∈ A.atlas → @ModelChart n kind M (parametrizationTopology A)

noncomputable def parametrizationChartValue : parametrizationChartType :=
  @AtlasData.parametrizationChart

def parametrizationAtlasOfCoverType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
    (A : Set (PartialEquiv M (ModelSpace n kind))) →
    (∀ p : M, ∃ e ∈ A, p ∈ e.source) →
    (∀ e ∈ A, ∀ f ∈ A, IsOpen (e.symm.trans f).source) →
    (∀ e ∈ A, ∀ f ∈ A, ContinuousOn (e.symm.trans f) (e.symm.trans f).source) →
    ParametrizationAtlas n kind M

noncomputable def parametrizationAtlasOfCoverValue : parametrizationAtlasOfCoverType :=
  @AtlasData.parametrizationAtlasOfCover

def parametrizationChartsType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
    (A : ParametrizationAtlas n kind M) → Set (@ModelChart n kind M (parametrizationTopology A))

noncomputable def parametrizationChartsValue : parametrizationChartsType :=
  @AtlasData.parametrizationCharts

def uniqueDiffOn_halfSpaceSetType :=
  ∀ (n : ℕ),
    UniqueDiffOn ℝ (halfSpaceSet n)

def uniqueDiffOn_modelSetType :=
  ∀ (n : ℕ) (kind : ModelKind),
    UniqueDiffOn ℝ (modelSet n kind)

def uniqueDiffOn_modelDomainType :=
  ∀ {n : ℕ} {kind : ModelKind}
    {s : Set (ModelSpace n kind)} (hs : IsOpen s),
    UniqueDiffOn ℝ (Subtype.val '' s : Set (Euclidean n))

def iteratedFDeriv_eq_of_model_extensionsType :=
  ∀ {n : ℕ} {kind : ModelKind}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : ℕ∞} {s : Set (ModelSpace n kind)} (hs : IsOpen s)
    {U V : Set (Euclidean n)} (hU : IsOpen U) (hV : IsOpen V)
    {f g : Euclidean n → F} (hf : ContDiffOn ℝ r f U) (hg : ContDiffOn ℝ r g V)
    (hfg : ∀ y ∈ s, (y : Euclidean n) ∈ U → (y : Euclidean n) ∈ V →
      f y = g y)
    {x : ModelSpace n kind} (hx : x ∈ s) (hxU : (x : Euclidean n) ∈ U)
    (hxV : (x : Euclidean n) ∈ V) (k : ℕ) (hk : (k : ℕ∞) ≤ r),
    iteratedFDeriv ℝ k f (x : Euclidean n) = iteratedFDeriv ℝ k g (x : Euclidean n)

def contDiffOnModel_iff_modelMapContDiffOnType :=
  ∀ {n : ℕ} {kind : ModelKind}
    (r : ℕ∞) (f : ModelSpace n kind → ModelSpace n kind) (s : Set (ModelSpace n kind)),
    ContDiffOnModel r f s ↔ ModelMapContDiffOn r s (fun x => f x.val)

def contDiffOnModel_monoType :=
  ∀ {n : ℕ} {kind : ModelKind} {r : ℕ∞}
    {f : ModelSpace n kind → ModelSpace n kind} {s t : Set (ModelSpace n kind)}
    (h : ContDiffOnModel r f t) (hst : s ⊆ t),
    ContDiffOnModel r f s

def contDiffOnModel_compType :=
  ∀ {n : ℕ} {kind : ModelKind} {r : ℕ∞}
    {f g : ModelSpace n kind → ModelSpace n kind} {s t : Set (ModelSpace n kind)}
    (hf : ContDiffOnModel r f s) (hg : ContDiffOnModel r g t),
    ContDiffOnModel r (g ∘ f) (s ∩ f ⁻¹' t)

def contDiffOnModel_localityType :=
  ∀ {n : ℕ} {kind : ModelKind} {r : ℕ∞}
    {f : ModelSpace n kind → ModelSpace n kind} {s : Set (ModelSpace n kind)}
    (h : ∀ x ∈ s, ∃ v, IsOpen v ∧ x ∈ v ∧ ContDiffOnModel r f (s ∩ v)),
    ContDiffOnModel r f s

def contDiffCompatible_symmType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {c d : ModelChart n kind M}
    (h : ContDiffCompatible r c d),
    ContDiffCompatible r d c

def subset_maximalExtensionType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {A : Set (ModelChart n kind M)}
    (hA : IsContDiffAtlas r A),
    A ⊆ maximalExtension r A

def atlas_subset_maximalExtensionType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {A B : Set (ModelChart n kind M)}
    (hB : IsContDiffAtlas r B) (hAB : A ⊆ B),
    B ⊆ maximalExtension r A

def maximalExtension_isContDiffAtlasType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {A : Set (ModelChart n kind M)}
    (hA : IsContDiffAtlas r A),
    IsContDiffAtlas r (maximalExtension r A)

def maximalExtension_isMaximalType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {A : Set (ModelChart n kind M)}
    (hA : IsContDiffAtlas r A),
    IsMaximalContDiffAtlas r (maximalExtension r A)

def exists_unique_maximalExtensionType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type*}
    [TopologicalSpace M] {r : ℕ∞} {A : Set (ModelChart n kind M)}
    (hA : IsContDiffAtlas r A),
    ∃! B : Set (ModelChart n kind M), IsMaximalContDiffAtlas r B ∧ A ⊆ B

def isOpen_parametrizationTopology_iffType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type*}
    (A : ParametrizationAtlas n kind M) (U : Set M),
    @IsOpen M (parametrizationTopology A) U ↔
      ∀ e ∈ A.atlas, IsOpen (e '' (U ∩ e.source))

def parametrizationChart_toPartialEquivType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type*}
    (A : ParametrizationAtlas n kind M) (e : PartialEquiv M (ModelSpace n kind))
    (he : e ∈ A.atlas),
    letI : TopologicalSpace M := parametrizationTopology A
    (parametrizationChart A e he).toPartialEquiv = e

def parametrizationCharts_coverType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type*}
    (A : ParametrizationAtlas n kind M),
    letI : TopologicalSpace M := parametrizationTopology A
    IsAtlas (parametrizationCharts A)

def secondCountable_parametrizationTopologyType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type*}
    (A : ParametrizationAtlas n kind M)
    (B : Set (PartialEquiv M (ModelSpace n kind))) (hB : B.Countable) (hBA : B ⊆ A.atlas)
    (hcover : ∀ p : M, ∃ e ∈ B, p ∈ e.source),
    @SecondCountableTopology M (parametrizationTopology A)

def exists_topologicalManifold_from_parametrizationsType :=
  ∀ {n : ℕ} {kind : ModelKind}
    {M : Type*} (A : ParametrizationAtlas n kind M)
    (hHaus : @T2Space M (parametrizationTopology A))
    (B : Set (PartialEquiv M (ModelSpace n kind))) (hB : B.Countable) (hBA : B ⊆ A.atlas)
    (hcover : ∀ p : M, ∃ e ∈ B, p ∈ e.source),
    letI : TopologicalSpace M := parametrizationTopology A
    ∃ T : TopologicalManifold n kind M, T.atlas = parametrizationCharts A

def exists_smoothManifold_from_parametrizationsType :=
  ∀ {n : ℕ} {kind : ModelKind}
    {M : Type*} (A : ParametrizationAtlas n kind M)
    (hHaus : @T2Space M (parametrizationTopology A))
    (B : Set (PartialEquiv M (ModelSpace n kind))) (hB : B.Countable) (hBA : B ⊆ A.atlas)
    (hcover : ∀ p : M, ∃ e ∈ B, p ∈ e.source)
    (hcompat : letI : TopologicalSpace M := parametrizationTopology A
      ∀ e ∈ parametrizationCharts A, ∀ f ∈ parametrizationCharts A,
        ContDiffCompatible (⊤ : ℕ∞) e f),
    letI : TopologicalSpace M := parametrizationTopology A
    ∃ S : SmoothManifold n kind M,
      S.topologicalManifold.atlas = parametrizationCharts A ∧
      S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (parametrizationCharts A)

end Specs.SmoothManifolds.Foundations.Atlases
