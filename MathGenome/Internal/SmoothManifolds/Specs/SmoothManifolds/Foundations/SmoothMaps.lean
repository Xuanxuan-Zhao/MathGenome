import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Atlases
import Mathlib.Topology.Homeomorph.Defs

/-! Local coordinate definitions for maps, independent of their proofs.

`LocalCoordinateExtension` uses one ambient open neighborhood and one C^r
extension, including at r = infinity. Agreement is on a neighborhood in the
source. For an actual chart this is precisely agreement on a relatively open
model neighborhood. No extension is required to remain in the target model.
The sets in `ManifoldContDiffOn` indicate where a map is locally C^r; restriction
and gluing below concern open subsets. Arbitrary-subset extension is defined
separately, with an actual extension on a neighborhood of each subset point.
-/
namespace SmoothManifolds.MapData
open ModelData AtlasData Set Filter
open scoped Topology
universe u v w

/-- A germ represented by one C^r map on an ambient Euclidean open set. -/
def LocalCoordinateExtension {X : Type u} [TopologicalSpace X] {n m : ℕ}
    (r : ℕ∞) (ι : X → Euclidean n) (f : X → Euclidean m) (x : X) : Prop :=
  ∃ U : Set (Euclidean n), IsOpen U ∧ ι x ∈ U ∧
    ∃ F : Euclidean n → Euclidean m, ContDiffOn ℝ r F U ∧
      (fun y => F (ι y)) =ᶠ[𝓝 x] f

section Maps
variable {n m l : ℕ} {a b c : ModelKind}
  {M : Type u} {N : Type v} {P : Type w}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

/-- Local smoothness of the coordinate expression, at a point in both charts. -/
def ChartContDiffAt (r : ℕ∞) (e : ModelChart n a M) (d : ModelChart m b N)
    (f : M → N) (x : M) : Prop :=
  LocalCoordinateExtension r (fun y => (e y).val) (fun y => (d (f y)).val) x

/-- The all-charts definition includes continuity and the ambient extension test. -/
def ManifoldContDiffAt (r : ℕ∞) (A : Set (ModelChart n a M))
    (B : Set (ModelChart m b N)) (f : M → N) (x : M) : Prop :=
  ContinuousAt f x ∧ ∀ e ∈ A, ∀ d ∈ B,
    x ∈ e.source → f x ∈ d.source → ChartContDiffAt r e d f x

def ManifoldContDiffOn (r : ℕ∞) (A : Set (ModelChart n a M))
    (B : Set (ModelChart m b N)) (f : M → N) (s : Set M) : Prop :=
  ∀ x ∈ s, ManifoldContDiffAt r A B f x

def ManifoldContDiff (r : ℕ∞) (A : Set (ModelChart n a M))
    (B : Set (ModelChart m b N)) (f : M → N) : Prop :=
  ∀ x, ManifoldContDiffAt r A B f x

abbrev ManifoldSmoothAt := @ManifoldContDiffAt n m a b M N _ _ (⊤ : ℕ∞)
abbrev ManifoldSmoothOn := @ManifoldContDiffOn n m a b M N _ _ (⊤ : ℕ∞)
abbrev ManifoldSmooth := @ManifoldContDiff n m a b M N _ _ (⊤ : ℕ∞)

/-- One pair of charts suffices locally; the whole source neighborhood maps
into the target chart and its coordinate expression is C^r there. -/
def LocalChartTestOn (r : ℕ∞) (A : Set (ModelChart n a M))
    (B : Set (ModelChart m b N)) (f : M → N) (s : Set M) : Prop :=
  ∀ x ∈ s, ∃ e ∈ A, ∃ d ∈ B, ∃ V : Set M,
    IsOpen V ∧ x ∈ V ∧ V ⊆ e.source ∧ MapsTo f V d.source ∧
      ∀ y ∈ V, ChartContDiffAt r e d f y

/-- A bijection with C^r inverse; continuity is a consequence of the map tests. -/
structure ContDiffDiffeomorph (r : ℕ∞) (A : Set (ModelChart n a M))
    (B : Set (ModelChart m b N)) where
  toEquiv : M ≃ N
  contDiff_toFun : ManifoldContDiff r A B toEquiv
  contDiff_invFun : ManifoldContDiff r B A toEquiv.symm

abbrev Diffeomorph := @ContDiffDiffeomorph n m a b M N _ _ (⊤ : ℕ∞)

/-- Smoothness in both directions supplies the underlying homeomorphism. -/
def ContDiffDiffeomorph.toHomeomorph {r : ℕ∞} {A : Set (ModelChart n a M)}
    {B : Set (ModelChart m b N)} (h : ContDiffDiffeomorph r A B) : M ≃ₜ N where
  toEquiv := h.toEquiv
  continuous_toFun := continuous_iff_continuousAt.mpr (fun x => (h.contDiff_toFun x).1)
  continuous_invFun := continuous_iff_continuousAt.mpr (fun x => (h.contDiff_invFun x).1)

/-- Restrict the charts to an open subspace; the empty subspace has empty atlas. -/
noncomputable def openSubsetAtlas (A : Set (ModelChart n a M)) (s : Set M) (hs : IsOpen s) :
    Set (ModelChart n a s) :=
  {e | ∃ hne : Nonempty s, ∃ d ∈ A, e = d.subtypeRestr (s := ⟨s, hs⟩) hne}

/-- Transport charts by a homeomorphism; their source/target and maps are actual
open partial homeomorphisms, rather than an assumed compatibility certificate. -/
def transportAtlas (h : M ≃ₜ N) (A : Set (ModelChart n a M)) :
    Set (ModelChart n a N) :=
  (fun e => h.symm.toOpenPartialHomeomorph.trans e) '' A

/-- Euclidean-valued maps, using the same source atlas and extension convention. -/
def ManifoldContDiffToEuclideanAt (r : ℕ∞) (A : Set (ModelChart n a M))
    (f : M → Euclidean m) (x : M) : Prop :=
  ContinuousAt f x ∧ ∀ e ∈ A, x ∈ e.source →
    LocalCoordinateExtension r (fun y => (e y).val) f x

/-- An arbitrary subset imposes no closedness, openness, or regularity hypothesis.
At every point there is an actual C^r manifold-neighborhood extension. -/
def LocallyContDiffOnSubset (r : ℕ∞) (A : Set (ModelChart n a M))
    (s : Set M) (f : s → Euclidean m) : Prop :=
  ∀ x : s, ∃ U : Set M, IsOpen U ∧ x.val ∈ U ∧
    ∃ g : M → Euclidean m,
      (∀ y ∈ U, ManifoldContDiffToEuclideanAt r A g y) ∧
        ∀ y : s, y.val ∈ U → g y.val = f y

abbrev LocallySmoothOnSubset := @LocallyContDiffOnSubset n m a M _ (⊤ : ℕ∞)

/-- The analogous extension convention for a boundaryless manifold target. -/
def LocallyContDiffOnSubsetToManifold (r : ℕ∞) (A : Set (ModelChart n a M))
    (B : Set (ModelChart m .euclidean N)) (s : Set M) (f : s → N) : Prop :=
  ∀ x : s, ∃ U : Set M, IsOpen U ∧ x.val ∈ U ∧
    ∃ g : M → N, ManifoldContDiffOn r A B g U ∧
      ∀ y : s, y.val ∈ U → g y.val = f y

abbrev LocallySmoothOnSubsetToManifold :=
  @LocallyContDiffOnSubsetToManifold n m a M N _ _ (⊤ : ℕ∞)

end Maps

/-- Specialization to the source's maximal smooth structures. -/
def IsSmoothMap {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N) : Prop :=
  ManifoldSmooth S.smoothStructure.val T.smoothStructure.val f

end SmoothManifolds.MapData

namespace Specs.SmoothManifolds.Foundations.SmoothMaps
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
open Set Filter
open scoped Topology
universe u v w

-- Definition contracts (the canonical data above are available without proofs).

def LocalCoordinateExtensionType :=
  {X : Type u} → [TopologicalSpace X] → {n m : ℕ} → ℕ∞ → (X → Euclidean n) → (X → Euclidean m) → X → Prop

def LocalCoordinateExtensionValue : LocalCoordinateExtensionType :=
  @MapData.LocalCoordinateExtension

def ChartContDiffAtType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → ℕ∞ → ModelChart n a M → ModelChart m b N → (M → N) → M → Prop

def ChartContDiffAtValue : ChartContDiffAtType :=
  @MapData.ChartContDiffAt

def ManifoldContDiffAtType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → ℕ∞ → Set (ModelChart n a M) → Set (ModelChart m b N) → (M → N) → M → Prop

def ManifoldContDiffAtValue : ManifoldContDiffAtType :=
  @MapData.ManifoldContDiffAt

def ManifoldContDiffOnType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → ℕ∞ → Set (ModelChart n a M) → Set (ModelChart m b N) → (M → N) → Set M → Prop

def ManifoldContDiffOnValue : ManifoldContDiffOnType :=
  @MapData.ManifoldContDiffOn

def ManifoldContDiffType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → ℕ∞ → Set (ModelChart n a M) → Set (ModelChart m b N) → (M → N) → Prop

def ManifoldContDiffValue : ManifoldContDiffType :=
  @MapData.ManifoldContDiff

def ManifoldSmoothAtType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → Set (ModelChart n a M) → Set (ModelChart m b N) → (M → N) → M → Prop

def ManifoldSmoothAtValue : ManifoldSmoothAtType :=
  @MapData.ManifoldSmoothAt

def ManifoldSmoothOnType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → Set (ModelChart n a M) → Set (ModelChart m b N) → (M → N) → Set M → Prop

def ManifoldSmoothOnValue : ManifoldSmoothOnType :=
  @MapData.ManifoldSmoothOn

def ManifoldSmoothType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → Set (ModelChart n a M) → Set (ModelChart m b N) → (M → N) → Prop

def ManifoldSmoothValue : ManifoldSmoothType :=
  @MapData.ManifoldSmooth

def LocalChartTestOnType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → ℕ∞ → Set (ModelChart n a M) → Set (ModelChart m b N) → (M → N) → Set M → Prop

def LocalChartTestOnValue : LocalChartTestOnType :=
  @MapData.LocalChartTestOn

def ContDiffDiffeomorphType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → ℕ∞ → Set (ModelChart n a M) → Set (ModelChart m b N) → Type (max u v)

def ContDiffDiffeomorphValue : ContDiffDiffeomorphType :=
  @MapData.ContDiffDiffeomorph

def DiffeomorphType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → Set (ModelChart n a M) → Set (ModelChart m b N) → Type (max u v)

def DiffeomorphValue : DiffeomorphType :=
  @MapData.Diffeomorph

def transportAtlasType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → (M ≃ₜ N) → Set (ModelChart n a M) → Set (ModelChart n a N)

def transportAtlasValue : transportAtlasType :=
  @MapData.transportAtlas

def ManifoldContDiffToEuclideanAtType :=
  {n m : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → ℕ∞ → Set (ModelChart n a M) → (M → Euclidean m) → M → Prop

def ManifoldContDiffToEuclideanAtValue : ManifoldContDiffToEuclideanAtType :=
  @MapData.ManifoldContDiffToEuclideanAt

def LocallyContDiffOnSubsetType :=
  {n m : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → ℕ∞ → Set (ModelChart n a M) → (s : Set M) → (s → Euclidean m) → Prop

def LocallyContDiffOnSubsetValue : LocallyContDiffOnSubsetType :=
  @MapData.LocallyContDiffOnSubset

def LocallySmoothOnSubsetType :=
  {n m : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → Set (ModelChart n a M) → (s : Set M) → (s → Euclidean m) → Prop

def LocallySmoothOnSubsetValue : LocallySmoothOnSubsetType :=
  @MapData.LocallySmoothOnSubset

def LocallyContDiffOnSubsetToManifoldType :=
  {n m : ℕ} → {a : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → ℕ∞ → Set (ModelChart n a M) → Set (ModelChart m .euclidean N) → (s : Set M) → (s → N) → Prop

def LocallyContDiffOnSubsetToManifoldValue : LocallyContDiffOnSubsetToManifoldType :=
  @MapData.LocallyContDiffOnSubsetToManifold

def LocallySmoothOnSubsetToManifoldType :=
  {n m : ℕ} → {a : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → Set (ModelChart n a M) → Set (ModelChart m .euclidean N) → (s : Set M) → (s → N) → Prop

def LocallySmoothOnSubsetToManifoldValue : LocallySmoothOnSubsetToManifoldType :=
  @MapData.LocallySmoothOnSubsetToManifold

def IsSmoothMapType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → SmoothManifold n a M → SmoothManifold m b N → (M → N) → Prop

def IsSmoothMapValue : IsSmoothMapType :=
  @MapData.IsSmoothMap

def toHomeomorphType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} →
    [TopologicalSpace M] → [TopologicalSpace N] → {r : ℕ∞} →
    {A : Set (ModelChart n a M)} → {B : Set (ModelChart m b N)} →
    ContDiffDiffeomorph r A B → (M ≃ₜ N)

def toHomeomorphValue : toHomeomorphType := @MapData.ContDiffDiffeomorph.toHomeomorph

def openSubsetAtlasType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    Set (ModelChart n a M) → (s : Set M) → IsOpen s → Set (ModelChart n a s)

noncomputable def openSubsetAtlasValue : openSubsetAtlasType := @MapData.openSubsetAtlas

section Theorems
variable {n m l : ℕ} {a b c : ModelKind}
  {M : Type u} {N : Type v} {P : Type w}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

/-- Exact bridge from germ agreement to the canonical model-domain convention. -/
def chartContDiffAt_iff_modelExtensionType :=
  ∀ {n : ℕ} {m : ℕ} {a : ModelKind} {b : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r : ℕ∞) (e : ModelChart n a M) (d : ModelChart m b N)
    (f : M → N) (x : M) (hx : x ∈ e.source) (hfx : f x ∈ d.source)
    (hf : ContinuousAt f x),
    ChartContDiffAt r e d f x ↔
      ∃ U : Set (Euclidean n), IsOpen U ∧ (e x).val ∈ U ∧
        ∃ F : Euclidean n → Euclidean m, ContDiffOn ℝ r F U ∧
          ∀ y : ModelSpace n a, y ∈ e.target → f (e.symm y) ∈ d.source →
            y.val ∈ U → F y.val = (d (f (e.symm y))).val

/-- The all-charts definition is equivalent to testing any one pair at a point. -/
def manifoldContDiffAt_iff_oneChartType :=
  ∀ {n : ℕ} {m : ℕ} {a : ModelKind} {b : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (hA : IsContDiffAtlas r A) (hB : IsContDiffAtlas r B)
    (f : M → N) (x : M),
    ManifoldContDiffAt r A B f x ↔
      ContinuousAt f x ∧ ∃ e ∈ A, ∃ d ∈ B,
        x ∈ e.source ∧ f x ∈ d.source ∧ ChartContDiffAt r e d f x

/-- Continuous local chart test with actual neighborhoods mapping into the target chart. -/
def manifoldContDiffOn_iff_localChartTestType :=
  ∀ {n : ℕ} {m : ℕ} {a : ModelKind} {b : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (hA : IsContDiffAtlas r A) (hB : IsContDiffAtlas r B)
    (f : M → N) (s : Set M) (hs : IsOpen s) (hf : ContinuousOn f s),
    ManifoldContDiffOn r A B f s ↔ LocalChartTestOn r A B f s

/-- Chart independence includes enlarging either atlas to its maximal extension. -/
def manifoldContDiff_maximalExtension_iffType :=
  ∀ {n : ℕ} {m : ℕ} {a : ModelKind} {b : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (hA : IsContDiffAtlas r A) (hB : IsContDiffAtlas r B) (f : M → N),
    ManifoldContDiff r (maximalExtension r A) (maximalExtension r B) f ↔
      ManifoldContDiff r A B f

def manifoldContDiffOn_monoType :=
  ∀ {n : ℕ} {m : ℕ} {a : ModelKind} {b : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (f : M → N) (s t : Set M),
    ManifoldContDiffOn r A B f t → s ⊆ t → ManifoldContDiffOn r A B f s

/-- Regularity and continuity glue, without a separate global continuity assumption. -/
def manifoldContDiffOn_glueType :=
  ∀ {n : ℕ} {m : ℕ} {a : ModelKind} {b : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (f : M → N) (s : Set M) {ι : Type*} (U : ι → Set M),
    (∀ i, IsOpen (U i)) → s ⊆ ⋃ i, U i →
    (∀ i, ManifoldContDiffOn r A B f (s ∩ U i)) →
      ManifoldContDiffOn r A B f s ∧ ContinuousOn f s

/-- Locality also for distinct maps that agree on overlapping open patches. -/
def manifoldContDiffOn_of_local_eqType :=
  ∀ {n : ℕ} {m : ℕ} {a : ModelKind} {b : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (f : M → N) (s : Set M),
    (∀ x ∈ s, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ g : M → N, EqOn f g U ∧ ManifoldContDiffOn r A B g U) →
    ManifoldContDiffOn r A B f s ∧ ContinuousOn f s

def manifoldContDiff_compType :=
  ∀ {n : ℕ} {m : ℕ} {l : ℕ} {a : ModelKind} {b : ModelKind} {c : ModelKind} {M : Type u} {N : Type v} {P : Type w} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (C : Set (ModelChart l c P)) (hB : IsAtlas B) (f : M → N) (g : N → P),
    ManifoldContDiff r A B f → ManifoldContDiff r B C g →
      ManifoldContDiff r A C (g ∘ f)

def manifoldContDiffOn_compType :=
  ∀ {n : ℕ} {m : ℕ} {l : ℕ} {a : ModelKind} {b : ModelKind} {c : ModelKind} {M : Type u} {N : Type v} {P : Type w} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (C : Set (ModelChart l c P)) (hB : IsAtlas B)
    (f : M → N) (g : N → P) (s : Set M) (t : Set N),
    IsOpen s → IsOpen t → MapsTo f s t →
    ManifoldContDiffOn r A B f s → ManifoldContDiffOn r B C g t →
      ManifoldContDiffOn r A C (g ∘ f) s

def manifoldContDiff_idType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)), IsContDiffAtlas r A →
    ManifoldContDiff r A A id

/-- C^0 and every lower order are included, without a positive-order hypothesis. -/
def manifoldContDiff_of_leType :=
  ∀ {n : ℕ} {m : ℕ} {a : ModelKind} {b : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r q : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (f : M → N), q ≤ r → ManifoldContDiff r A B f → ManifoldContDiff q A B f

/-- Open-subspace restriction uses the actual restricted charts. -/
def manifoldContDiff_restrict_openType :=
  ∀ {n : ℕ} {m : ℕ} {a : ModelKind} {b : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    (f : M → N) (s : Set M) (hs : IsOpen s),
    let R : Set (ModelChart n a s) :=
      {e | ∃ hne : Nonempty s, ∃ d ∈ A,
        e = d.subtypeRestr (s := ⟨s, hs⟩) hne}
    ManifoldContDiffOn r A B f s ↔
      ManifoldContDiff r R B (fun x : s => f x.val)

/-- Any atlas is transported by a homeomorphism with the same regularity. -/
def transportAtlas_isContDiffAtlasType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (h : M ≃ₜ N),
    IsContDiffAtlas r A → IsContDiffAtlas r (transportAtlas h A)

/-- Across different dimensions or permitted model kinds, every transported
chart and every target chart have locally C^r transitions in both directions. -/
def diffeomorph_transport_chartsType :=
  ∀ {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N)) (h : M ≃ₜ N),
    ManifoldContDiff r A B h → ManifoldContDiff r B A h.symm →
    ∀ e ∈ A, ∀ d ∈ B, ∀ y : N, h.symm y ∈ e.source → y ∈ d.source →
      ChartContDiffAt r (h.symm.toOpenPartialHomeomorph.trans e) d id y ∧
      ChartContDiffAt r d (h.symm.toOpenPartialHomeomorph.trans e) id y

/-- A diffeomorphism identifies maximal atlases by transport. -/
def diffeomorph_transportAtlasType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart n a N))
    (hA : IsMaximalContDiffAtlas r A) (hB : IsMaximalContDiffAtlas r B)
    (h : M ≃ₜ N),
    ManifoldContDiff r A B h → ManifoldContDiff r B A h.symm →
      transportAtlas h A = B

/-- The transported atlas makes the transporting homeomorphism a C^r diffeomorphism. -/
def transportAtlas_mapsType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (h : M ≃ₜ N),
    IsContDiffAtlas r A →
      ManifoldContDiff r A (transportAtlas h A) h ∧
      ManifoldContDiff r (transportAtlas h A) A h.symm

/-- Compatible maps defined only on cover members have a unique global smooth gluing.
Continuity of that gluing is part of the conclusion, not a hypothesis. -/
def exists_unique_manifoldContDiff_gluingType :=
  ∀ {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
    {ι : Type w} (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x : M, ∃ i, x ∈ U i) (F : ∀ i, U i → N),
    (∀ i j (x : M) (hi : x ∈ U i) (hj : x ∈ U j), F i ⟨x, hi⟩ = F j ⟨x, hj⟩) →
    (∀ i, ManifoldContDiff r (openSubsetAtlas A (U i) (hU i)) B (F i)) →
    ∃! f : M → N, ManifoldContDiff r A B f ∧ Continuous f ∧
      ∀ i (x : M) (hx : x ∈ U i), f x = F i ⟨x, hx⟩

/-- Atlas transport for precisely the defined C^r diffeomorphism objects. -/
def contDiffDiffeomorph_transportAtlasType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (r : ℕ∞) (A : Set (ModelChart n a M)) (B : Set (ModelChart n a N)),
    IsMaximalContDiffAtlas r A → IsMaximalContDiffAtlas r B →
    ∀ h : ContDiffDiffeomorph r A B, transportAtlas h.toHomeomorph A = B

end Theorems

/-- The inverse assertion is about an actual inverse of the smooth bijection. -/
def cubic_smooth_bijectionType :=
  ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ 3) ∧
    Function.Bijective (fun x : ℝ => x ^ 3) ∧
    ∀ g : ℝ → ℝ, Function.LeftInverse g (fun x : ℝ => x ^ 3) →
      ¬ DifferentiableAt ℝ g 0

end Specs.SmoothManifolds.Foundations.SmoothMaps
