import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.ThomClass
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Ordered simultaneous normal coordinates for paper.tex 2576–2580.
The family consists of actual P104 embeddings and their quotient normal bundles.
All coordinate and slice data below are outputs, never hypotheses. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.MapData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
universe u
namespace P202Specs.TransverseNormalCoordinates
attribute [local instance] normalTopology

/-- The geometric fields of one embedded submanifold, without orientation data. -/
structure EmbeddedData {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) where
  dimension : ℕ
  source : Type u
  topology : TopologicalSpace source
  compact : @CompactSpace source topology
  manifold : @SmoothManifold dimension .euclidean source topology
  inclusion : source → M
  embedding : @IsSmoothEmbedding dimension n .euclidean .euclidean source M
    topology _ manifold S inclusion
  normal : @NormalBundle dimension n .euclidean .euclidean source M topology _ manifold S inclusion
attribute [instance] EmbeddedData.topology EmbeddedData.compact

variable {n k : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

abbrev Blocks (F : Fin k → EmbeddedData S) := ∀ j, Euclidean (n - (F j).dimension)

def totalCodimension (F : Fin k → EmbeddedData S) : ℕ :=
  ∑ j, (n - (F j).dimension)

/-- Transport to the actual source point, followed by the actual quotient map. -/
def normalProjection (A : EmbeddedData S) (p : A.source) (x : M)
    (h : A.inclusion p = x) : TangentSpace S x →ₗ[ℝ] NormalFiber A.normal p := by
  subst x
  exact { toFun := Submodule.Quotient.mk
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }

def combinedProjection (F : Fin k → EmbeddedData S) (x : M)
    (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x) :
    TangentSpace S x →ₗ[ℝ] (∀ j, NormalFiber (F j).normal (p j)) :=
  LinearMap.pi (fun j => normalProjection (F j) (p j) x (h j))

/-- A derivative represented in an original chart, with a general vector target. -/
def HasChartDerivative {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ModelChart n .euclidean M) (f : M → V) (x : M)
    (L : Euclidean n →L[ℝ] V) : Prop :=
  ∃ g : Euclidean n → V, HasFDerivAt g L (c x).val ∧
    (fun y => g (c y).val) =ᶠ[nhds x] f

/-- Forget the vacuous Euclidean model subtype in an original P104 chart. -/
def euclideanChart (c : ModelChart n .euclidean M) :
    OpenPartialHomeomorph M (Euclidean n) :=
  c.trans (Homeomorph.Set.univ (Euclidean n)).toOpenPartialHomeomorph

/-- A smooth submersion chart preserving all ordered normal blocks, together
with an actual smooth local slice. Smoothness of the inverse and slice is
expressed in one original ambient chart; their images lie in that chart.
This is the usual coordinate definition of smoothness, on open domains.
`normal_derivative` retains the original quotient normal vector in each block. -/
structure SimultaneousCoordinates (F : Fin k → EmbeddedData S) (x : M)
    (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x) where
  codimension_le : totalCodimension F ≤ n
  chart : ModelChart n .euclidean M
  chart_mem : chart ∈ S.smoothStructure.val
  point_mem : x ∈ chart.source
  tangentCoordinates : TangentSpace S x ≃ₗ[ℝ] Euclidean n
  tangent_isCoordinates : IsChartCoordinates S x chart tangentCoordinates
  chartPoint : ∀ j, (F j).source
  base_mem : ∀ j, p j ∈ (normalBundle (F j).normal).baseSet (chartPoint j)
  derivative : Euclidean n →L[ℝ] Blocks F
  normal_derivative : ∀ (v : TangentSpace S x) j,
    derivative (tangentCoordinates v) j =
      P202Specs.ThomClass.fiberLinearCoordinates (F j).normal (chartPoint j) (p j)
        (base_mem j) (normalProjection (F j) (p j) x (h j) v)
  coordinates : OpenPartialHomeomorph M (Blocks F × derivative.ker)
  center : coordinates x = (0, 0)
  mem_source : x ∈ coordinates.source
  source_in_chart : coordinates.source ⊆ chart.source
  smooth : ContDiffOn ℝ (⊤ : ℕ∞)
    (coordinates ∘ (euclideanChart chart).symm)
    ((euclideanChart chart) '' coordinates.source)
  inverse_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
    (fun z => (chart (coordinates.symm z)).val) coordinates.target
  has_derivative : HasChartDerivative chart
    (fun y => (coordinates y).1) x derivative
  zero_equations : ∀ y ∈ coordinates.source, ∀ j,
    y ∈ Set.range (F j).inclusion ↔ (coordinates y).1 j = 0
  sliceDomain : Set (Blocks F)
  sliceDomain_open : IsOpen sliceDomain
  sliceDomain_zero : 0 ∈ sliceDomain
  slice : Blocks F → M
  slice_center : slice 0 = x
  slice_mem : ∀ z ∈ sliceDomain, slice z ∈ coordinates.source
  slice_coordinates : ∀ z ∈ sliceDomain, coordinates (slice z) = (z, 0)
  slice_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (chart (slice z)).val) sliceDomain
  slice_continuous : ContinuousOn slice sliceDomain
  slice_injective : Set.InjOn slice sliceDomain
  slice_normal_derivative : ∀ (v : Blocks F) j,
    normalProjection (F j) (p j) x (h j)
      (tangentCoordinates.symm (fderiv ℝ (fun z => (chart (slice z)).val) 0 v)) =
        (P202Specs.ThomClass.fiberLinearCoordinates (F j).normal (chartPoint j) (p j)
          (base_mem j)).symm (v j)
  slice_zero_equations : ∀ z ∈ sliceDomain, ∀ j,
    slice z ∈ Set.range (F j).inclusion ↔ z j = 0

/-- Full geometric obligation, including the empty family and all zero ranks. -/
def simultaneousCoordinates_type : Prop :=
  ∀ (n k : ℕ) (M : Type u) [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (F : Fin k → EmbeddedData S)
    (x : M) (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x),
    Function.Surjective (combinedProjection F x p h) →
      Nonempty (SimultaneousCoordinates F x p h)

/-- The dimension consequence uses only the original transversality map. -/
def codimensionBound_type : Prop :=
  ∀ (n k : ℕ) (M : Type u) [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (F : Fin k → EmbeddedData S)
    (x : M) (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x),
    Function.Surjective (combinedProjection F x p h) → totalCodimension F ≤ n

end P202Specs.TransverseNormalCoordinates
