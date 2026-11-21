import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionFoundation
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.TransversePreimage

/-!
Independent interface for paper.tex 5032–5052. The input is a compact subset
of a boundaryless smooth surface and a supplied chart family covering that
subset, together with an optional actual compact embedded smooth seam.
No double, graph, orientation, connectedness or global compactness is input.
The empty seam is represented by an empty carrier with its empty smooth atlas.
The earlier draft's canonical names `toPlane`, `coordinates` and `ChartDisk`
are retained verbatim. Every subtype and product has its ordinary topology.
-/
set_option autoImplicit false
noncomputable section
open Set Topology
open scoped ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.MapClassData
open P202Specs.PlanarRegionTopology (Plane)
universe u v

namespace P202Specs.SurfaceRegionConstruction

def toPlane : Euclidean 2 ≃L[ℝ] Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm

def coordinates {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (e : ModelChart 2 kind M) (x : M) : Plane := toPlane (e x).val

/-- A closed chart disk with two radii, retaining room to perturb its circle.
This auxiliary structure is not a hypothesis of the decomposition target. -/
structure ChartDisk (X : Type u) [TopologicalSpace X]
    (A : Set (OpenPartialHomeomorph X Plane)) where
  chart : OpenPartialHomeomorph X Plane
  chart_mem : chart ∈ A
  center : Plane
  innerRadius : ℝ
  outerRadius : ℝ
  inner_pos : 0 < innerRadius
  inner_lt_outer : innerRadius < outerRadius
  closedBall_subset : Metric.closedBall center outerRadius ⊆ chart.target

def ChartDisk.inner {X : Type u} [TopologicalSpace X]
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A) : Set X :=
  d.chart.source ∩ d.chart ⁻¹' Metric.ball d.center d.innerRadius

def ChartDisk.outer {X : Type u} [TopologicalSpace X]
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A) : Set X :=
  d.chart.symm '' Metric.closedBall d.center d.outerRadius


namespace ChartDisk
variable {X : Type u} [TopologicalSpace X]
variable {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A)

/-- A variable-radius disk in the fixed original chart. The perturbation
changes the radius, rather than replacing the chart by an unrelated disk. -/
def openAtRadius (r : ℝ) : Set X :=
  d.chart.source ∩ d.chart ⁻¹' Metric.ball d.center r

def closedAtRadius (r : ℝ) : Set X :=
  d.chart.symm '' Metric.closedBall d.center r

def circleAtRadius (r : ℝ) : Set X :=
  d.chart.symm '' Metric.sphere d.center r

end ChartDisk

variable {X : Type u} [TopologicalSpace X]

/-- P104's Euclidean model, with its actual subtype topology, is the plane. -/
def euclideanModelPlane : ModelSpace 2 .euclidean ≃ₜ Plane :=
  (Homeomorph.Set.univ (Euclidean 2)).trans toPlane.toHomeomorph

def euclideanChartToPlane (e : ModelChart 2 .euclidean X) :
    OpenPartialHomeomorph X Plane := e.transHomeomorph euclideanModelPlane

def planeAtlas (S : SmoothManifold 2 .euclidean X) :
    Set (OpenPartialHomeomorph X Plane) :=
  {e | ∃ c ∈ S.smoothStructure.val, e = euclideanChartToPlane c}


/-- The prescribed family is retained, including its labels via membership. -/
def planeChartFamily (A : Set (ModelChart 2 .euclidean X)) :
    Set (OpenPartialHomeomorph X Plane) := euclideanChartToPlane '' A

/-- The seam's smooth source is its actual ambient subspace. This permits the
empty seam and does not presume any circle-component decomposition. -/
structure CompactSmoothSeam (S : SmoothManifold 2 .euclidean X) where
  carrier : Set X
  compact : IsCompact carrier
  manifold : SmoothManifold 1 .euclidean carrier
  embedding : IsSmoothEmbedding manifold S Subtype.val

/-- Smooth structures on the actual circle subsets, not on independent labels.
A homeomorphism to the ordinary unit circle records their circle topology. -/
structure SmoothChartCircle (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A) (r : ℝ) where
  manifold : SmoothManifold 1 .euclidean (d.circleAtRadius r)
  embedding : IsSmoothEmbedding manifold S Subtype.val
  circleHomeomorph : (d.circleAtRadius r) ≃ₜ Metric.sphere (0 : Plane) 1

/-- Ordinary axes; `a` is the normal coordinate, so the tangent coordinate
is the other coordinate. -/
def axisTangent (a : Fin 2) : Plane := toPlane (fun i => if i = a then 0 else 1)

/-- All curves are indexed by `Option`: `none` is the prescribed seam. -/
def arrangementCurve {n : ℕ} {A : Set (OpenPartialHomeomorph X Plane)}
    (B : Set X) (d : Fin n → ChartDisk X A) (r : Fin n → ℝ) :
    Option (Fin n) → Set X
  | none => B
  | some i => (d i).circleAtRadius (r i)

/-- An exact sign-preserving smooth local normal form in an original smooth
atlas. Distinct incident curves have distinct normal axes. All nonincident
curves are absent. The whole coordinate ball, not only a germ, is retained.
The final field retains two-sided smooth regular extensions at potential edge
endpoints, in every original chart, including the crossing itself. -/
structure ArrangementNormalForm (S : SmoothManifold 2 .euclidean X)
    {n : ℕ} {A : Set (OpenPartialHomeomorph X Plane)}
    (B : Set X) (d : Fin n → ChartDisk X A) (r : Fin n → ℝ)
    (p : X) (O : Set X) where
  chart : ModelChart 2 .euclidean X
  chart_mem : chart ∈ S.smoothStructure.val
  mem_source : p ∈ chart.source
  centered : coordinates chart p = 0
  radius : ℝ
  radius_pos : 0 < radius
  ball_in_target : ∀ z : ModelSpace 2 .euclidean,
    toPlane z.val ∈ Metric.ball (0 : Plane) radius → z ∈ chart.target
  neighborhood_subset :
    chart.source ∩ coordinates chart ⁻¹' Metric.ball (0 : Plane) radius ⊆ O
  axis : Option (Fin n) → Option (Fin 2)
  axis_injective : ∀ i j a, axis i = some a → axis j = some a → i = j
  active_iff : ∀ i, axis i ≠ none ↔ p ∈ arrangementCurve B d r i
  curve_eq : ∀ i x, x ∈ chart.source →
    coordinates chart x ∈ Metric.ball (0 : Plane) radius →
    (x ∈ arrangementCurve B d r i ↔
      ∃ a, axis i = some a ∧ coordinates chart x a = 0)
  disk_sign : ∀ i x, x ∈ chart.source →
    coordinates chart x ∈ Metric.ball (0 : Plane) radius →
    (x ∈ (d i).openAtRadius (r i) ↔
      match axis (some i) with
      | some a => coordinates chart x a < 0
      | none => p ∈ (d i).openAtRadius (r i))
  endpoint_germs : ∀ i a, axis i = some a →
    ∃ (δ : ℝ) (g : ℝ → X), 0 < δ ∧ g 0 = p ∧
      (∀ t ∈ Ioo (-δ) δ, g t ∈ chart.source ∧
        g t ∈ arrangementCurve B d r i ∧
        coordinates chart (g t) = t • axisTangent a) ∧
      (∀ e ∈ S.smoothStructure.val, p ∈ e.source →
        ContDiffAt ℝ ∞ (fun t => coordinates e (g t)) 0 ∧
        deriv (fun t => coordinates e (g t)) 0 ≠ 0)

/-- Complete output of the arrangement construction. Smooth radius maps and
Sard selection are proof obligations, rather than premises of this structure.
The transversality predicate uses actual inclusion differentials in the full
ambient tangent space. No graph or regional conclusion is included as input. -/
structure TransverseDiskArrangement (S : SmoothManifold 2 .euclidean X)
    (K : Set X) (A : Set (ModelChart 2 .euclidean X)) (B : CompactSmoothSeam S) where
  count : ℕ
  disk : Fin count → ChartDisk X (planeChartFamily A)
  radius : Fin count → ℝ
  radius_bounds : ∀ i, radius i ∈ Ioo (disk i).innerRadius (disk i).outerRadius
  inner_cover : K ⊆ ⋃ i, (disk i).inner
  final_cover : K ⊆ ⋃ i, (disk i).openAtRadius (radius i)
  circle : ∀ i, SmoothChartCircle S (disk i) (radius i)
  transverse_pairs : ∀ i j, i ≠ j →
    SmoothManifolds.TransversePreimageData.IsTransverse
      (circle i).manifold S (circle j).manifold Subtype.val
  transverse_seam : ∀ i,
    SmoothManifolds.TransversePreimageData.IsTransverse
      (circle i).manifold S B.manifold Subtype.val
  finite_pairs : ∀ i j, i ≠ j →
    ((disk i).circleAtRadius (radius i) ∩ (disk j).circleAtRadius (radius j)).Finite
  finite_seam : ∀ i, ((disk i).circleAtRadius (radius i) ∩ B.carrier).Finite
  no_triple : ∀ i j k : Option (Fin count), i ≠ j → i ≠ k → j ≠ k →
    arrangementCurve B.carrier disk radius i ∩ arrangementCurve B.carrier disk radius j ∩
      arrangementCurve B.carrier disk radius k = ∅
  normal_forms : ∀ p, ∀ O : Set X, IsOpen O → p ∈ O →
    Nonempty (ArrangementNormalForm S B.carrier disk radius p O)

namespace Expected

/-- Perturbation-room disks subordinate to a family covering only K. -/
def suppliedDiskCover : Prop := ∀ {X : Type u} [TopologicalSpace X]
    (K : Set X), IsCompact K → ∀ A : Set (ModelChart 2 .euclidean X),
    (∀ p ∈ K, ∃ e ∈ A, p ∈ e.source) →
    ∃ (n : ℕ) (d : Fin n → ChartDisk X (planeChartFamily A)), K ⊆ ⋃ i, (d i).inner

/-- Smooth regular circles are constructed from the actual chart and radius. -/
def chartCircleConstruction : Prop := ∀ {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A)
    (e : ModelChart 2 .euclidean X), e ∈ S.smoothStructure.val →
    d.chart = euclideanChartToPlane e → ∀ {r : ℝ}, 0 < r → r ≤ d.outerRadius →
    Nonempty (SmoothChartCircle S d r)

/-- Original generic input; the prescribed charts only have to cover K. -/
def transverseDiskArrangement : Prop := ∀ {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold 2 .euclidean X) (K : Set X), IsCompact K →
    ∀ (A : Set (ModelChart 2 .euclidean X)), A ⊆ S.smoothStructure.val →
      (∀ p ∈ K, ∃ e ∈ A, p ∈ e.source) →
      ∀ B : CompactSmoothSeam S, Nonempty (TransverseDiskArrangement S K A B)

end Expected
end P202Specs.SurfaceRegionConstruction
