import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnetLocalization
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Canonical radial coordinate sets used for the local sector classification.
All original graph and manifold definitions are imported unchanged. -/
set_option autoImplicit false
noncomputable section
open Set
open P202Specs.PlanarRegionTopology
namespace P202.RadialGraphSectors
/-- Representative in (0,2*pi], with coincident rays describing a full turn. -/
def positiveAngle (theta : Real.Angle) : ℝ :=
  if 0 < theta.toReal then theta.toReal else theta.toReal + 2 * Real.pi
namespace AngularSector
/-- Open angular sector in the slit complex plane. -/
def sector (r a b : ℝ) : Set ℂ :=
  {z | z ≠ 0 ∧ ‖z‖ < r ∧ Complex.arg z ∈ Ioo a b}
def polar (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)
def rayComplement {ι : Type*} (r : ℝ) (d : ι → ℂ) : Set ℂ :=
  {z | z ≠ 0 ∧ ‖z‖ < r ∧ ∀ i, ¬SameRay ℝ z (d i)}
def upperRayComplement {ι : Type*} (r : ℝ) (d : ι → ℂ) : Set ℂ :=
  rayComplement r d ∩ {z | 0 < Complex.arg z}
end AngularSector
namespace GraphStarImage
def planeRayComplement (r : ℝ) {n : ℕ} (d : Fin n → Plane) : Set Plane :=
  {z | z ≠ 0 ∧ ‖z‖ < r ∧ ∀ i, ¬SameRay ℝ z (d i)}
end GraphStarImage
namespace PlaneComplexBridge
def planeComplex : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
end PlaneComplexBridge
end P202.RadialGraphSectors

open scoped BigOperators
open Complex
open SmoothManifolds (ModelKind)
open SmoothManifolds.BoundaryData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.SurfaceBoundaryData P202Specs.SurfaceRegionConstruction
universe u
namespace P202.RadialGraphSectors
/-- Actual inverse differential of a star's chart, at its original center.
This uses the original tangent bundle, including at smooth boundary points. -/
def starTangentEquiv {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M} (s : GraphStar G p) :
    Plane ≃ₗ[ℝ] TangentSpace S p :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv.trans
    ((tangentStructure S).fiberCoordinates.equiv s.chart s.chart_mem p s.mem_source).symm

/-- Genuine positive metric angle of two star directions, measured in the
original tangent fiber with either chosen tangent orientation. -/
def starMetricAngle {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2)) (v w : Plane) : ℝ := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  exact positiveAngle (o.oangle (starTangentEquiv s v) (starTangentEquiv s w))

/-- An actual subset of the original star complement, tested using the
inverse chart differential and genuine metric angles. -/
def starMetricSector {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2)) (v w : Plane) : Set M :=
  {x | x ∈ s.neighborhood \ G.carrier ∧
    starMetricAngle g s o v (coordinates s.chart x - coordinates s.chart p) <
      starMetricAngle g s o v w}
end P202.RadialGraphSectors

namespace P202Specs.RadialGraphSectors.Expected
open P202.RadialGraphSectors
/-- Complete full-disk obligation: the ordering and component correspondence
are outputs, and the widths use the genuine inverse chart differential. -/
def fullStarMetricSectors : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2)),
    (∀ z : Plane, ‖z‖ < s.radius →
      toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind) →
    0 < s.rayCount →
    ∃ e : Equiv.Perm (Fin s.rayCount),
      ∃ E : ConnectedComponents (s.neighborhood \ G.carrier : Set M) ≃ Fin s.rayCount,
        (∀ a, componentSet (s.neighborhood \ G.carrier) a =
          starMetricSector g s o (s.direction (e (E a)))
            (s.direction (e (finRotate s.rayCount (E a))))) ∧
        (∑ i, starMetricAngle g s o (s.direction (e i))
          (s.direction (e (finRotate s.rayCount i)))) = 2 * Real.pi

/-- Complete genuine-boundary obligation. The finite family is reindexed
only by the proved equality of its actual ray count with n+2. -/
def halfStarMetricSectors : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
    (g : RiemannianMetric S) {G : EmbeddedGraph S} {p : M} (s : GraphStar G p)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2)),
    p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S →
    SmoothManifolds.BoundaryData.intrinsicBoundary S ⊆ G.carrier →
    ∃ n : ℕ, ∃ hn : s.rayCount = n + 2,
      let d := fun i : Fin (n + 2) => s.direction (Fin.cast hn.symm i)
      ∃ e : Equiv.Perm (Fin (n + 2)),
        ∃ E : ConnectedComponents (s.neighborhood \ G.carrier : Set M) ≃ Fin (n + 1),
          (∀ a, componentSet (s.neighborhood \ G.carrier) a =
            starMetricSector g s o (d (e (E a).castSucc)) (d (e (E a).succ))) ∧
          (∑ i : Fin (n + 1), starMetricAngle g s o
            (d (e i.castSucc)) (d (e i.succ))) = Real.pi
end P202Specs.RadialGraphSectors.Expected

namespace P202Specs.RadialGraphSectors.Expected
open P202.RadialGraphSectors

def fullStarComponents : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p)
    (hfull : ∀ z : Plane, ‖z‖ < s.radius →
      toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind)
    (hn : 0 < s.rayCount),
    ∃ c : ℂ, ‖c‖ = 1 ∧ c * PlaneComplexBridge.planeComplex (s.direction ⟨0, hn⟩) = -1 ∧
      ∃ e : Equiv.Perm (Fin s.rayCount),
        let cuts : Fin (s.rayCount + 1) → ℝ := Fin.cons (-Real.pi)
          (fun i => arg (c * PlaneComplexBridge.planeComplex (s.direction (e i))))
        StrictMono cuts ∧ cuts (Fin.last s.rayCount) = Real.pi ∧
        ∃ E : ConnectedComponents (s.neighborhood \ G.carrier : Set M) ≃ Fin s.rayCount,
          ∀ a, (fun x => c * PlaneComplexBridge.planeComplex
            (coordinates s.chart x - coordinates s.chart p)) ''
              componentSet (s.neighborhood \ G.carrier) a =
                AngularSector.sector s.radius (cuts (E a).castSucc) (cuts (E a).succ)

def boundaryStarComponents : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hp : p ∈ intrinsicBoundary S)
    (hB : intrinsicBoundary S ⊆ G.carrier),
    ∃ n : ℕ, ∃ hn : s.rayCount = n + 2,
      let d := fun i : Fin (n + 2) =>
        PlaneComplexBridge.planeComplex (s.direction (Fin.cast hn.symm i))
      ∃ e : Equiv.Perm (Fin (n + 2)),
        let cuts := fun i => arg (d (e i))
        StrictMono cuts ∧ cuts 0 = 0 ∧ cuts (Fin.last (n + 1)) = Real.pi ∧
        ∃ E : ConnectedComponents (s.neighborhood \ G.carrier : Set M) ≃ Fin (n + 1),
          ∀ a, (fun x => PlaneComplexBridge.planeComplex
            (coordinates s.chart x - coordinates s.chart p)) ''
              componentSet (s.neighborhood \ G.carrier) a =
                AngularSector.sector s.radius (cuts (E a).castSucc) (cuts (E a).succ)

def fullStarZeroComponents : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p)
    (hfull : ∀ z : Plane, ‖z‖ < s.radius →
      toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind)
    (hz : s.rayCount = 0),
    Nonempty (ConnectedComponents (s.neighborhood \ G.carrier : Set M) ≃ Fin 1)

def fullStar_component_card : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p)
    (hfull : ∀ z : Plane, ‖z‖ < s.radius →
      toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind),
    Nat.card (ConnectedComponents (s.neighborhood \ G.carrier : Set M)) =
      if s.rayCount = 0 then 1 else s.rayCount

def boundaryStar_component_card : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hp : p ∈ intrinsicBoundary S)
    (hB : intrinsicBoundary S ⊆ G.carrier),
    Nat.card (ConnectedComponents (s.neighborhood \ G.carrier : Set M)) = s.rayCount - 1

def starMetricAngle_cyclic_sum : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2)) (hn : 0 < s.rayCount),
    ∃ e : Equiv.Perm (Fin s.rayCount),
      (∑ i, starMetricAngle g s o (s.direction (e i))
        (s.direction (e (finRotate s.rayCount i)))) = 2 * Real.pi

def exists_interior_halfSpace_star : Prop :=
  ∀
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p)
    (hp : p ∉ intrinsicBoundary S),
    ∃ t : GraphStar G p,
      t.chart = s.chart ∧ t.rayCount = s.rayCount ∧ HEq t.direction s.direction ∧
      t.radius ≤ s.radius ∧ t.neighborhood ⊆ s.neighborhood ∧
      ∀ z : Plane, ‖z‖ < t.radius →
        toPlane.symm (coordinates t.chart p + z) ∈ modelSet 2 .halfSpace

def boundaryRays : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p),
    p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S →
    SmoothManifolds.BoundaryData.intrinsicBoundary S ⊆ G.carrier →
    ∃ i₀ i₁ : Fin s.rayCount, i₀ ≠ i₁ ∧
      s.direction i₀ = P202Specs.PlaneTurning.reference ∧
      s.direction i₁ = -P202Specs.PlaneTurning.reference ∧
      ∀ i, 0 ≤ s.direction i 1 ∧
        (s.direction i 1 = 0 ↔ i = i₀ ∨ i = i₁)
end P202Specs.RadialGraphSectors.Expected
