import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SmoothSurfaceDouble
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.TransverseDiskArrangement
import Mathlib.Topology.Order.ProjIcc

/-!
Independent graph-geometry interface for paper.tex 5053–5076, with the compact
one-manifold cutting argument at 5023–5030. All canonical graph and region
objects are rehomed from the unaccepted parent draft. Coordinates and chart
disks are the identical objects exported by TransverseDiskArrangement.

The input consists only of the original compact surface, its actual labelled
smooth double, and a transverse arrangement subordinate to original charts.
No graph, component finiteness, boundary cycles, or planar region is an input.
The graph-geometry target is stated independently of the parent extraction theorem.
-/
set_option autoImplicit false
noncomputable section
open Set Topology
open scoped ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.BoundaryData
open P202Specs.PlanarRegionTopology (Plane PlanarRegion)
universe u

namespace P202Specs.SurfaceRegionConstruction

/-- Local regularity at interior parameters uses the original atlas and a real
ambient germ. Clamping is irrelevant at each of these interior parameters. -/
def RegularOpenEdge {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) (c : C(unitInterval, M)) : Prop :=
  ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1),
    ∃ e ∈ S.smoothStructure.val,
      c ⟨t, ht.1.le, ht.2.le⟩ ∈ e.source ∧
      ContDiffAt ℝ ∞ (fun s => coordinates e (IccExtend zero_le_one c s)) t ∧
      deriv (fun s => coordinates e (IccExtend zero_le_one c s)) t ≠ 0

structure EmbeddedGraph {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) where
  vertexCount : ℕ
  edgeCount : ℕ
  vertex : Fin vertexCount → M
  vertex_injective : Function.Injective vertex
  edge : Fin edgeCount → C(unitInterval, M)
  initial : Fin edgeCount → Fin vertexCount
  terminal : Fin edgeCount → Fin vertexCount
  at_zero : ∀ i, edge i 0 = vertex (initial i)
  at_one : ∀ i, edge i 1 = vertex (terminal i)
  open_injective : ∀ i, Set.InjOn (edge i) {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
  avoids_vertices : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → edge i t ∉ range vertex
  disjoint_open_edges : Pairwise (fun i j => Disjoint
    (edge i '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1})
    (edge j '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1}))
  regular : ∀ i, RegularOpenEdge S (edge i)

def EmbeddedGraph.carrier {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (G : EmbeddedGraph S) : Set M :=
  range G.vertex ∪ ⋃ i, range (G.edge i)

/-- Actual component subset in an ambient space. -/
def componentSet {X : Type u} [TopologicalSpace X] (U : Set X)
    (a : ConnectedComponents U) : Set X :=
  Subtype.val '' {x : U | ConnectedComponents.mk x = a}

/-- A local star in an actual smooth chart. Its rays lie in the given model;
at boundary points the neighborhood is a half-disk. Centering takes place in
the ambient plane, so interior points of half-space manifolds are allowed. -/
structure GraphStar {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (G : EmbeddedGraph S) (p : M) where
  chart : ModelChart 2 kind M
  chart_mem : chart ∈ S.smoothStructure.val
  mem_source : p ∈ chart.source
  radius : ℝ
  radius_pos : 0 < radius
  ball_in_target : ∀ z : ModelSpace 2 kind,
    toPlane z.val ∈ Metric.ball (coordinates chart p) radius → z ∈ chart.target
  rayCount : ℕ
  direction : Fin rayCount → Plane
  direction_injective : Function.Injective direction
  direction_unit : ∀ i, ‖direction i‖ = 1
  rays_in_model : ∀ i t, 0 < t → t < radius →
    toPlane.symm (coordinates chart p + t • direction i) ∈ modelSet 2 kind
  graph_eq : ∀ x ∈ chart.source,
    coordinates chart x ∈ Metric.ball (coordinates chart p) radius →
    (x ∈ G.carrier ↔ x = p ∨ ∃ i, ∃ t : ℝ,
      0 < t ∧ t < radius ∧ coordinates chart x = coordinates chart p + t • direction i)

def GraphStar.neighborhood {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) : Set M :=
  s.chart.source ∩ coordinates s.chart ⁻¹' Metric.ball (coordinates s.chart p) s.radius

/-- Geometric decomposition without any connectedness or orientation premise. -/
structure RegionDecomposition {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) where
  graph : EmbeddedGraph S
  contains_boundary : intrinsicBoundary S ⊆ graph.carrier
  regionCount : ℕ
  component : Fin regionCount ≃ ConnectedComponents (graph.carrierᶜ : Set M)
  region : Fin regionCount → PlanarRegion
  chart : Fin regionCount → ModelChart 2 kind M
  chart_mem : ∀ j, chart j ∈ S.smoothStructure.val
  closure_in_chart : ∀ j,
    closure (componentSet graph.carrierᶜ (component j)) ⊆ (chart j).source
  domain_coordinates : ∀ j,
    coordinates (chart j) '' componentSet graph.carrierᶜ (component j) = (region j).domain
  closure_coordinates : ∀ j,
    coordinates (chart j) '' closure (componentSet graph.carrierᶜ (component j)) =
      (region j).carrier
  open_components : ∀ j, IsOpen (componentSet graph.carrierᶜ (component j))
  compact_closures : ∀ j, IsCompact (closure (componentSet graph.carrierᶜ (component j)))
  connected_closures : ∀ j, IsConnected (closure (componentSet graph.carrierᶜ (component j)))
  frontiers_on_graph : ∀ j,
    frontier (componentSet graph.carrierᶜ (component j)) =
      closure (componentSet graph.carrierᶜ (component j)) ∩ graph.carrier
  disjoint_interiors : Pairwise (fun i j => Disjoint
    (interior (closure (componentSet graph.carrierᶜ (component i))))
    (interior (closure (componentSet graph.carrierᶜ (component j)))))
  /-- Arbitrarily small graph stars. Every incident region occupies one whole
  local sector, every local sector occurs, and two sectors cannot be parts of
  the same global region. This also applies at inserted smooth-edge vertices. -/
  sectors : ∀ p ∈ graph.carrier, ∀ O : Set M, IsOpen O → p ∈ O →
    ∃ s : GraphStar graph p, s.neighborhood ⊆ O ∧
      (∀ j, p ∈ closure (componentSet graph.carrierᶜ (component j)) →
        ∃ a : ConnectedComponents (s.neighborhood \ graph.carrier : Set M),
          componentSet graph.carrierᶜ (component j) ∩ s.neighborhood =
            componentSet (s.neighborhood \ graph.carrier) a) ∧
      (∀ a : ConnectedComponents (s.neighborhood \ graph.carrier : Set M),
        ∃! j, componentSet graph.carrierᶜ (component j) ∩ s.neighborhood =
          componentSet (s.neighborhood \ graph.carrier) a)
  empty_case : IsEmpty M → graph.vertexCount = 0 ∧ graph.edgeCount = 0 ∧ regionCount = 0

/-- Smooth one-sided extensions in the ambient coordinate plane at both
endpoints. The extensions need not stay in the half-space model: at a circle
crossing the seam that would incorrectly forbid a nonzero normal tangent. -/
def RegularEdgeEndpoints {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) (c : C(unitInterval, M)) : Prop :=
  ∀ t : unitInterval, t = 0 ∨ t = 1 →
    ∀ e ∈ S.smoothStructure.val, c t ∈ e.source →
      ∃ (δ : ℝ) (F : ℝ → Plane), 0 < δ ∧
        ContDiffOn ℝ ∞ F (Ioo ((t : ℝ) - δ) ((t : ℝ) + δ)) ∧
        deriv F (t : ℝ) ≠ 0 ∧
        ∀ q : unitInterval, |(q : ℝ) - (t : ℝ)| < δ →
          c q ∈ e.source ∧ F (q : ℝ) = coordinates e (c q)

/-- The actual circle/seam carrier in the double. -/
def arrangementCarrier {X : Type u} [TopologicalSpace X]
    {W : SmoothManifold 2 .euclidean X} {K : Set X}
    {A : Set (ModelChart 2 .euclidean X)} {B : CompactSmoothSeam W}
    (T : TransverseDiskArrangement W K A B) : Set X :=
  B.carrier ∪ ⋃ i, (T.disk i).circleAtRadius (T.radius i)

/-- A supplied double chart family refines original charts on the designated
copy. This is chart subordination, with no component-containment premise. -/
def CopySubordinate {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) (_D : SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool) (A : Set (ModelChart 2 .euclidean (SmoothSurfaceDouble.SurfaceDouble S))) : Prop :=
  ∀ d ∈ A, ∃ e ∈ S.smoothStructure.val,
    SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' d.source ⊆ e.source

/-- Output bridges tying every interval edge and every actual global region
to the supplied arrangement. In particular an untouched compact curve is
covered by finitely many genuine interval edges, not just component labels. -/
structure ArrangementExtractionData {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold 2 kind M)
    (D : SmoothSurfaceDouble.SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (T : TransverseDiskArrangement D.manifold
      (range (SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (R : RegionDecomposition S) : Prop where
  carrier_eq : R.graph.carrier =
    SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T
  endpoint_germs : ∀ i, RegularEdgeEndpoints S (R.graph.edge i)
  edge_curve : ∀ i, ∃ k : Option (Fin T.count), ∀ t : unitInterval,
    SmoothSurfaceDouble.copy (intrinsicBoundary S) s (R.graph.edge i t) ∈
      arrangementCurve B.carrier T.disk T.radius k
  region_disk : ∀ j, ∃ i : Fin T.count,
    componentSet R.graph.carrierᶜ (R.component j) ⊆
      SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        (T.disk i).openAtRadius (T.radius i) ∧
    closure (componentSet R.graph.carrierᶜ (R.component j)) ⊆
      SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        (T.disk i).closedAtRadius (T.radius i)
  /-- Actual local components are distinguished by disk memberships. The seam
  restricts to one side on the designated copy, so it needs no extra bit. -/
  separated_stars : ∀ p ∈ R.graph.carrier, ∀ O : Set M, IsOpen O → p ∈ O →
    ∃ g : GraphStar R.graph p, g.neighborhood ⊆ O ∧
      ∀ a b : ConnectedComponents (g.neighborhood \ R.graph.carrier : Set M), a ≠ b →
        ∃ i : Fin T.count,
          ∀ x ∈ componentSet (g.neighborhood \ R.graph.carrier) a,
          ∀ y ∈ componentSet (g.neighborhood \ R.graph.carrier) b,
            ¬ (SmoothSurfaceDouble.copy (intrinsicBoundary S) s x ∈
                (T.disk i).openAtRadius (T.radius i) ↔
              SmoothSurfaceDouble.copy (intrinsicBoundary S) s y ∈
                (T.disk i).openAtRadius (T.radius i))


/-- The graph and local geometry stage on the exact original surface. There is
no regional curve family or PlanarRegion in this output. All components are
components of the actual complement, with its subspace topology. -/
structure ArrangementGraphGeometryData {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold 2 kind M)
    (D : SmoothSurfaceDouble.SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (T : TransverseDiskArrangement D.manifold
      (range (SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B) where
  graph : EmbeddedGraph S
  carrier_eq : graph.carrier =
    SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T
  contains_boundary : intrinsicBoundary S ⊆ graph.carrier
  endpoint_germs : ∀ i, RegularEdgeEndpoints S (graph.edge i)
  edge_curve : ∀ i, ∃ k : Option (Fin T.count), ∀ t : unitInterval,
    SmoothSurfaceDouble.copy (intrinsicBoundary S) s (graph.edge i t) ∈
      arrangementCurve B.carrier T.disk T.radius k
  finite_components : Finite (ConnectedComponents (graph.carrierᶜ : Set M))
  component_disk_chart : ∀ a : ConnectedComponents (graph.carrierᶜ : Set M),
    ∃ (i : Fin T.count) (e : ModelChart 2 kind M), e ∈ S.smoothStructure.val ∧
      componentSet graph.carrierᶜ a ⊆ SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        (T.disk i).openAtRadius (T.radius i) ∧
      closure (componentSet graph.carrierᶜ a) ⊆
        SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
          (T.disk i).closedAtRadius (T.radius i) ∧
      closure (componentSet graph.carrierᶜ a) ⊆ e.source
  open_components : ∀ a, IsOpen (componentSet graph.carrierᶜ a)
  connected_components : ∀ a, IsConnected (componentSet graph.carrierᶜ a)
  compact_closures : ∀ a, IsCompact (closure (componentSet graph.carrierᶜ a))
  connected_closures : ∀ a, IsConnected (closure (componentSet graph.carrierᶜ a))
  frontiers_on_graph : ∀ a, frontier (componentSet graph.carrierᶜ a) =
    closure (componentSet graph.carrierᶜ a) ∩ graph.carrier
  nonempty_frontiers : ∀ a, (frontier (componentSet graph.carrierᶜ a)).Nonempty
  disjoint_interiors : Pairwise (fun a b => Disjoint
    (interior (closure (componentSet graph.carrierᶜ a)))
    (interior (closure (componentSet graph.carrierᶜ b))))
  /-- The same arbitrarily small star supplies disk separation and both exact
  occupancy statements, including at seam and inserted smooth-edge vertices. -/
  stars : ∀ p ∈ graph.carrier, ∀ O : Set M, IsOpen O → p ∈ O →
        ∃ g : GraphStar graph p, g.neighborhood ⊆ O ∧
          Finite (ConnectedComponents (g.neighborhood \ graph.carrier : Set M)) ∧
          (∀ a b : ConnectedComponents (g.neighborhood \ graph.carrier : Set M), a ≠ b →
            ∃ i : Fin T.count,
              ∀ x ∈ componentSet (g.neighborhood \ graph.carrier) a,
              ∀ y ∈ componentSet (g.neighborhood \ graph.carrier) b,
                ¬ (SmoothSurfaceDouble.copy (intrinsicBoundary S) s x ∈ (T.disk i).openAtRadius (T.radius i) ↔
                   SmoothSurfaceDouble.copy (intrinsicBoundary S) s y ∈ (T.disk i).openAtRadius (T.radius i))) ∧
          (∀ c : ConnectedComponents (graph.carrierᶜ : Set M), p ∈ closure (componentSet graph.carrierᶜ c) →
            ∃ a : ConnectedComponents (g.neighborhood \ graph.carrier : Set M),
              componentSet graph.carrierᶜ c ∩ g.neighborhood =
                componentSet (g.neighborhood \ graph.carrier) a) ∧
          (∀ a : ConnectedComponents (g.neighborhood \ graph.carrier : Set M),
            ∃! c : ConnectedComponents (graph.carrierᶜ : Set M),
              componentSet graph.carrierᶜ c ∩ g.neighborhood =
                componentSet (g.neighborhood \ graph.carrier) a)
  empty_case : IsEmpty M → graph.vertexCount = 0 ∧ graph.edgeCount = 0 ∧
    IsEmpty (ConnectedComponents (graph.carrierᶜ : Set M))

namespace Expected

/-- Explicit-double/arrangement graph construction. The only input
certificates are the upstream smooth double, its actual seam, the transverse
arrangement and chart subordination; every graph-stage property is output. -/
def arrangementGraphGeometry : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold 2 kind M) (D : SmoothSurfaceDouble.SmoothDouble S) (s : Bool)
    (A : Set (ModelChart 2 .euclidean (SmoothSurfaceDouble.SurfaceDouble S))),
    A ⊆ D.manifold.smoothStructure.val → CopySubordinate S D s A →
    ∀ (B : CompactSmoothSeam D.manifold),
      B.carrier = SmoothSurfaceDouble.seam (intrinsicBoundary S) →
      ∀ T : TransverseDiskArrangement D.manifold
        (range (SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B,
        Nonempty (ArrangementGraphGeometryData S D s T)

end Expected
end P202Specs.SurfaceRegionConstruction
