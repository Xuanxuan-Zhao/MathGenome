import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ArrangementGraphGeometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothSurfaceDouble
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.FiniteRegularity
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Data.Set.Card
import Mathlib.Basic.Finite.Sum
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.ContDiff.Operations
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! Finite smooth interval cuts of the actual arrangement, pullback to the
original surface, and exact original-atlas graph stars and local sectors. -/
set_option autoImplicit false
noncomputable section
open Set Topology
open scoped ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BoundaryData
open P202Specs.PlanarRegionTopology (Plane PlanarRegion)
open P202Specs.SurfaceRegionConstruction
universe u v
namespace P202.SurfaceRegionConstruction
variable {X : Type u} [TopologicalSpace X]

/-- A connected set missing an open set's frontier cannot switch membership.
This is the disk-membership step in the source's chart-containment argument. -/
theorem subset_of_avoids_frontier {U C : Set X} (hU : IsOpen U)
    (hC : IsPreconnected C) (hmiss : Disjoint C (frontier U))
    (hmeet : (C ∩ U).Nonempty) : C ⊆ U := by
  apply hC.subset_of_closure_inter_subset hU hmeet
  rintro x ⟨hxcl, hxC⟩
  by_contra hxU
  exact Set.disjoint_left.mp hmiss hxC
    ⟨hxcl, by simpa only [hU.interior_eq] using hxU⟩

/-- The closure of a connected complementary component remains inside one
closed chart disk, as soon as the disks cover it and their frontiers are
contained in the graph. Finiteness and transversality are not assumed here. -/
theorem closure_subset_one_cover {ι : Type*} (U K : ι → Set X) (G C : Set X)
    (hU : ∀ i, IsOpen (U i)) (hUK : ∀ i, U i ⊆ K i)
    (hK : ∀ i, IsClosed (K i)) (hfrontier : ∀ i, frontier (U i) ⊆ G)
    (hcover : C ⊆ ⋃ i, U i) (hC : IsConnected C) (hCG : Disjoint C G) :
    ∃ i, closure C ⊆ K i := by
  obtain ⟨p, hp⟩ := hC.nonempty
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp (hcover hp)
  have hsub : C ⊆ U i := subset_of_avoids_frontier (hU i) hC.isPreconnected
    (hCG.mono_right (hfrontier i)) ⟨p, hp, hpi⟩
  exact ⟨i, closure_minimal (hsub.trans (hUK i)) (hK i)⟩

namespace ChartDisk
open P202Specs.SurfaceRegionConstruction.ChartDisk
variable {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A)

theorem isOpen_inner : IsOpen d.inner :=
  d.chart.isOpen_inter_preimage Metric.isOpen_ball

theorem outer_subset_source : d.outer ⊆ d.chart.source := by
  rintro x ⟨y, hy, rfl⟩
  exact d.chart.map_target (d.closedBall_subset hy)

theorem inner_subset_outer : d.inner ⊆ d.outer := by
  rintro x ⟨hxs, hxb⟩
  refine ⟨d.chart x, Metric.closedBall_subset_closedBall d.inner_lt_outer.le
    (Metric.ball_subset_closedBall hxb), ?_⟩
  exact d.chart.left_inv hxs

theorem isCompact_outer : IsCompact d.outer :=
  (isCompact_closedBall d.center d.outerRadius).image_of_continuousOn
    (d.chart.symm.continuousOn.mono d.closedBall_subset)

theorem closure_inner_subset_outer [T2Space X] : closure d.inner ⊆ d.outer :=
  closure_minimal (inner_subset_outer d) (isCompact_outer d).isClosed

theorem closedBall_subset_target {r : ℝ} (hr : r ≤ d.outerRadius) :
    Metric.closedBall d.center r ⊆ d.chart.target :=
  (Metric.closedBall_subset_closedBall hr).trans d.closedBall_subset

theorem isOpen_openAtRadius (r : ℝ) : IsOpen (openAtRadius d r) :=
  d.chart.isOpen_inter_preimage Metric.isOpen_ball

theorem isCompact_closedAtRadius {r : ℝ} (hr : r ≤ d.outerRadius) :
    IsCompact (closedAtRadius d r) :=
  (isCompact_closedBall d.center r).image_of_continuousOn
    (d.chart.symm.continuousOn.mono (closedBall_subset_target d hr))

theorem closedAtRadius_subset_source {r : ℝ} (hr : r ≤ d.outerRadius) :
    closedAtRadius d r ⊆ d.chart.source := by
  rintro x ⟨z, hz, rfl⟩
  exact d.chart.map_target (closedBall_subset_target d hr hz)

theorem openAtRadius_subset_closedAtRadius (r : ℝ) :
    openAtRadius d r ⊆ closedAtRadius d r := by
  rintro x ⟨hxs, hxb⟩
  exact ⟨d.chart x, Metric.ball_subset_closedBall hxb, d.chart.left_inv hxs⟩

/-- The final disks still cover the inner disks at every permitted radius. -/
theorem inner_subset_openAtRadius {r : ℝ} (hr : d.innerRadius ≤ r) :
    d.inner ⊆ openAtRadius d r :=
  inter_subset_inter_right _ (preimage_mono (Metric.ball_subset_ball hr))

/-- The image/closure equality is ambient, including at the disk boundary;
the compact outer disk prevents loss of points through the chart boundary. -/
theorem closure_openAtRadius [T2Space X] {r : ℝ} (hpos : 0 < r)
    (hr : r ≤ d.outerRadius) :
    closure (openAtRadius d r) = closedAtRadius d r := by
  have hcl : closure (openAtRadius d r) ⊆ d.chart.source :=
    (closure_minimal (openAtRadius_subset_closedAtRadius d r)
      (isCompact_closedAtRadius d hr).isClosed).trans (closedAtRadius_subset_source d hr)
  have hi : d.chart.IsImage (openAtRadius d r) (Metric.ball d.center r) := by
    intro x hx
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  have heq := hi.closure.symm_image_eq
  rw [closure_ball d.center hpos.ne', inter_eq_right.mpr (closedBall_subset_target d hr),
    inter_eq_right.mpr hcl] at heq
  exact heq.symm

/-- The disk frontier is exactly the actual coordinate circle selected by
Sard, with no other boundary pieces introduced by the partial chart. -/
theorem frontier_openAtRadius [T2Space X] {r : ℝ} (hpos : 0 < r)
    (hr : r ≤ d.outerRadius) :
    frontier (openAtRadius d r) = circleAtRadius d r := by
  have hfront : frontier (openAtRadius d r) ⊆ d.chart.source := by
    rw [frontier, closure_openAtRadius d hpos hr]
    exact sdiff_subset.trans (closedAtRadius_subset_source d hr)
  have hsph : Metric.sphere d.center r ⊆ d.chart.target :=
    Metric.sphere_subset_closedBall.trans (closedBall_subset_target d hr)
  have hi : d.chart.IsImage (openAtRadius d r) (Metric.ball d.center r) := by
    intro x hx
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  have heq := hi.frontier.symm_image_eq
  rw [frontier_ball d.center hpos.ne', inter_eq_right.mpr hsph,
    inter_eq_right.mpr hfront] at heq
  exact heq.symm

theorem closure_openAtRadius_subset_outer [T2Space X] {r : ℝ} (hpos : 0 < r)
    (hr : r ≤ d.outerRadius) : closure (openAtRadius d r) ⊆ d.outer := by
  rw [closure_openAtRadius d hpos hr]
  exact image_mono (Metric.closedBall_subset_closedBall hr)

end ChartDisk

/-- The source's entire chart-containment argument for the selected final
circles. Both the final closed disk and the original atlas chart are retained
in the conclusion. No regularity of the crossings is used at this stage. -/
theorem closure_in_selected_chart [T2Space X] {ι : Type*}
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ι → ChartDisk X A) (r : ι → ℝ)
    (hlower : ∀ i, (d i).innerRadius ≤ r i) (hupper : ∀ i, r i ≤ (d i).outerRadius)
    (G C : Set X) (hcircle : ∀ i, ChartDisk.circleAtRadius (d i) (r i) ⊆ G)
    (hcover : C ⊆ ⋃ i, (d i).inner) (hC : IsConnected C) (hCG : Disjoint C G) :
    ∃ i, closure C ⊆ ChartDisk.closedAtRadius (d i) (r i) ∧
      closure C ⊆ (d i).chart.source := by
  have hpos : ∀ i, 0 < r i := fun i => (d i).inner_pos.trans_le (hlower i)
  have hcover' : C ⊆ ⋃ i, ChartDisk.openAtRadius (d i) (r i) :=
    hcover.trans (iUnion_mono (fun i => ChartDisk.inner_subset_openAtRadius (d i) (hlower i)))
  obtain ⟨i, hi⟩ := closure_subset_one_cover
    (fun i => ChartDisk.openAtRadius (d i) (r i))
    (fun i => ChartDisk.closedAtRadius (d i) (r i)) G C
    (fun i => ChartDisk.isOpen_openAtRadius (d i) (r i))
    (fun i => ChartDisk.openAtRadius_subset_closedAtRadius (d i) (r i))
    (fun i => (ChartDisk.isCompact_closedAtRadius (d i) (hupper i)).isClosed)
    (fun i => by rw [ChartDisk.frontier_openAtRadius (d i) (hpos i) (hupper i)]; exact hcircle i)
    hcover' hC hCG
  exact ⟨i, hi, hi.trans (ChartDisk.closedAtRadius_subset_source (d i) (hupper i))⟩

namespace EmbeddedGraph
variable {kind : ModelKind} {S : SmoothManifold 2 kind X} (G : EmbeddedGraph S)

theorem isCompact_carrier : IsCompact G.carrier :=
  (Set.finite_range G.vertex).isCompact.union
    (isCompact_iUnion (fun i => isCompact_range (G.edge i).continuous))

theorem isClosed_carrier : IsClosed G.carrier := by
  let := S.topologicalManifold.hausdorff
  exact (isCompact_carrier G).isClosed

/-- Endpoints are precisely the points of an edge that can be vertices. -/
theorem edge_preimage_compl_vertices (i : Fin G.edgeCount) :
    G.edge i ⁻¹' (range G.vertex)ᶜ = {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
  ext t
  constructor
  · intro h
    have h0 : t ≠ 0 := by
      rintro rfl
      exact h ⟨G.initial i, (G.at_zero i).symm⟩
    have h1 : t ≠ 1 := by
      rintro rfl
      exact h ⟨G.terminal i, (G.at_one i).symm⟩
    have hv0 : (t : ℝ) ≠ 0 := fun h => h0 (Subtype.ext h)
    have hv1 : (t : ℝ) ≠ 1 := fun h => h1 (Subtype.ext h)
    exact ⟨lt_of_le_of_ne t.property.1 hv0.symm, lt_of_le_of_ne t.property.2 hv1⟩
  · rintro ⟨h0, h1⟩
    exact G.avoids_vertices i t h0 h1

/-- The open edges have the actual subspace topology of embedded intervals.
Compactness of each closed parameter interval controls both end accumulations,
including when the two endpoints of an edge are the same vertex. -/
theorem open_edge_embedding (i : Fin G.edgeCount) :
    Topology.IsEmbedding (fun t : {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} =>
      G.edge i t.val) := by
  let := S.topologicalManifold.hausdorff
  let V : Set X := (range G.vertex)ᶜ
  have hc : IsClosedMap (G.edge i) := (G.edge i).continuous.isClosedMap
  have hrestr : Topology.IsClosedEmbedding (V.restrictPreimage (G.edge i)) := by
    apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (G.edge i).continuous.restrictPreimage _ (hc.restrictPreimage V)
    intro a b hab
    apply Subtype.ext
    apply G.open_injective i
    · rw [← edge_preimage_compl_vertices G i]
      exact a.property
    · rw [← edge_preimage_compl_vertices G i]
      exact b.property
    · exact congrArg Subtype.val hab
  have he := Topology.IsEmbedding.subtypeVal.comp hrestr.isEmbedding
  change Topology.IsEmbedding (fun t : G.edge i ⁻¹' V => G.edge i t.val) at he
  exact he.comp (Homeomorph.setCongr (edge_preimage_compl_vertices G i).symm).isEmbedding

/-- The actual finite graph on an empty surface, with no edges or vertices. -/
def empty (S : SmoothManifold 2 kind X) : EmbeddedGraph S where
  vertexCount := 0
  edgeCount := 0
  vertex := fun i => Fin.elim0 i
  vertex_injective := fun i => Fin.elim0 i
  edge := fun i => Fin.elim0 i
  initial := fun i => Fin.elim0 i
  terminal := fun i => Fin.elim0 i
  at_zero := fun i => Fin.elim0 i
  at_one := fun i => Fin.elim0 i
  open_injective := fun i => Fin.elim0 i
  avoids_vertices := fun i => Fin.elim0 i
  disjoint_open_edges := fun i => Fin.elim0 i
  regular := fun i => Fin.elim0 i

@[simp] theorem empty_carrier (S : SmoothManifold 2 kind X) :
    (empty S).carrier = ∅ := by
  ext x
  simp [P202Specs.SurfaceRegionConstruction.EmbeddedGraph.carrier, empty]

end EmbeddedGraph

namespace Components
variable (U : Set X)

theorem subset (a : ConnectedComponents U) : componentSet U a ⊆ U := by
  rintro x ⟨p, _, rfl⟩
  exact p.property

theorem mk_eq (p : U) :
    componentSet U (ConnectedComponents.mk p) = connectedComponentIn U p.val := by
  rw [connectedComponentIn_eq_image p.property]
  unfold componentSet
  congr 1
  ext q
  exact ConnectedComponents.coe_eq_coe'

theorem nonempty (a : ConnectedComponents U) : (componentSet U a).Nonempty := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe a
  exact ⟨p.val, p, rfl, rfl⟩

theorem isConnected (a : ConnectedComponents U) : IsConnected (componentSet U a) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe a
  rw [mk_eq]
  exact isConnected_connectedComponentIn_iff.mpr p.property

theorem isOpen [LocallyConnectedSpace X] (hU : IsOpen U) (a : ConnectedComponents U) :
    IsOpen (componentSet U a) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe a
  rw [mk_eq]
  exact hU.connectedComponentIn

theorem disjoint (a b : ConnectedComponents U) (hab : a ≠ b) :
    Disjoint (componentSet U a) (componentSet U b) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
  have hpq : p = q := Subtype.ext heq.symm
  exact hab (hp.symm.trans (hpq ▸ hq))

theorem union_eq : ⋃ a : ConnectedComponents U, componentSet U a = U := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (subset U)
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨ConnectedComponents.mk (⟨x, hx⟩ : U), ⟨x, hx⟩, rfl, rfl⟩

/-- A connected subset meeting one component is entirely in that component.
This applies to a local sector without assuming that it is a global region. -/
theorem contains_preconnected {C : Set X} (hC : IsPreconnected C) (hCU : C ⊆ U)
    (a : ConnectedComponents U) (hmeet : (C ∩ componentSet U a).Nonempty) :
    C ⊆ componentSet U a := by
  obtain ⟨x, hxC, p, hp, rfl⟩ := hmeet
  rw [← hp, mk_eq]
  exact hC.subset_connectedComponentIn hxC hCU

/-- Inclusion of subsets induces inclusion of their actual connected
components. No local connectedness or openness is needed. -/
def inclusion {V : Set X} (hVU : V ⊆ U) (a : ConnectedComponents V) :
    ConnectedComponents U :=
  ConnectedComponents.mk
    ⟨(nonempty V a).choose, hVU (subset V a (nonempty V a).choose_spec)⟩

theorem subset_inclusion {V : Set X} (hVU : V ⊆ U) (a : ConnectedComponents V) :
    componentSet V a ⊆ componentSet U (inclusion U hVU a) := by
  apply contains_preconnected U (isConnected V a).isPreconnected
    ((subset V a).trans hVU)
  refine ⟨(nonempty V a).choose, (nonempty V a).choose_spec, ?_⟩
  exact ⟨_, rfl, rfl⟩

/-- A neighborhood meets only finitely many global components if its
intersection with the open complement has finitely many local components.
Local sectors are allowed to merge into the same global component. -/
theorem finite_meeting_of_finite_local_components (N : Set X)
    [Finite (ConnectedComponents (U ∩ N : Set X))] :
    {a : ConnectedComponents U | (componentSet U a ∩ N).Nonempty}.Finite := by
  classical
  let f := inclusion U (inter_subset_left : U ∩ N ⊆ U)
  apply (Set.finite_range f).subset
  rintro a ⟨x, hx, hxN⟩
  let b := ConnectedComponents.mk (⟨x, subset U a hx, hxN⟩ : (U ∩ N : Set X))
  have hxb : x ∈ componentSet (U ∩ N) b := ⟨_, rfl, rfl⟩
  have hxf : x ∈ componentSet U (f b) := subset_inclusion U _ b hxb
  have heq : f b = a := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint U (f b) a hne) hxf hx
  exact ⟨b, heq⟩

/-- Finite local sector counts give a locally finite family of global
components, including at points of the removed graph. -/
theorem locallyFinite_of_finite_local_components
    (hlocal : ∀ x : X, ∃ N ∈ 𝓝 x, Finite (ConnectedComponents (U ∩ N : Set X))) :
    LocallyFinite (componentSet U) := by
  intro x
  obtain ⟨N, hxN, hN⟩ := hlocal x
  let := hN
  exact ⟨N, hxN, finite_meeting_of_finite_local_components U N⟩

/-- Compactness turns the local finite-sector statement into the required
global finiteness of complementary components. The complement itself need
not be compact, and the graph need not be connected. -/
theorem finite_of_finite_local_components [CompactSpace X]
    (hlocal : ∀ x : X, ∃ N ∈ 𝓝 x, Finite (ConnectedComponents (U ∩ N : Set X))) :
    Finite (ConnectedComponents U) :=
  Set.finite_univ_iff.mp
    ((locallyFinite_of_finite_local_components U hlocal).finite_of_compact (nonempty U))

/-- For an open complement in a locally connected compact space it suffices
to count local sectors at the removed set. At all other points a connected
open component itself supplies the neighborhood. -/
theorem finite_of_finite_local_components_outside [CompactSpace X] [LocallyConnectedSpace X]
    (hU : IsOpen U)
    (hlocal : ∀ x ∉ U, ∃ N ∈ 𝓝 x, Finite (ConnectedComponents (U ∩ N : Set X))) :
    Finite (ConnectedComponents U) := by
  apply finite_of_finite_local_components U
  intro x
  by_cases hx : x ∈ U
  · let a := ConnectedComponents.mk (⟨x, hx⟩ : U)
    have hxC : x ∈ componentSet U a := ⟨_, rfl, rfl⟩
    refine ⟨componentSet U a, (isOpen U hU a).mem_nhds hxC, ?_⟩
    rw [inter_eq_right.mpr (subset U a)]
    let := isPreconnected_iff_preconnectedSpace.mp (isConnected U a).isPreconnected
    infer_instance
  · exact hlocal x hx

/-- Components are closed relative to the original open complement; taking
ambient closure can add only points outside that complement. -/
theorem closure_inter (a : ConnectedComponents U) :
    closure (componentSet U a) ∩ U = componentSet U a := by
  let F : Set U := {p | ConnectedComponents.mk p = a}
  have hF : IsClosed F := by
    obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe a
    have heq : F = connectedComponent p := by
      ext q
      change ConnectedComponents.mk q = a ↔ q ∈ connectedComponent p
      rw [← hp]
      exact ConnectedComponents.coe_eq_coe'
    rw [heq]
    exact isClosed_connectedComponent
  have hpre : (Subtype.val : U → X) ⁻¹' closure (componentSet U a) = F := by
    change (Subtype.val : U → X) ⁻¹' closure (Subtype.val '' F) = F
    rw [← Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, hF.closure_eq]
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxU⟩
    have hp : (⟨x, hxU⟩ : U) ∈ F := by rw [← hpre]; exact hx
    exact ⟨⟨x, hxU⟩, hp, rfl⟩
  · intro x hx
    exact ⟨subset_closure hx, subset U a hx⟩

/-- The complement components have the precise ambient boundary required in
the decomposition interface. Local connectivity is what makes them open. -/
theorem frontier_eq [LocallyConnectedSpace X] (G : Set X) (hG : IsClosed G)
    (a : ConnectedComponents (Gᶜ : Set X)) :
    frontier (componentSet Gᶜ a) = closure (componentSet Gᶜ a) ∩ G := by
  rw [frontier, (isOpen Gᶜ hG.isOpen_compl a).interior_eq]
  ext x
  constructor
  · rintro ⟨hxcl, hxC⟩
    refine ⟨hxcl, ?_⟩
    by_contra hxG
    exact hxC (by rw [← closure_inter Gᶜ a]; exact ⟨hxcl, hxG⟩)
  · rintro ⟨hxcl, hxG⟩
    exact ⟨hxcl, fun hxC => (subset Gᶜ a hxC) hxG⟩

end Components

namespace EmbeddedGraph
variable {kind : ModelKind} {S : SmoothManifold 2 kind X} (G : EmbeddedGraph S)

/-- Openness and frontier identification need no region-boundary certificate. -/
theorem open_component (a : ConnectedComponents (G.carrierᶜ : Set X)) :
    IsOpen (componentSet G.carrierᶜ a) := by
  let := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  exact Components.isOpen _ (isClosed_carrier G).isOpen_compl a

theorem connected_component_closure (a : ConnectedComponents (G.carrierᶜ : Set X)) :
    IsConnected (closure (componentSet G.carrierᶜ a)) :=
  (Components.isConnected _ a).closure

theorem compact_component_closure [CompactSpace X]
    (a : ConnectedComponents (G.carrierᶜ : Set X)) :
    IsCompact (closure (componentSet G.carrierᶜ a)) := isClosed_closure.isCompact

theorem frontier_component (a : ConnectedComponents (G.carrierᶜ : Set X)) :
    frontier (componentSet G.carrierᶜ a) = closure (componentSet G.carrierᶜ a) ∩ G.carrier := by
  let := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  exact Components.frontier_eq _ (isClosed_carrier G) a

theorem disjoint_component_interiors (a b : ConnectedComponents (G.carrierᶜ : Set X))
    (hab : a ≠ b) :
    Disjoint (interior (closure (componentSet G.carrierᶜ a)))
      (interior (closure (componentSet G.carrierᶜ b))) := by
  have h := (Components.disjoint _ a b hab).closure_left (open_component G b)
  exact ((h.mono_left interior_subset).closure_right isOpen_interior).mono_right interior_subset

end EmbeddedGraph

/-- The neighborhood in a graph star uses the actual surface topology. -/
theorem GraphStar.isOpen_neighborhood {kind : ModelKind}
    {S : SmoothManifold 2 kind X} {G : EmbeddedGraph S} {p : X}
    (s : GraphStar G p) : IsOpen s.neighborhood := by
  exact s.chart.isOpen_inter_preimage
    (Metric.isOpen_ball.preimage (toPlane.continuous.comp continuous_subtype_val))

theorem GraphStar.mem_neighborhood {kind : ModelKind}
    {S : SmoothManifold 2 kind X} {G : EmbeddedGraph S} {p : X}
    (s : GraphStar G p) : p ∈ s.neighborhood := by
  refine ⟨s.mem_source, ?_⟩
  change dist (coordinates s.chart p) (coordinates s.chart p) < s.radius
  simpa only [dist_self] using s.radius_pos

/-- Compact transverse intersections are finite once the local inverse theorem
has isolated every crossing. The local-isolation premise is explicit; this
lemma does not replace the missing transversality construction. -/
theorem finite_intersection_of_local_isolation [T2Space X] {A B : Set X}
    (hA : IsCompact A) (hB : IsCompact B)
    (hisolate : ∀ p ∈ A ∩ B, ∃ N : Set X, IsOpen N ∧ N ∩ (A ∩ B) = {p}) :
    (A ∩ B).Finite :=
  (hA.inter hB).finite (isDiscrete_iff_forall_mem_exists_isOpen.mpr hisolate)

/-- Disk membership is constant throughout each connected complementary set. -/
theorem membership_constant {C U : Set X} (hC : IsPreconnected C) (hU : IsOpen U)
    (hmiss : Disjoint C (frontier U)) {x y : X} (hx : x ∈ C) (hy : y ∈ C) :
    x ∈ U ↔ y ∈ U := by
  constructor
  · intro hxU
    exact subset_of_avoids_frontier hU hC hmiss ⟨x, hx, hxU⟩ hy
  · intro hyU
    exact subset_of_avoids_frontier hU hC hmiss ⟨y, hy, hyU⟩ hx

namespace Components

/-- A disk whose frontier is removed has constant membership on each actual
global complementary component. -/
theorem disk_membership_constant (G D : Set X) (hD : IsOpen D)
    (hfrontier : frontier D ⊆ G) (a : ConnectedComponents (Gᶜ : Set X))
    {x y : X} (hx : x ∈ componentSet Gᶜ a) (hy : y ∈ componentSet Gᶜ a) :
    x ∈ D ↔ y ∈ D := by
  apply membership_constant (isConnected Gᶜ a).isPreconnected hD _ hx hy
  exact Set.disjoint_left.mpr (fun p hp hf => subset Gᶜ a hp (hfrontier hf))

/-- Distinct local sectors cannot merge into a global component when their
disk-membership vectors differ. This is the source's no-return argument; the
sector separation must be proved for the actual transverse arrangement. -/
theorem inclusion_injective_of_disk_memberships (G N : Set X) {ι : Type*}
    (D : ι → Set X) (hD : ∀ i, IsOpen (D i)) (hfrontier : ∀ i, frontier (D i) ⊆ G)
    (hseparate : ∀ a b : ConnectedComponents (N \ G : Set X), a ≠ b →
      ∃ i, ∃ x ∈ componentSet (N \ G) a, ∃ y ∈ componentSet (N \ G) b,
        ¬ (x ∈ D i ↔ y ∈ D i)) :
    Function.Injective (inclusion Gᶜ (fun _ hx => hx.2 : N \ G ⊆ Gᶜ)) := by
  intro a b hab
  by_contra hne
  obtain ⟨i, x, hx, y, hy, hxy⟩ := hseparate a b hne
  have hx' := subset_inclusion Gᶜ (fun _ hx => hx.2 : N \ G ⊆ Gᶜ) a hx
  have hy' := subset_inclusion Gᶜ (fun _ hx => hx.2 : N \ G ⊆ Gᶜ) b hy
  rw [← hab] at hy'
  exact hxy (disk_membership_constant G (D i) (hD i) (hfrontier i) _ hx' hy')

/-- Injectivity of the local-to-global component map is exactly the missing
condition that makes a whole global component meet a neighborhood in one
sector. This conclusion is about actual subsets, not just component labels. -/
theorem component_inter_eq_of_inclusion_injective (U N : Set X)
    (hinj : Function.Injective
      (inclusion U (inter_subset_left : U ∩ N ⊆ U)))
    (a : ConnectedComponents (U ∩ N : Set X)) :
    componentSet U (inclusion U inter_subset_left a) ∩ N = componentSet (U ∩ N) a := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxN⟩
    let b := ConnectedComponents.mk (⟨x, subset U _ hx, hxN⟩ : (U ∩ N : Set X))
    have hxb : x ∈ componentSet (U ∩ N) b := ⟨_, rfl, rfl⟩
    have hx' := subset_inclusion U (inter_subset_left : U ∩ N ⊆ U) b hxb
    have hab : inclusion U inter_subset_left a = inclusion U inter_subset_left b := by
      by_contra hne
      exact Set.disjoint_left.mp (disjoint U _ _ hne) hx hx'
    exact hinj hab ▸ hxb
  · intro x hx
    exact ⟨subset_inclusion U inter_subset_left a hx, (subset (U ∩ N) a hx).2⟩

/-- Every global component meeting the neighborhood occupies a unique local
sector, provided distinct local sectors cannot merge globally. -/
theorem exists_unique_local_component (U N : Set X)
    (hinj : Function.Injective
      (inclusion U (inter_subset_left : U ∩ N ⊆ U)))
    (a : ConnectedComponents U) (hmeet : (componentSet U a ∩ N).Nonempty) :
    ∃! b : ConnectedComponents (U ∩ N : Set X),
      componentSet U a ∩ N = componentSet (U ∩ N) b := by
  obtain ⟨x, hx, hxN⟩ := hmeet
  let b := ConnectedComponents.mk (⟨x, subset U a hx, hxN⟩ : (U ∩ N : Set X))
  have hxb : x ∈ componentSet (U ∩ N) b := ⟨_, rfl, rfl⟩
  have hx' := subset_inclusion U (inter_subset_left : U ∩ N ⊆ U) b hxb
  have hab : a = inclusion U inter_subset_left b := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint U _ _ hne) hx hx'
  have heq : componentSet U a ∩ N = componentSet (U ∩ N) b := by
    rw [hab]
    exact component_inter_eq_of_inclusion_injective U N hinj b
  refine ⟨b, heq, ?_⟩
  intro c hc
  by_contra hne
  have hxc : x ∈ componentSet (U ∩ N) c := by rw [← hc]; exact ⟨hx, hxN⟩
  exact Set.disjoint_left.mp (disjoint (U ∩ N) c b hne) hxc hxb

/-- At a closure point every open neighborhood meets the component, so the
previous theorem applies to all incident regions, including graph vertices. -/
theorem exists_unique_local_component_at_closure (U N : Set X)
    (hinj : Function.Injective
      (inclusion U (inter_subset_left : U ∩ N ⊆ U)))
    (hN : IsOpen N) (a : ConnectedComponents U) {p : X}
    (hp : p ∈ closure (componentSet U a)) (hpN : p ∈ N) :
    ∃! b : ConnectedComponents (U ∩ N : Set X),
      componentSet U a ∩ N = componentSet (U ∩ N) b := by
  apply exists_unique_local_component U N hinj a
  obtain ⟨x, hxN, hx⟩ := mem_closure_iff_nhds.mp hp N (hN.mem_nhds hpN)
  exact ⟨x, hx, hxN⟩

end Components

/-- The supplied inner disks cover any connected set in the designated copy.
Avoiding the arrangement forces the whole connected set into one selected open
disk, and continuity puts its closure in the corresponding closed disk. -/
theorem copy_connected_set_in_disk {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    {C : Set X} (hC : IsConnected C)
    (hmiss : Disjoint C
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)) :
    ∃ i : Fin T.count,
      C ⊆ P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        (T.disk i).openAtRadius (T.radius i) ∧
      closure C ⊆ P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        (T.disk i).closedAtRadius (T.radius i) := by
  let := D.hausdorff
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  have hf : Continuous f := (D.copy_closedEmbedding s).continuous
  have himage : IsConnected (f '' C) := hC.image f hf.continuousOn
  have hdisjoint : Disjoint (f '' C) (arrangementCarrier T) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hy
    exact Set.disjoint_left.mp hmiss hx hy
  obtain ⟨x, hx⟩ := hC.nonempty
  obtain ⟨i, hi⟩ := mem_iUnion.mp (T.inner_cover (mem_range_self x))
  have hxi : f x ∈ (T.disk i).openAtRadius (T.radius i) :=
    ChartDisk.inner_subset_openAtRadius _ (T.radius_bounds i).1.le hi
  have hfront : frontier ((T.disk i).openAtRadius (T.radius i)) ⊆ arrangementCarrier T := by
    rw [ChartDisk.frontier_openAtRadius _
      ((T.disk i).inner_pos.trans (T.radius_bounds i).1) (T.radius_bounds i).2.le]
    exact fun _ hy => Or.inr (mem_iUnion.mpr ⟨i, hy⟩)
  have hsub : f '' C ⊆ (T.disk i).openAtRadius (T.radius i) :=
    subset_of_avoids_frontier (ChartDisk.isOpen_openAtRadius _ _)
      himage.isPreconnected (hdisjoint.mono_right hfront) ⟨f x, ⟨x, hx, rfl⟩, hxi⟩
  have hcl : closure (f '' C) ⊆ (T.disk i).closedAtRadius (T.radius i) :=
    closure_minimal (hsub.trans (ChartDisk.openAtRadius_subset_closedAtRadius _ _))
      (ChartDisk.isCompact_closedAtRadius _ (T.radius_bounds i).2.le).isClosed
  exact ⟨i, fun y hy => hsub (mem_image_of_mem f hy),
    fun y hy => hcl (image_closure_subset_closure_image hf (mem_image_of_mem f hy))⟩

/-- Chart containment for the actual complementary components of the
restricted arrangement, before constructing a graph or any planar region.
Subordination is used only on the selected disk's chart source. -/
theorem arrangement_component_in_original_chart {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    (hsubordinate : CopySubordinate S D s A)
    {B : CompactSmoothSeam D.manifold}
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (a : ConnectedComponents
      ((P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)ᶜ : Set X)) :
    ∃ (i : Fin T.count) (e : ModelChart 2 kind X), e ∈ S.smoothStructure.val ∧
      componentSet (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)ᶜ a ⊆
        P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
          (T.disk i).openAtRadius (T.radius i) ∧
      closure (componentSet (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)ᶜ a) ⊆
        P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
          (T.disk i).closedAtRadius (T.radius i) ∧
      closure (componentSet (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)ᶜ a) ⊆ e.source := by
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  let U : Set X := (f ⁻¹' arrangementCarrier T)ᶜ
  have hmiss : Disjoint (componentSet U a) (f ⁻¹' arrangementCarrier T) :=
    Set.disjoint_left.mpr (fun _ hx hg => Components.subset U a hx hg)
  obtain ⟨i, hi, hcl⟩ := copy_connected_set_in_disk S D s T
    (Components.isConnected U a) hmiss
  obtain ⟨d, hdA, heqd⟩ := (T.disk i).chart_mem
  obtain ⟨e, heS, hde⟩ := hsubordinate d hdA
  refine ⟨i, e, heS, hi, hcl, ?_⟩
  intro x hx
  apply hde
  have hsource := ChartDisk.closedAtRadius_subset_source (T.disk i)
    (T.radius_bounds i).2.le (hcl hx)
  rw [← heqd] at hsource
  exact hsource

namespace Components

/-- A finite cover by preconnected subsets gives finitely many actual
components, even if some covering subsets are empty or overlap. -/
theorem finite_of_preconnected_cover {ι : Type*} [Finite ι] (U : Set X)
    (C : ι → Set X) (hC : ∀ i, IsPreconnected (C i))
    (hsub : ∀ i, C i ⊆ U) (hcover : U ⊆ ⋃ i, C i) :
    Finite (ConnectedComponents U) := by
  classical
  let (i : ι) : PreconnectedSpace (C i) :=
    isPreconnected_iff_preconnectedSpace.mp (hC i)
  let f : (Σ i, ConnectedComponents (C i)) → ConnectedComponents U :=
    fun b => inclusion U (hsub b.1) b.2
  apply Finite.of_surjective f
  intro a
  obtain ⟨x, hx⟩ := nonempty U a
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover (subset U a hx))
  let b := ConnectedComponents.mk (⟨x, hxi⟩ : C i)
  have hxb : x ∈ componentSet (C i) b := ⟨_, rfl, rfl⟩
  have hxf := subset_inclusion U (hsub i) b hxb
  refine ⟨⟨i, b⟩, ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (disjoint U (f ⟨i,b⟩) a hne) hxf hx

end Components

namespace NormalSectors

/-- Open sign chambers; inactive axes impose no inequality. -/
def chamber (J : Set (Fin 2)) (r : ℝ) (σ : Fin 2 → Bool) : Set Plane :=
  Metric.ball 0 r ∩ ⋂ a ∈ J, {z | if σ a then 0 < z a else z a < 0}

/-- Every sign chamber is convex, including when there are no active axes. -/
theorem convex_chamber (J : Set (Fin 2)) (r : ℝ) (σ : Fin 2 → Bool) :
    Convex ℝ (chamber J r σ) := by
  apply (convex_ball (0 : Plane) r).inter
  apply convex_iInter₂
  intro a _
  have hlinear : IsLinearMap ℝ (fun z : Plane => z a) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  cases h : σ a <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact convex_halfSpace_lt hlinear 0
  · exact convex_halfSpace_gt hlinear 0

/-- Coordinate axes removed from a disk are covered by its four possible sign
chambers. Unused signs give duplicate chambers, which causes no problem. -/
theorem union_chambers (J : Set (Fin 2)) (r : ℝ) :
    (⋃ σ : Fin 2 → Bool, chamber J r σ) =
      {z : Plane | z ∈ Metric.ball 0 r ∧ ∀ a ∈ J, z a ≠ 0} := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨σ, hzball, hzsign⟩ := mem_iUnion.mp hz
    refine ⟨hzball, ?_⟩
    intro a ha
    have h := mem_iInter₂.mp hzsign a ha
    cases hσ : σ a <;> simp only [hσ, Bool.false_eq_true, ↓reduceIte] at h
    · exact ne_of_lt h
    · exact ne_of_gt h
  · rintro ⟨hzball, hzaxes⟩
    refine mem_iUnion.mpr ⟨fun a => decide (0 < z a), hzball, ?_⟩
    apply mem_iInter₂.mpr
    intro a ha
    simp only [decide_eq_true_eq]
    split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (le_of_not_gt h) (hzaxes a ha)

/-- Finitely many local components is a consequence of the exact axis normal
form, rather than an assumed property of an arrangement. -/
theorem finite_axis_complement (J : Set (Fin 2)) (r : ℝ) :
    Finite (ConnectedComponents
      {z : Plane | z ∈ Metric.ball 0 r ∧ ∀ a ∈ J, z a ≠ 0}) := by
  apply Components.finite_of_preconnected_cover _ (chamber J r)
    (fun σ => (convex_chamber J r σ).isPreconnected)
  · intro σ
    rw [← union_chambers J r]
    exact fun x hx => mem_iUnion.mpr ⟨σ, hx⟩
  · rw [union_chambers]

end NormalSectors

namespace Arrangement
variable {W : SmoothManifold 2 .euclidean X} {K : Set X}
variable {A : Set (ModelChart 2 .euclidean X)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)

/-- The carrier is the union of the actual curves, with `none` denoting seam. -/
theorem carrier_eq_iUnion : arrangementCarrier T =
    ⋃ k : Option (Fin T.count), arrangementCurve B.carrier T.disk T.radius k := by
  ext x
  simp only [arrangementCarrier, mem_union, mem_iUnion]
  constructor
  · rintro (hx | ⟨i, hi⟩)
    · exact ⟨none, hx⟩
    · exact ⟨some i, hi⟩
  · rintro ⟨k, hk⟩
    cases k with
    | none => exact Or.inl hk
    | some i => exact Or.inr ⟨i, hk⟩

/-- The seam and circles form an actual compact carrier. -/
theorem isCompact_carrier : IsCompact (arrangementCarrier T) := by
  apply B.compact.union
  apply isCompact_iUnion
  intro i
  exact (isCompact_sphere (T.disk i).center (T.radius i)).image_of_continuousOn
    ((T.disk i).chart.symm.continuousOn.mono
      (Metric.sphere_subset_closedBall.trans
        (ChartDisk.closedBall_subset_target _ (T.radius_bounds i).2.le)))

theorem isClosed_carrier : IsClosed (arrangementCarrier T) := by
  let := W.topologicalManifold.hausdorff
  exact (isCompact_carrier T).isClosed

/-- All potential curve-curve crossings, including seam crossings, form a
finite set. Self-pairs are excluded; no compact seam parametrization is assumed. -/
theorem finite_crossings :
    (⋃ i : Option (Fin T.count), ⋃ j : {j : Option (Fin T.count) // i ≠ j},
      arrangementCurve B.carrier T.disk T.radius i ∩
        arrangementCurve B.carrier T.disk T.radius j.val).Finite := by
  apply Set.finite_iUnion
  intro i
  apply Set.finite_iUnion
  intro j
  cases i with
  | none =>
    rcases j with ⟨j, hj⟩
    cases j with
    | none => exact (hj rfl).elim
    | some b => simpa only [arrangementCurve, inter_comm] using T.finite_seam b
  | some a =>
    rcases j with ⟨j, hj⟩
    cases j with
    | none => exact T.finite_seam a
    | some b => exact T.finite_pairs a b (fun h => hj (congrArg some h))

variable {p : X} {O : Set X}
variable (F : ArrangementNormalForm W B.carrier T.disk T.radius p O)

/-- The actual open disk on which the normal form is exact. -/
def normalNeighborhood : Set X :=
  F.chart.source ∩ coordinates F.chart ⁻¹' Metric.ball 0 F.radius

def activeAxes : Set (Fin 2) := {a | ∃ k, F.axis k = some a}

theorem isOpen_normalNeighborhood : IsOpen (normalNeighborhood T F) :=
  F.chart.isOpen_inter_preimage
    (Metric.isOpen_ball.preimage (toPlane.continuous.comp continuous_subtype_val))

theorem mem_normalNeighborhood : p ∈ normalNeighborhood T F := by
  refine ⟨F.mem_source, ?_⟩
  change coordinates F.chart p ∈ Metric.ball 0 F.radius
  rw [F.centered]
  exact Metric.mem_ball_self F.radius_pos

/-- On the whole retained neighborhood, the removed carrier is exactly the
union of the active axes, not just equal to it as a germ at the center. -/
theorem carrier_iff_axis {x : X} (hx : x ∈ normalNeighborhood T F) :
    x ∈ arrangementCarrier T ↔ ∃ a ∈ activeAxes T F, coordinates F.chart x a = 0 := by
  rw [carrier_eq_iUnion T, mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨a, hka, hax⟩ := (F.curve_eq k x hx.1 hx.2).mp hk
    exact ⟨a, ⟨k, hka⟩, hax⟩
  · rintro ⟨a, ⟨k, hka⟩, hax⟩
    exact ⟨k, (F.curve_eq k x hx.1 hx.2).mpr ⟨a, hka, hax⟩⟩

/-- The smooth normal form has a genuine finite preconnected cover of its
complement, obtained by transporting the convex coordinate sign chambers. -/
theorem finite_local_components :
    Finite (ConnectedComponents (normalNeighborhood T F \ arrangementCarrier T : Set X)) := by
  let g : Plane → X := fun z => F.chart.symm (euclideanModelPlane.symm z)
  let C := NormalSectors.chamber (activeAxes T F) F.radius
  have htarget : ∀ z ∈ Metric.ball (0 : Plane) F.radius,
      euclideanModelPlane.symm z ∈ F.chart.target := by
    intro z hz
    apply F.ball_in_target
    change euclideanModelPlane (euclideanModelPlane.symm z) ∈ Metric.ball 0 F.radius
    simpa only [Homeomorph.apply_symm_apply] using hz
  have hg : ContinuousOn g (Metric.ball 0 F.radius) :=
    F.chart.symm.continuousOn.comp euclideanModelPlane.symm.continuous.continuousOn htarget
  have hcoord : ∀ z ∈ Metric.ball (0 : Plane) F.radius,
      coordinates F.chart (g z) = z := by
    intro z hz
    change euclideanModelPlane (F.chart (F.chart.symm (euclideanModelPlane.symm z))) = z
    rw [F.chart.right_inv (htarget z hz), Homeomorph.apply_symm_apply]
  have hcover : (⋃ σ : Fin 2 → Bool, g '' C σ) =
      normalNeighborhood T F \ arrangementCarrier T := by
    rw [← image_iUnion, NormalSectors.union_chambers]
    apply Set.Subset.antisymm
    · rintro x ⟨z, ⟨hzball, hzaxes⟩, rfl⟩
      have hxN : g z ∈ normalNeighborhood T F :=
        ⟨F.chart.map_target (htarget z hzball), by
          change coordinates F.chart (g z) ∈ Metric.ball 0 F.radius
          rwa [hcoord z hzball]⟩
      refine ⟨hxN, ?_⟩
      intro hxG
      obtain ⟨a, ha, hax⟩ := (carrier_iff_axis T F hxN).mp hxG
      rw [hcoord z hzball] at hax
      exact hzaxes a ha hax
    · rintro x ⟨hxN, hxG⟩
      refine ⟨coordinates F.chart x, ⟨hxN.2, ?_⟩, ?_⟩
      · intro a ha hzero
        exact hxG ((carrier_iff_axis T F hxN).mpr ⟨a, ha, hzero⟩)
      · change F.chart.symm (euclideanModelPlane.symm
          (euclideanModelPlane (F.chart x))) = x
        rw [Homeomorph.symm_apply_apply, F.chart.left_inv hxN.1]
  apply Components.finite_of_preconnected_cover _ (fun σ => g '' C σ)
  · intro σ
    exact (NormalSectors.convex_chamber _ _ σ).isPreconnected.image g
      (hg.mono inter_subset_left)
  · intro σ
    rw [← hcover]
    exact fun x hx => mem_iUnion.mpr ⟨σ, hx⟩
  · exact hcover.ge

end Arrangement
/-- A connected set avoiding the overlap of a closed two-set cover lies
entirely in one of its open sides as soon as it meets that side. Restriction
to either closed set therefore preserves preconnectedness. -/
theorem preconnected_inter_closed_cover {L R C G : Set X}
    (hL : IsClosed L) (hR : IsClosed R) (hcover : L ∪ R = univ)
    (hinter : L ∩ R ⊆ G) (hC : IsPreconnected C) (hmiss : Disjoint C G) :
    IsPreconnected (C ∩ L) := by
  by_cases hmeet : (C ∩ L).Nonempty
  · obtain ⟨x, hxC, hxL⟩ := hmeet
    have hnotR : x ∉ R := fun hxR =>
      Set.disjoint_left.mp hmiss hxC (hinter ⟨hxL, hxR⟩)
    have hdisjoint : Disjoint Rᶜ Lᶜ := Set.disjoint_left.mpr (by
      intro y hyR hyL
      have hy : y ∈ L ∪ R := by rw [hcover]; trivial
      exact hy.elim hyL hyR)
    have hCsides : C ⊆ Rᶜ ∪ Lᶜ := by
      intro y hyC
      by_cases hyR : y ∈ R
      · exact Or.inr (fun hyL => Set.disjoint_left.mp hmiss hyC (hinter ⟨hyL, hyR⟩))
      · exact Or.inl hyR
    have hCR : C ⊆ Rᶜ := hC.subset_left_of_subset_union
      hR.isOpen_compl hL.isOpen_compl hdisjoint hCsides ⟨x, hxC, hnotR⟩
    have hCL : C ⊆ L := by
      intro y hyC
      have hy : y ∈ L ∪ R := by rw [hcover]; trivial
      exact hy.resolve_right (hCR hyC)
    simpa only [inter_eq_left.mpr hCL] using hC
  · rw [Set.not_nonempty_iff_eq_empty.mp hmeet]
    exact isPreconnected_empty

/-- Passing to either half of a closed cover cannot split a local complementary
component when their overlap is removed. Applied to the two closed copies of
the double, this avoids assuming that a double chart is an original chart. -/
theorem finite_preimage_components_of_closed_cover {Y : Type*} [TopologicalSpace Y]
    {f : X → Y} (hf : IsClosedEmbedding f) (R G N : Set Y)
    (hR : IsClosed R) (hcover : range f ∪ R = univ) (hinter : range f ∩ R ⊆ G)
    [Finite (ConnectedComponents (N \ G : Set Y))] :
    Finite (ConnectedComponents (f ⁻¹' (N \ G))) := by
  let U := N \ G
  apply Components.finite_of_preconnected_cover _
    (fun a : ConnectedComponents U => f ⁻¹' componentSet U a)
  · intro a
    apply hf.isEmbedding.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_inter_range]
    exact preconnected_inter_closed_cover hf.isClosed_range hR hcover hinter
      (Components.isConnected U a).isPreconnected
      (Set.disjoint_left.mpr (fun y hy hyG => (Components.subset U a hy).2 hyG))
  · intro a
    exact preimage_mono (Components.subset U a)
  · intro x hx
    have hfx : f x ∈ ⋃ a : ConnectedComponents U, componentSet U a := by
      rw [Components.union_eq U]
      exact hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp hfx
    exact mem_iUnion.mpr ⟨a, ha⟩

/-- Finiteness of the actual complementary components on the original compact
surface follows directly from the arrangement's finite local normal forms.
This theorem does not assume the existence of an embedded graph, boundary
cycles or regions, and also covers empty and disconnected surfaces. -/
theorem finite_arrangement_components {kind : ModelKind} [CompactSpace X]
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B) :
    Finite (ConnectedComponents
      ((P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)ᶜ : Set X)) := by
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  let R := range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) (!s))
  have hf : IsClosedEmbedding f := D.copy_closedEmbedding s
  have hR : IsClosed R := (D.copy_closedEmbedding (!s)).isClosed_range
  have hcover : range f ∪ R = univ := by
    cases s
    · exact D.copies_cover
    · simpa only [f, R, Bool.not_true, union_comm] using D.copies_cover
  have hinter : range f ∩ R ⊆ arrangementCarrier T := by
    have heq : range f ∩ R = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S) := by
      cases s
      · exact D.copies_intersect
      · simpa only [f, R, Bool.not_true, inter_comm] using D.copies_intersect
    rw [heq, ← hB]
    exact subset_union_left
  apply Components.finite_of_finite_local_components
  intro x
  obtain ⟨F⟩ := T.normal_forms (f x) univ isOpen_univ (mem_univ _)
  let N := Arrangement.normalNeighborhood T F
  have hN : IsOpen N := Arrangement.isOpen_normalNeighborhood T F
  have hxN : f x ∈ N := Arrangement.mem_normalNeighborhood T F
  have hlocal : Finite (ConnectedComponents (N \ arrangementCarrier T : Set _)) :=
    Arrangement.finite_local_components T F
  let := hlocal
  have hpre := finite_preimage_components_of_closed_cover hf R
    (arrangementCarrier T) N hR hcover hinter
  refine ⟨f ⁻¹' N, (hN.preimage hf.continuous).mem_nhds hxN, ?_⟩
  have heq : (f ⁻¹' arrangementCarrier T)ᶜ ∩ f ⁻¹' N =
      f ⁻¹' (N \ arrangementCarrier T) := by
    ext y
    exact and_comm
  rw [heq]
  exact hpre

/-! The finite-interval route to cutting compact curves. These constructions use
actual chart maps, so their inverse-coordinate parametrizations can later be
transported through the smooth curve embeddings. No circle classification or
arbitrary topological circle parametrization is used. -/
namespace CurveCuts

/-- A compact interval strictly inside a real chart. Its two endpoints will be
marked before taking connected components of the punctured curve. -/
structure ChartInterval (X : Type u) [TopologicalSpace X]
    (A : Set (OpenPartialHomeomorph X ℝ)) where
  chart : OpenPartialHomeomorph X ℝ
  chart_mem : chart ∈ A
  lower : ℝ
  upper : ℝ
  lower_lt_upper : lower < upper
  interval_subset : Icc lower upper ⊆ chart.target

namespace ChartInterval
variable {A : Set (OpenPartialHomeomorph X ℝ)} (d : ChartInterval X A)

def inside : Set X := d.chart.source ∩ d.chart ⁻¹' Ioo d.lower d.upper

def carrier : Set X := d.chart.symm '' Icc d.lower d.upper

def endpoints : Set X := {d.chart.symm d.lower, d.chart.symm d.upper}

theorem isOpen_inside : IsOpen d.inside :=
  d.chart.isOpen_inter_preimage isOpen_Ioo

theorem isCompact_carrier : IsCompact d.carrier :=
  isCompact_Icc.image_of_continuousOn (d.chart.symm.continuousOn.mono d.interval_subset)

theorem carrier_subset_source : d.carrier ⊆ d.chart.source := by
  rintro x ⟨t, ht, rfl⟩
  exact d.chart.map_target (d.interval_subset ht)

theorem inside_subset_carrier : d.inside ⊆ d.carrier := by
  rintro x ⟨hx, ht⟩
  exact ⟨d.chart x, ⟨ht.1.le, ht.2.le⟩, d.chart.left_inv hx⟩

theorem closure_inside [T2Space X] : closure d.inside = d.carrier := by
  have hcl : closure d.inside ⊆ d.chart.source :=
    (closure_minimal d.inside_subset_carrier d.isCompact_carrier.isClosed).trans
      d.carrier_subset_source
  have hi : d.chart.IsImage d.inside (Ioo d.lower d.upper) := by
    intro x hx
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  have heq := hi.closure.symm_image_eq
  rw [closure_Ioo d.lower_lt_upper.ne, inter_eq_right.mpr d.interval_subset,
    inter_eq_right.mpr hcl] at heq
  exact heq.symm

theorem frontier_inside [T2Space X] : frontier d.inside = d.endpoints := by
  rw [frontier, d.closure_inside, d.isOpen_inside.interior_eq]
  apply Set.Subset.antisymm
  · rintro x ⟨⟨t, ht, rfl⟩, hout⟩
    have hsource := d.chart.map_target (d.interval_subset ht)
    have htend : t = d.lower ∨ t = d.upper := by
      by_contra h
      have hne := not_or.mp h
      apply hout
      refine ⟨hsource, ?_⟩
      change d.chart (d.chart.symm t) ∈ Ioo d.lower d.upper
      rw [d.chart.right_inv (d.interval_subset ht)]
      exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hne.1), lt_of_le_of_ne ht.2 hne.2⟩
    rcases htend with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (mem_singleton _)
  · intro x hx
    rcases hx with hx | hx
    · rw [hx]
      have ht := d.interval_subset (left_mem_Icc.mpr d.lower_lt_upper.le)
      refine ⟨⟨d.lower, left_mem_Icc.mpr d.lower_lt_upper.le, rfl⟩, ?_⟩
      intro h
      rw [inside, mem_inter_iff, mem_preimage, d.chart.right_inv ht] at h
      exact (lt_irrefl _ h.2.1)
    · have hx' := mem_singleton_iff.mp hx
      rw [hx']
      have ht := d.interval_subset (right_mem_Icc.mpr d.lower_lt_upper.le)
      refine ⟨⟨d.upper, right_mem_Icc.mpr d.lower_lt_upper.le, rfl⟩, ?_⟩
      intro h
      rw [inside, mem_inter_iff, mem_preimage, d.chart.right_inv ht] at h
      exact (lt_irrefl _ h.2.2)

theorem finite_endpoints : d.endpoints.Finite := by
  unfold endpoints
  exact Set.Finite.insert _ (Set.finite_singleton _)

end ChartInterval

/-- Compactness supplies the source's finite closed coordinate-interval cover.
The chosen charts remain members of the supplied atlas. Empty curves give a
possibly empty finite cover, without choosing a point of the curve. -/
theorem finite_chart_interval_cover [CompactSpace X]
    (A : Set (OpenPartialHomeomorph X ℝ))
    (hA : ∀ x : X, ∃ e ∈ A, x ∈ e.source) :
    ∃ (n : ℕ) (d : Fin n → ChartInterval X A), ⋃ i, (d i).inside = univ := by
  classical
  have hlocal : ∀ x : X, ∃ d : ChartInterval X A, x ∈ d.inside := by
    intro x
    obtain ⟨e, heA, hxe⟩ := hA x
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxe)
    let d : ChartInterval X A := {
      chart := e
      chart_mem := heA
      lower := e x - ε / 2
      upper := e x + ε / 2
      lower_lt_upper := by linarith
      interval_subset := by
        intro t ht
        apply hball
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2] }
    exact ⟨d, hxe, by change e x - ε / 2 < e x ∧ e x < e x + ε / 2; constructor <;> linarith⟩
  choose d hd using hlocal
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (d x).inside) (fun x => (d x).isOpen_inside)
    (by intro x _; exact mem_iUnion.mpr ⟨x, hd x⟩)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun i => d (e i).val, ?_⟩
  apply Set.Subset.antisymm (subset_univ _)
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hJ hx)
  exact mem_iUnion.mpr ⟨e.symm ⟨j, hj⟩, by simpa only [Equiv.apply_symm_apply] using hxj⟩

/-- Once the chart endpoints are marked, a connected component cannot leave
any chart interval that it meets. The closure stays in the same closed chart
interval. Extra prescribed finite marks can be included in `P`. -/
theorem component_in_chart_interval [T2Space X] {n : ℕ}
    {A : Set (OpenPartialHomeomorph X ℝ)} (d : Fin n → ChartInterval X A)
    (hcover : ⋃ i, (d i).inside = univ) (P : Set X)
    (hends : ∀ i, (d i).endpoints ⊆ P) (a : ConnectedComponents (Pᶜ : Set X)) :
    ∃ i, componentSet Pᶜ a ⊆ (d i).inside ∧
      closure (componentSet Pᶜ a) ⊆ (d i).carrier := by
  obtain ⟨x, hx⟩ := Components.nonempty Pᶜ a
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover ▸ mem_univ x)
  have hsub : componentSet Pᶜ a ⊆ (d i).inside :=
    subset_of_avoids_frontier (d i).isOpen_inside (Components.isConnected Pᶜ a).isPreconnected
      (Set.disjoint_left.mpr (fun y hy hfront => (Components.subset Pᶜ a hy)
        (hends i (by rwa [← (d i).frontier_inside])))) ⟨x, hx, hxi⟩
  refine ⟨i, hsub, ?_⟩
  rw [← (d i).closure_inside]
  exact closure_mono hsub


/-- An open connected subset with compact closure in one real chart is an
actual bounded open interval in that chart, with its exact closed interval as
closure. This retains the original chart, rather than an unspecified interval
homeomorphism. -/
theorem interval_coordinates [T2Space X]
    (e : OpenPartialHomeomorph X ℝ) (U : Set X)
    (hopen : IsOpen U) (hconn : IsConnected U) (hcompact : IsCompact (closure U))
    (hsource : closure U ⊆ e.source) :
    ∃ a b : ℝ, a < b ∧ Icc a b ⊆ e.target ∧
      e '' U = Ioo a b ∧ e '' closure U = Icc a b := by
  let V := e '' U
  have hUs : U ⊆ e.source := subset_closure.trans hsource
  have hVo : IsOpen V := e.isOpen_image_of_subset_source hopen hUs
  have hVc : IsConnected V := hconn.image e (e.continuousOn.mono hUs)
  have hKc : IsCompact (e '' closure U) :=
    hcompact.image_of_continuousOn (e.continuousOn.mono hsource)
  have hVK : V ⊆ e '' closure U := image_mono subset_closure
  have hclVK : closure V ⊆ e '' closure U := closure_minimal hVK hKc.isClosed
  have hKt : e '' closure U ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hsource hx)
  have hi : e.IsImage U V := by
    intro x hx
    constructor
    · rintro ⟨y, hy, heq⟩
      have hyx : y = x := e.injOn (hUs hy) hx heq
      exact hyx ▸ hy
    · intro hxU
      exact ⟨x, hxU, rfl⟩
  have hcl : e '' closure U = closure V := by
    have heq := hi.closure.image_eq
    rwa [inter_eq_right.mpr hsource, inter_eq_right.mpr (hclVK.trans hKt)] at heq
  have hb : BddBelow V := hKc.bddBelow.mono hVK
  have ha : BddAbove V := hKc.bddAbove.mono hVK
  have hVint : V ⊆ Ioo (sInf V) (sSup V) := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVo x hx
    have hleft : x - ε / 2 ∈ V := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hright : x + ε / 2 ∈ V := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact ⟨csInf_lt_of_lt hb hleft (by linarith),
      lt_csSup_of_lt ha hright (by linarith)⟩
  have hV : V = Ioo (sInf V) (sSup V) :=
    hVint.antisymm (hVc.Ioo_csInf_csSup_subset hb ha)
  obtain ⟨x, hx⟩ := hVc.nonempty
  have hab : sInf V < sSup V := (hVint hx).1.trans (hVint hx).2
  have hclosed : e '' closure U = Icc (sInf V) (sSup V) := by
    calc
      e '' closure U = closure V := hcl
      _ = closure (Ioo (sInf V) (sSup V)) := congrArg closure hV
      _ = Icc (sInf V) (sSup V) := closure_Ioo hab.ne
  refine ⟨sInf V, sSup V, hab, ?_, hV, hclosed⟩
  rw [← hclosed]
  exact hKt

/-- Inverse-chart affine parametrization of a closed interval. Its formula is
retained so derivative and endpoint-germ proofs can use the smooth chart. -/
def intervalMap (e : OpenPartialHomeomorph X ℝ) (a b : ℝ) (hab : a < b)
    (htarget : Icc a b ⊆ e.target) : C(unitInterval, X) :=
  ⟨fun t => e.symm ((b - a) * (t : ℝ) + a), by
    have hI : ∀ t : unitInterval, (b - a) * (t : ℝ) + a ∈ e.target := by
      intro t
      exact htarget ((iccHomeoI a b hab).symm t).property
    exact e.symm.continuousOn.comp_continuous
      (by fun_prop) hI⟩

@[simp] theorem intervalMap_zero (e : OpenPartialHomeomorph X ℝ)
    (a b : ℝ) (hab : a < b) (htarget : Icc a b ⊆ e.target) :
    intervalMap e a b hab htarget 0 = e.symm a := by
  simp [intervalMap]

@[simp] theorem intervalMap_one (e : OpenPartialHomeomorph X ℝ)
    (a b : ℝ) (hab : a < b) (htarget : Icc a b ⊆ e.target) :
    intervalMap e a b hab htarget 1 = e.symm b := by
  simp [intervalMap]

theorem intervalMap_coordinates (e : OpenPartialHomeomorph X ℝ)
    (a b : ℝ) (hab : a < b) (htarget : Icc a b ⊆ e.target) (t : unitInterval) :
    e (intervalMap e a b hab htarget t) = (b - a) * (t : ℝ) + a :=
  e.right_inv (htarget ((iccHomeoI a b hab).symm t).property)

theorem intervalMap_injective (e : OpenPartialHomeomorph X ℝ)
    (a b : ℝ) (hab : a < b) (htarget : Icc a b ⊆ e.target) :
    Function.Injective (intervalMap e a b hab htarget) := by
  intro t q h
  have heq := congrArg e h
  rw [intervalMap_coordinates, intervalMap_coordinates] at heq
  apply Subtype.ext
  exact mul_left_cancel₀ (sub_pos.mpr hab).ne' (add_right_cancel heq)

theorem intervalMap_range (e : OpenPartialHomeomorph X ℝ)
    (a b : ℝ) (hab : a < b) (htarget : Icc a b ⊆ e.target) :
    range (intervalMap e a b hab htarget) = e.symm '' Icc a b := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact ⟨((iccHomeoI a b hab).symm t).val,
      ((iccHomeoI a b hab).symm t).property, rfl⟩
  · rintro x ⟨r, hr, rfl⟩
    refine ⟨iccHomeoI a b hab ⟨r, hr⟩, ?_⟩
    change e.symm (((iccHomeoI a b hab).symm (iccHomeoI a b hab ⟨r, hr⟩)).val) = _
    rw [Homeomorph.symm_apply_apply]

theorem intervalMap_open_image (e : OpenPartialHomeomorph X ℝ)
    (a b : ℝ) (hab : a < b) (htarget : Icc a b ⊆ e.target) :
    intervalMap e a b hab htarget '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} =
      e.symm '' Ioo a b := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, ht, rfl⟩
    refine ⟨(b - a) * (t : ℝ) + a, ?_, rfl⟩
    constructor <;> nlinarith [sub_pos.mpr hab, ht.1, ht.2]
  · rintro x ⟨r, hr, rfl⟩
    have hr' : r ∈ Icc a b := ⟨hr.1.le, hr.2.le⟩
    let t := iccHomeoI a b hab ⟨r, hr'⟩
    have ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
      change 0 < (r - a) / (b - a) ∧ (r - a) / (b - a) < 1
      exact ⟨div_pos (sub_pos.mpr hr.1) (sub_pos.mpr hab),
        (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [hr.2])⟩
    refine ⟨t, ht, ?_⟩
    change e.symm (((iccHomeoI a b hab).symm (iccHomeoI a b hab ⟨r, hr'⟩)).val) = _
    rw [Homeomorph.symm_apply_apply]

/-- Every actual punctured-curve component whose closure stays in a chart has
a compact interval map, injective including the endpoints. Its open image is
exactly that component and its endpoint images are actual marked points. -/
theorem component_interval_map [T2Space X] [CompactSpace X] [LocallyConnectedSpace X]
    (P : Set X) (hP : IsClosed P) (a : ConnectedComponents (Pᶜ : Set X))
    (e : OpenPartialHomeomorph X ℝ)
    (hsource : closure (componentSet Pᶜ a) ⊆ e.source) :
    ∃ c : C(unitInterval, X), Function.Injective c ∧
      range c = closure (componentSet Pᶜ a) ∧
      c '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} = componentSet Pᶜ a ∧
      c 0 ∈ P ∧ c 1 ∈ P ∧
      ∃ l r : ℝ, l < r ∧ ∀ t : unitInterval, e (c t) = (r - l) * (t : ℝ) + l := by
  let U := componentSet Pᶜ a
  have hUo : IsOpen U := Components.isOpen _ hP.isOpen_compl a
  obtain ⟨l, r, hlr, htarget, hU, hclU⟩ := interval_coordinates e U hUo
    (Components.isConnected _ a) isClosed_closure.isCompact hsource
  have hU' : e.symm '' Ioo l r = U := by
    rw [← hU]
    exact e.symm_image_image_of_subset_source (subset_closure.trans hsource)
  have hclU' : e.symm '' Icc l r = closure U := by
    rw [← hclU]
    exact e.symm_image_image_of_subset_source hsource
  let c := intervalMap e l r hlr htarget
  have hcopen : c '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} = U := by
    rw [intervalMap_open_image, hU']
  have hcrange : range c = closure U := by rw [intervalMap_range, hclU']
  have hends : ∀ t : unitInterval, t = 0 ∨ t = 1 → c t ∈ P := by
    intro t ht
    have hcl : c t ∈ closure U := hcrange ▸ mem_range_self t
    by_contra hnot
    have htU : c t ∈ U := by
      change c t ∈ componentSet Pᶜ a
      rw [← Components.closure_inter Pᶜ a]
      exact ⟨hcl, hnot⟩
    obtain ⟨q, hq, hqt⟩ := hcopen ▸ htU
    have hqt' : q = t := intervalMap_injective e l r hlr htarget hqt
    rcases ht with rfl | rfl
    · have hzero : (q : ℝ) = 0 := congrArg Subtype.val hqt'
      exact (lt_irrefl (0 : ℝ)) (hzero ▸ hq.1)
    · have hone : (q : ℝ) = 1 := congrArg Subtype.val hqt'
      exact (lt_irrefl (1 : ℝ)) (hone ▸ hq.2)
  exact ⟨c, intervalMap_injective e l r hlr htarget, hcrange, hcopen,
    hends 0 (Or.inl rfl), hends 1 (Or.inr rfl), l, r, hlr,
    intervalMap_coordinates e l r hlr htarget⟩


/-- One genuine compact interval cut, with its atlas label and affine chart
formula. Smoothness is deliberately not inferred merely from continuity. -/
structure ComponentInterval (A : Set (OpenPartialHomeomorph X ℝ))
    (P : Set X) (a : ConnectedComponents (Pᶜ : Set X)) where
  chart : OpenPartialHomeomorph X ℝ
  chart_mem : chart ∈ A
  closure_source : closure (componentSet Pᶜ a) ⊆ chart.source
  map : C(unitInterval, X)
  injective : Function.Injective map
  range_eq : range map = closure (componentSet Pᶜ a)
  open_image : map '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} = componentSet Pᶜ a
  initial_mark : map 0 ∈ P
  terminal_mark : map 1 ∈ P
  lower : ℝ
  upper : ℝ
  lower_lt_upper : lower < upper
  coordinate_formula : ∀ t : unitInterval, chart (map t) = (upper - lower) * (t : ℝ) + lower

/-- Chart labels and the two marked endpoints determine each actual component.
This proves finiteness without assuming it in order to index the cuts. -/
theorem finite_components_of_interval_cuts
    {A : Set (OpenPartialHomeomorph X ℝ)} (hA : A.Finite)
    {P : Set X} (hP : P.Finite)
    (c : ∀ a : ConnectedComponents (Pᶜ : Set X), ComponentInterval A P a) :
    Finite (ConnectedComponents (Pᶜ : Set X)) := by
  classical
  let := hA.fintype
  let := hP.fintype
  let f : ConnectedComponents (Pᶜ : Set X) → A × P × P := fun a =>
    (⟨(c a).chart, (c a).chart_mem⟩,
      ⟨(c a).map 0, (c a).initial_mark⟩, ⟨(c a).map 1, (c a).terminal_mark⟩)
  apply Finite.of_injective f
  intro a b hab
  have he : (c a).chart = (c b).chart := congrArg (fun x => x.1.val) hab
  have h0 : (c a).map 0 = (c b).map 0 := congrArg (fun x => x.2.1.val) hab
  have h1 : (c a).map 1 = (c b).map 1 := congrArg (fun x => x.2.2.val) hab
  have hl : (c a).lower = (c b).lower := by
    have h := congrArg (c b).chart h0
    rw [← he, (c a).coordinate_formula, he, (c b).coordinate_formula] at h
    simpa using h
  have hr : (c a).upper = (c b).upper := by
    have h := congrArg (c b).chart h1
    rw [← he, (c a).coordinate_formula, he, (c b).coordinate_formula] at h
    simpa using h
  let t : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1 := by norm_num [t]
  have hmaps : (c a).map t = (c b).map t := by
    apply (c a).chart.injOn
    · exact (c a).closure_source ((c a).range_eq ▸ mem_range_self t)
    · rw [he]
      exact (c b).closure_source ((c b).range_eq ▸ mem_range_self t)
    · rw [(c a).coordinate_formula, he, (c b).coordinate_formula, hl, hr]
  by_contra hne
  have hxa : (c a).map t ∈ componentSet Pᶜ a := by
    rw [← (c a).open_image]
    exact ⟨t, ht, rfl⟩
  have hxb : (c a).map t ∈ componentSet Pᶜ b := by
    rw [hmaps, ← (c b).open_image]
    exact ⟨t, ht, rfl⟩
  exact Set.disjoint_left.mp (Components.disjoint Pᶜ a b hne) hxa hxb

/-- Finite actual interval cuts of a compact curve, relative to a supplied real
atlas and any prescribed finite set of cuts. The extra marks are precisely
endpoints of finitely many chart intervals. No component classification,
orientability or nonemptiness hypothesis occurs. -/
theorem finite_interval_cutting [T2Space X] [CompactSpace X] [LocallyConnectedSpace X]
    (A : Set (OpenPartialHomeomorph X ℝ))
    (hA : ∀ x : X, ∃ e ∈ A, x ∈ e.source) (Q : Set X) (hQ : Q.Finite) :
    ∃ P : Set X, P.Finite ∧ Q ⊆ P ∧
      Finite (ConnectedComponents (Pᶜ : Set X)) ∧
      Nonempty (∀ a : ConnectedComponents (Pᶜ : Set X), ComponentInterval A P a) := by
  classical
  obtain ⟨n, d, hcover⟩ := finite_chart_interval_cover A hA
  let P : Set X := Q ∪ ⋃ i, (d i).endpoints
  have hP : P.Finite := hQ.union (Set.finite_iUnion fun i => (d i).finite_endpoints)
  have hends : ∀ i, (d i).endpoints ⊆ P := by
    intro i x hx
    exact Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
  let A' : Set (OpenPartialHomeomorph X ℝ) := range (fun i => (d i).chart)
  have hcuts : ∀ a : ConnectedComponents (Pᶜ : Set X), Nonempty (ComponentInterval A' P a) := by
    intro a
    obtain ⟨i, _, hcl⟩ := component_in_chart_interval d hcover P hends a
    have hs := hcl.trans (d i).carrier_subset_source
    obtain ⟨c, hci, hcr, hco, hc0, hc1, l, r, hlr, hformula⟩ :=
      component_interval_map P hP.isClosed a (d i).chart hs
    exact ⟨{
      chart := (d i).chart
      chart_mem := mem_range_self i
      closure_source := hs
      map := c
      injective := hci
      range_eq := hcr
      open_image := hco
      initial_mark := hc0
      terminal_mark := hc1
      lower := l
      upper := r
      lower_lt_upper := hlr
      coordinate_formula := hformula }⟩
  let c := fun a => (hcuts a).some
  have hfin : Finite (ConnectedComponents (Pᶜ : Set X)) :=
    finite_components_of_interval_cuts (Set.finite_range _) hP c
  refine ⟨P, hP, subset_union_left, hfin, ?_⟩
  have hsub : A' ⊆ A := by
    rintro e ⟨i, rfl⟩
    exact (d i).chart_mem
  exact ⟨fun a => { c a with chart_mem := hsub (c a).chart_mem }⟩

/-- The actual one-dimensional Euclidean model is the real line. -/
def realModel : ModelSpace 1 .euclidean ≃ₜ ℝ :=
  (Homeomorph.Set.univ (Euclidean 1)).trans (Homeomorph.funUnique (Fin 1) ℝ)

def realChart (e : ModelChart 1 .euclidean X) : OpenPartialHomeomorph X ℝ :=
  e.transHomeomorph realModel

/-- Specialization to the actual atlas of a compact smooth boundaryless curve.
The chart labels are retained for the subsequent smoothness and regularity
bridges; a bare homeomorphism to a circle would lose that information. -/
theorem smooth_curve_interval_cutting [CompactSpace X]
    (S : SmoothManifold 1 .euclidean X) (Q : Set X) (hQ : Q.Finite) :
    ∃ P : Set X, P.Finite ∧ Q ⊆ P ∧
      Finite (ConnectedComponents (Pᶜ : Set X)) ∧
      Nonempty (∀ a : ConnectedComponents (Pᶜ : Set X),
        ComponentInterval (realChart '' S.smoothStructure.val) P a) := by
  let := S.topologicalManifold.hausdorff
  let := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  apply finite_interval_cutting _ _ Q hQ
  intro x
  obtain ⟨e, he, hx⟩ := S.smoothStructure.property.1.1 x
  exact ⟨realChart e, mem_image_of_mem realChart he, hx⟩


/-- The affine atlas formula of a cut gives genuine smooth regular germs after
any smooth immersion into a surface. This includes both endpoints: the ambient
extension is defined on a real neighborhood, not merely on the parameter
interval. No smoothness is attributed to a chosen circle homeomorphism. -/
theorem ComponentInterval.regular_image_germs
    {Y : Type*} [TopologicalSpace Y] {kind : ModelKind}
    (S : SmoothManifold 1 .euclidean X) (W : SmoothManifold 2 kind Y)
    (f : X → Y) (hf : SmoothManifolds.MapData.IsSmoothMap S W f)
    (himm : SmoothManifolds.MapClassData.IsImmersion S W f)
    {P : Set X} {a : ConnectedComponents (Pᶜ : Set X)}
    (c : ComponentInterval (realChart '' S.smoothStructure.val) P a)
    (t : unitInterval) (d : ModelChart 2 kind Y) (hd : d ∈ W.smoothStructure.val)
    (htd : f (c.map t) ∈ d.source) :
    ∃ (δ : ℝ) (F : ℝ → Plane), 0 < δ ∧
      ContDiffOn ℝ ∞ F (Ioo ((t : ℝ) - δ) ((t : ℝ) + δ)) ∧
      deriv F (t : ℝ) ≠ 0 ∧
      ∀ q : unitInterval, |(q : ℝ) - (t : ℝ)| < δ →
        f (c.map q) ∈ d.source ∧ F (q : ℝ) = coordinates d (f (c.map q)) := by
  classical
  obtain ⟨e, he, hec⟩ := c.chart_mem
  have hce : c.chart = realChart e := hec.symm
  have hsource : ∀ q : unitInterval, c.map q ∈ e.source := by
    intro q
    have h := c.closure_source (c.range_eq ▸ mem_range_self q)
    rwa [hce] at h
  let H : ℝ → Euclidean 1 := fun s _ => (c.upper - c.lower) * s + c.lower
  let v : Euclidean 1 := fun _ => c.upper - c.lower
  have hcoord : ∀ q : unitInterval, (e (c.map q)).val = H (q : ℝ) := by
    intro q
    funext i
    have h := c.coordinate_formula q
    rw [hce] at h
    change (e (c.map q)).val default = _ at h
    simpa only [Subsingleton.elim i default] using h
  have hH : ContDiff ℝ ∞ H :=
    contDiff_pi.mpr fun _ => (contDiff_const.mul contDiff_id).add contDiff_const
  have hHd : HasDerivAt H v (t : ℝ) := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa [H, v] using (((hasDerivAt_id (t : ℝ)).const_mul
      (c.upper - c.lower)).add_const c.lower)
  obtain ⟨U, hU, hpU, g, hg, heq⟩ := (hf (c.map t)).2 e he d hd (hsource t) htd
  have hgd := ((hg.contDiffAt (hU.mem_nhds hpU)).differentiableAt
    (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hJ : SmoothManifolds.FiniteRegularityData.chartDerivative e d f (c.map t) =
      fderiv ℝ g (e (c.map t)).val :=
    SmoothManifolds.FiniteRegularity.coordinateDerivative_eq e _ (c.map t) (hsource t) _
      ⟨g, hgd, heq⟩
  have hf1 := SmoothManifolds.manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf
  have hgi : Function.Injective (fderiv ℝ g (e (c.map t)).val) := by
    rw [← hJ]
    exact ((SmoothManifolds.MapClasses.chart_invariants S W f hf1 (c.map t)
      e d he hd (hsource t) htd).2.1).mp (himm (c.map t))
  let F : ℝ → Plane := fun s => toPlane (g (H s))
  have hFt : HasDerivAt F (toPlane ((fderiv ℝ g (e (c.map t)).val) v)) (t : ℝ) := by
    have hgH := hgd.comp_hasDerivAt_of_eq (t : ℝ) hHd (hcoord t)
    exact toPlane.hasFDerivAt.comp_hasDerivAt (t : ℝ) hgH
  have hFne : deriv F (t : ℝ) ≠ 0 := by
    rw [hFt.deriv]
    intro hzero
    have hJzero : (fderiv ℝ g (e (c.map t)).val) v = 0 :=
      toPlane.injective (by simpa only [map_zero] using hzero)
    have hvzero : v = 0 := hgi (by simpa only [map_zero] using hJzero)
    have h := congrFun hvzero 0
    exact (sub_pos.mpr c.lower_lt_upper).ne' h
  have hF : ContDiffOn ℝ ∞ F (H ⁻¹' U) :=
    toPlane.contDiff.comp_contDiffOn (hg.comp hH.contDiffOn (fun _ hx => hx))
  have hV : IsOpen (H ⁻¹' U) := hU.preimage hH.continuous
  have htV : (t : ℝ) ∈ H ⁻¹' U := by
    change H (t : ℝ) ∈ U
    rwa [← hcoord]
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.mp hV (t : ℝ) htV
  have heqc := c.map.continuous.continuousAt.eventually heq
  have hdc : ∀ᶠ q in 𝓝 t, f (c.map q) ∈ d.source :=
    ((hf (c.map t)).1.comp c.map.continuous.continuousAt).eventually
      (d.open_source.mem_nhds htd)
  obtain ⟨δ₂, hδ₂, hnear⟩ := Metric.mem_nhds_iff.mp (heqc.and hdc)
  refine ⟨min δ₁ δ₂, F, lt_min hδ₁ hδ₂, hF.mono ?_, hFne, ?_⟩
  · intro s hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left δ₁ δ₂, hs.1, hs.2]
  · intro q hq
    have hqt : dist q t < δ₂ := by
      rw [Subtype.dist_eq, Real.dist_eq]
      exact hq.trans_le (min_le_right δ₁ δ₂)
    obtain ⟨hEq, hdq⟩ := hnear hqt
    refine ⟨hdq, ?_⟩
    change toPlane (g (H (q : ℝ))) = toPlane (d (f (c.map q))).val
    change g (e (c.map q)).val = (d (f (c.map q))).val at hEq
    rw [← hcoord, hEq]


/-- Composition of a cut with the actual smooth curve inclusion. -/
def ComponentInterval.imageMap
    {Y : Type*} [TopologicalSpace Y] {A : Set (OpenPartialHomeomorph X ℝ)}
    {P : Set X} {a : ConnectedComponents (Pᶜ : Set X)}
    (c : ComponentInterval A P a) (f : C(X, Y)) : C(unitInterval, Y) :=
  f.comp c.map

theorem ComponentInterval.imageMap_regular
    {Y : Type*} [TopologicalSpace Y] {kind : ModelKind}
    (S : SmoothManifold 1 .euclidean X) (W : SmoothManifold 2 kind Y)
    (f : X → Y) (hf : SmoothManifolds.MapData.IsSmoothMap S W f)
    (himm : SmoothManifolds.MapClassData.IsImmersion S W f)
    {P : Set X} {a : ConnectedComponents (Pᶜ : Set X)}
    (c : ComponentInterval (realChart '' S.smoothStructure.val) P a) :
    RegularOpenEdge W
      (c.imageMap ⟨f, continuous_iff_continuousAt.mpr fun x => (hf x).1⟩) ∧
    RegularEdgeEndpoints W
      (c.imageMap ⟨f, continuous_iff_continuousAt.mpr fun x => (hf x).1⟩) := by
  let C := c.imageMap ⟨f, continuous_iff_continuousAt.mpr fun x => (hf x).1⟩
  constructor
  · intro t ht
    let q : unitInterval := ⟨t, ht.1.le, ht.2.le⟩
    obtain ⟨d, hd, hqd⟩ := W.smoothStructure.property.1.1 (f (c.map q))
    obtain ⟨δ, F, hδ, hF, hFn, heq⟩ := c.regular_image_germs S W f hf himm q d hd hqd
    refine ⟨d, hd, hqd, ?_⟩
    have hFq : ContDiffAt ℝ ∞ F t :=
      hF.contDiffAt (isOpen_Ioo.mem_nhds (by change t - δ < t ∧ t < t + δ; constructor <;> linarith))
    have hnear : (fun s => coordinates d (IccExtend zero_le_one C s)) =ᶠ[𝓝 t] F := by
      have hball : Metric.ball t δ ∈ 𝓝 t := Metric.ball_mem_nhds t hδ
      filter_upwards [isOpen_Ioo.mem_nhds ht, hball] with s hs hst
      rw [IccExtend_of_mem _ _ ⟨hs.1.le, hs.2.le⟩]
      exact (heq ⟨s, hs.1.le, hs.2.le⟩ (by
        change |s - t| < δ
        simpa only [Metric.mem_ball, Real.dist_eq] using hst)).2.symm
    exact ⟨hFq.congr_of_eventuallyEq hnear, by rw [hnear.deriv_eq]; exact hFn⟩
  · intro t _ d hd htd
    exact c.regular_image_germs S W f hf himm t d hd htd

end CurveCuts

variable {X : Type u} [TopologicalSpace X]

/-- The entire compact edge is the closure of its open edge image, even for a loop. -/
theorem closure_open_edge_image [T2Space X] (c : C(unitInterval, X)) :
    closure (c '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}) = range c := by
  have hcl : closure ({t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} : Set unitInterval) = univ := by
    change closure (Ioo (0 : unitInterval) 1) = univ
    rw [closure_Ioo (by intro h; have h' := congrArg Subtype.val h; norm_num at h')]
    ext t
    simp only [mem_Icc, mem_univ, iff_true]
    exact t.property
  apply Subset.antisymm
  · exact closure_minimal (image_subset_range _ _) (isCompact_range c.continuous).isClosed
  · rw [← image_univ, ← hcl]
    exact image_closure_subset_closure_image c.continuous

/-- In a closed two-piece cover a connected set avoiding the overlap lies
wholly in any side it meets. This is the topological step used to restrict
cut circle arcs from the double to the original surface. -/
theorem preconnected_subset_closed_side {L R C : Set X}
    (hL : IsClosed L) (hR : IsClosed R) (hcover : L ∪ R = univ)
    (hC : IsPreconnected C) (hmiss : Disjoint C (L ∩ R))
    (hmeet : (C ∩ L).Nonempty) : C ⊆ L := by
  obtain ⟨x, hxC, hxL⟩ := hmeet
  have hxR : x ∉ R := fun hxR => Set.disjoint_left.mp hmiss hxC ⟨hxL, hxR⟩
  have hsides : C ⊆ Rᶜ ∪ Lᶜ := by
    intro y hyC
    by_cases hyR : y ∈ R
    · exact Or.inr fun hyL => Set.disjoint_left.mp hmiss hyC ⟨hyL, hyR⟩
    · exact Or.inl hyR
  have hdisjoint : Disjoint Rᶜ Lᶜ := Set.disjoint_left.mpr (by
    intro y hyR hyL
    have hy : y ∈ L ∪ R := by rw [hcover]; trivial
    exact hy.elim hyL hyR)
  have hCR : C ⊆ Rᶜ := hC.subset_left_of_subset_union
    hR.isOpen_compl hL.isOpen_compl hdisjoint hsides ⟨x, hxC, hxR⟩
  intro y hyC
  have hy : y ∈ L ∪ R := by rw [hcover]; trivial
  exact hy.resolve_right (hCR hyC)

/-- An arc whose open part misses the seam cannot enter and leave one closed
copy. If its open part meets that copy, its endpoints also lie in that copy. -/
theorem edge_range_subset_closed_side [T2Space X] (c : C(unitInterval, X))
    {L R : Set X} (hL : IsClosed L) (hR : IsClosed R) (hcover : L ∪ R = univ)
    (hmiss : Disjoint
      (c '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}) (L ∩ R))
    (hmeet : ((c '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}) ∩ L).Nonempty) :
    range c ⊆ L := by
  rw [← closure_open_edge_image c]
  apply closure_minimal _ hL
  apply preconnected_subset_closed_side hL hR hcover _ hmiss hmeet
  change IsPreconnected (c '' Ioo (0 : unitInterval) 1)
  exact isPreconnected_Ioo.image c c.continuous.continuousOn



/-- The unconstrained first coordinate is surjective for both surface models. -/
theorem model_first_coordinate_surjective (kind : ModelKind) :
    Function.Surjective (fun z : ModelSpace 2 kind => z.val (0 : Fin 2)) := by
  intro t
  refine ⟨⟨fun i => if i = 0 then t else 0, ?_⟩, by simp⟩
  cases kind <;> simp [modelSet, halfSpaceSet]

/-- Neither of the two surface models is compact. -/
theorem model_noncompact (kind : ModelKind) : NoncompactSpace (ModelSpace 2 kind) := by
  apply not_compactSpace_iff.mp
  intro hc
  let := hc
  have hreal : IsCompact (univ : Set ℝ) := by
    have hf : Continuous (fun z : ModelSpace 2 kind => z.val (0 : Fin 2)) :=
      (continuous_apply (0 : Fin 2)).comp continuous_subtype_val
    have hi : (fun z : ModelSpace 2 kind => z.val (0 : Fin 2)) '' univ = univ :=
      Set.image_univ_of_surjective (model_first_coordinate_surjective kind)
    rw [← hi]
    exact isCompact_univ.image hf
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ))
    (isCompact_univ_iff.mp hreal)

/-- A nonempty open set with compact closure in one surface chart has a
nonempty ambient frontier, including for charts into a half-space. -/
theorem frontier_nonempty_in_surface_chart
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {kind : ModelKind} (e : ModelChart 2 kind X) {C : Set X}
    (hC : C.Nonempty) (hopen : IsOpen C) (hsource : closure C ⊆ e.source) :
    (frontier C).Nonempty := by
  let : T2Space (ModelSpace 2 kind) := inferInstance
  let : PreconnectedSpace (ModelSpace 2 kind) :=
    isPreconnected_iff_preconnectedSpace.mp (SmoothManifolds.convex_modelSet 2 kind).isPreconnected
  let : NoncompactSpace (ModelSpace 2 kind) := model_noncompact kind
  by_contra hfront
  have hclopen : IsClopen C := isClopen_iff_frontier_eq_empty.mpr
    (Set.not_nonempty_iff_eq_empty.mp hfront)
  have hcomp : IsCompact (e '' C) := hclopen.isClosed.isCompact.image_of_continuousOn
    (e.continuousOn.mono (subset_closure.trans hsource))
  have himageopen : IsOpen (e '' C) :=
    e.isOpen_image_of_subset_source hopen (subset_closure.trans hsource)
  have heq : e '' C = univ := (IsClopen.eq_univ ⟨hcomp.isClosed, himageopen⟩ (hC.image e))
  rw [heq] at hcomp
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace (ModelSpace 2 kind)))
    (isCompact_univ_iff.mp hcomp)

/-- Every actual complementary region of the restricted arrangement has a
nonempty boundary; this is established before graph cutting or planar-region
construction, without a connectedness or orientation hypothesis on the surface. -/
theorem arrangement_component_frontier_nonempty {X : Type u} [TopologicalSpace X]
    {kind : ModelKind} [CompactSpace X]
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    (hsubordinate : CopySubordinate S D s A)
    {B : CompactSmoothSeam D.manifold}
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (a : ConnectedComponents
      ((P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)ᶜ : Set X)) :
    (frontier (componentSet
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)ᶜ a)).Nonempty := by
  let := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  let G := f ⁻¹' arrangementCarrier T
  have hG : IsClosed G := (Arrangement.isClosed_carrier T).preimage
    (D.copy_closedEmbedding s).continuous
  obtain ⟨i, e, he, hi, hc, hsource⟩ :=
    arrangement_component_in_original_chart S D s hsubordinate T a
  exact frontier_nonempty_in_surface_chart e (Components.nonempty Gᶜ a)
    (Components.isOpen Gᶜ hG.isOpen_compl a) hsource

/-- In particular a component closure meets the actual curve arrangement. -/
theorem arrangement_component_closure_meets_carrier {X : Type u} [TopologicalSpace X]
    {kind : ModelKind} [CompactSpace X]
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    (hsubordinate : CopySubordinate S D s A)
    {B : CompactSmoothSeam D.manifold}
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (a : ConnectedComponents
      ((P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)ᶜ : Set X)) :
    (closure (componentSet
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)ᶜ a) ∩
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)).Nonempty := by
  let := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  have hG := (Arrangement.isClosed_carrier T).preimage
    (D.copy_closedEmbedding s).continuous
  rw [← Components.frontier_eq _ hG a]
  exact arrangement_component_frontier_nonempty S D s hsubordinate T a


theorem embeddedGraph_of_finite_edges {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (V : Set X) (hV : V.Finite)
    {E : Type v} [Finite E] (c : E → C(unitInterval, X))
    (h0 : ∀ e, c e 0 ∈ V) (h1 : ∀ e, c e 1 ∈ V)
    (hinj : ∀ e, Set.InjOn (c e) {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1})
    (havoid : ∀ e (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → c e t ∉ V)
    (hdisj : Pairwise (fun i j => Disjoint
      (c i '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1})
      (c j '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1})))
    (hreg : ∀ e, RegularOpenEdge S (c e)) :
    ∃ G : EmbeddedGraph S, range G.vertex = V ∧ G.carrier = V ∪ ⋃ e, range (c e) ∧
      (∀ i, ∃ e, G.edge i = c e) ∧ (∀ e, ∃ i, G.edge i = c e) := by
  classical
  let := hV.fintype
  let := Fintype.ofFinite E
  let ev : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let ee : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  let vertex : Fin (Fintype.card V) → X := fun i => (ev i).val
  have hvrange : range vertex = V := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (ev i).property
    · intro hx
      exact ⟨ev.symm ⟨x,hx⟩, by simp [vertex]⟩
  let G : EmbeddedGraph S := {
    vertexCount := Fintype.card V
    edgeCount := Fintype.card E
    vertex := vertex
    vertex_injective := Subtype.val_injective.comp ev.injective
    edge := fun i => c (ee i)
    initial := fun i => ev.symm ⟨c (ee i) 0, h0 (ee i)⟩
    terminal := fun i => ev.symm ⟨c (ee i) 1, h1 (ee i)⟩
    at_zero := by intro i; simp [vertex]
    at_one := by intro i; simp [vertex]
    open_injective := fun i => hinj (ee i)
    avoids_vertices := by intro i t ht ht'; rw [hvrange]; exact havoid (ee i) t ht ht'
    disjoint_open_edges := fun i j hij => hdisj (ee.injective.ne hij)
    regular := fun i => hreg (ee i) }
  refine ⟨G, hvrange, ?_, ?_, ?_⟩
  · change range vertex ∪ ⋃ i, range (c (ee i)) = _
    rw [hvrange]
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨ee i,hi⟩
    · intro hx
      obtain ⟨e,he⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨ee.symm e, by simpa using he⟩
  · intro i; exact ⟨ee i,rfl⟩
  · intro e; exact ⟨ee.symm e, by simp [G]⟩

variable {X : Type u} [TopologicalSpace X]

/-- Smooth regular ambient coordinate extensions at every parameter, retaining
the endpoint information required when pulling arcs back from the double. -/
def RegularCoordinateGerms {kind : ModelKind} (S : SmoothManifold 2 kind X)
    (c : C(unitInterval, X)) : Prop :=
  ∀ t : unitInterval, ∀ e ∈ S.smoothStructure.val, c t ∈ e.source →
    ∃ (δ : ℝ) (F : ℝ → Plane), 0 < δ ∧
      ContDiffOn ℝ ∞ F (Ioo ((t : ℝ) - δ) ((t : ℝ) + δ)) ∧
      deriv F (t : ℝ) ≠ 0 ∧
      ∀ q : unitInterval, |(q : ℝ) - (t : ℝ)| < δ →
        c q ∈ e.source ∧ F (q : ℝ) = coordinates e (c q)

/-- Actual coordinate extensions imply both the open-edge and endpoint
regularity predicates; clamping is used only away from its endpoints. -/
theorem RegularCoordinateGerms.regular {kind : ModelKind}
    {S : SmoothManifold 2 kind X} {c : C(unitInterval, X)}
    (h : RegularCoordinateGerms S c) :
    RegularOpenEdge S c ∧ RegularEdgeEndpoints S c := by
  constructor
  · intro t ht
    let q : unitInterval := ⟨t, ht.1.le, ht.2.le⟩
    obtain ⟨e, he, hqe⟩ := S.smoothStructure.property.1.1 (c q)
    obtain ⟨δ, F, hδ, hF, hFn, heq⟩ := h q e he hqe
    refine ⟨e, he, hqe, ?_⟩
    have hFt : ContDiffAt ℝ ∞ F t := hF.contDiffAt
      (isOpen_Ioo.mem_nhds (by change t - δ < t ∧ t < t + δ; constructor <;> linarith))
    have hnear : (fun s => coordinates e (IccExtend zero_le_one c s)) =ᶠ[𝓝 t] F := by
      filter_upwards [isOpen_Ioo.mem_nhds ht, Metric.ball_mem_nhds t hδ] with s hs hst
      rw [IccExtend_of_mem _ _ ⟨hs.1.le, hs.2.le⟩]
      exact (heq ⟨s, hs.1.le, hs.2.le⟩ (by
        change |s - t| < δ
        simpa only [Metric.mem_ball, Real.dist_eq] using hst)).2.symm
    exact ⟨hFt.congr_of_eventuallyEq hnear, by rw [hnear.deriv_eq]; exact hFn⟩
  · intro t _ e he hte
    exact h t e he hte


/-- Finite smooth curve cuts assemble into an embedded graph once all curve
intersections have been marked. The source curves have their actual subspace
 topology, including all endpoint accumulations. -/
theorem embeddedGraph_of_finite_smooth_curves {kind : ModelKind}
    (W : SmoothManifold 2 kind X) {ι : Type v} [Finite ι]
    (K : ι → Set X) (C : ∀ i, SmoothManifold 1 .euclidean (K i))
    [∀ i, CompactSpace (K i)]
    (hsm : ∀ i, SmoothManifolds.MapData.IsSmoothMap (C i) W Subtype.val)
    (himm : ∀ i, SmoothManifolds.MapClassData.IsImmersion (C i) W Subtype.val)
    (hcross : ∀ i j, i ≠ j → (K i ∩ K j).Finite) :
    ∃ G : EmbeddedGraph W, G.carrier = ⋃ i, K i ∧
      (∀ i j, i ≠ j → K i ∩ K j ⊆ range G.vertex) ∧
      (∀ e, RegularEdgeEndpoints W (G.edge e)) ∧
      (∀ e, ∃ i, ∀ t : unitInterval, G.edge e t ∈ K i) ∧
      (∀ e, RegularCoordinateGerms W (G.edge e)) := by
  classical
  let Q : ∀ i, Set (K i) := fun i => ⋃ j, ⋃ (_ : i ≠ j),
    (Subtype.val : K i → X) ⁻¹' (K i ∩ K j)
  have hQ : ∀ i, (Q i).Finite := by
    intro i
    apply Set.finite_iUnion
    intro j
    apply Set.finite_iUnion
    intro hij
    exact (hcross i j hij).preimage (Subtype.val_injective.injOn)
  have hcuts := fun i => CurveCuts.smooth_curve_interval_cutting (C i) (Q i) (hQ i)
  choose P hP hQP hfinite cuts using hcuts
  let : ∀ i, Finite (ConnectedComponents ((P i)ᶜ : Set (K i))) := hfinite
  let c := fun i => (cuts i).some
  let V : Set X := ⋃ i, (Subtype.val : K i → X) '' P i
  have hV : V.Finite := Set.finite_iUnion fun i => (hP i).image Subtype.val
  let E := Σ i, ConnectedComponents ((P i)ᶜ : Set (K i))
  let edge : E → C(unitInterval, X) := fun e =>
    (c e.1 e.2).imageMap ⟨Subtype.val, continuous_subtype_val⟩
  have hedge (e : E) (t : unitInterval) : edge e t = ((c e.1 e.2).map t).val := rfl
  have hopen (e : E) (t : unitInterval) (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1) :
      (c e.1 e.2).map t ∈ componentSet ((P e.1)ᶜ) e.2 := by
    rw [← (c e.1 e.2).open_image]
    exact ⟨t, ht, rfl⟩
  have hmark (i : ι) (x : K i) (hx : x.val ∈ V) : x ∈ P i := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    obtain ⟨y,hy,hyx⟩ := hj
    by_cases hij : i = j
    · subst j
      have hxy : y = x := Subtype.ext hyx
      exact hxy ▸ hy
    · apply hQP i
      exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hij, ⟨x.property, by rw [← hyx]; exact y.property⟩⟩⟩
  have h0 : ∀ e, edge e 0 ∈ V := by
    intro e
    exact mem_iUnion.mpr ⟨e.1, (c e.1 e.2).map 0, (c e.1 e.2).initial_mark, rfl⟩
  have h1 : ∀ e, edge e 1 ∈ V := by
    intro e
    exact mem_iUnion.mpr ⟨e.1, (c e.1 e.2).map 1, (c e.1 e.2).terminal_mark, rfl⟩
  have hinj : ∀ e, Set.InjOn (edge e) {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
    intro e t _ q _ htq
    exact (c e.1 e.2).injective (Subtype.ext htq)
  have havoid : ∀ e (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → edge e t ∉ V := by
    intro e t ht ht' hv
    exact (Components.subset _ _ (hopen e t ⟨ht,ht'⟩)) (hmark _ _ hv)
  have hdisj : Pairwise (fun i j => Disjoint
      (edge i '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1})
      (edge j '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1})) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    rintro x ⟨t,ht,rfl⟩ ⟨q,hq,hqt⟩
    by_cases hij : a.1 = b.1
    · obtain ⟨i,a⟩ := a
      obtain ⟨j,b⟩ := b
      dsimp at hij
      subst j
      have hab' : a ≠ b := by intro h; exact hab (Sigma.ext rfl (heq_of_eq h))
      have htq : (c i b).map q = (c i a).map t := Subtype.ext hqt
      exact Set.disjoint_left.mp (Components.disjoint _ a b hab')
        (hopen ⟨i,a⟩ t ht) (htq ▸ hopen ⟨i,b⟩ q hq)
    · have hxQ : (c a.1 a.2).map t ∈ Q a.1 := by
        refine mem_iUnion.mpr ⟨b.1, mem_iUnion.mpr ⟨hij, ?_⟩⟩
        refine ⟨((c a.1 a.2).map t).property, ?_⟩
        change edge a t ∈ K b.1
        rw [← hqt]
        exact ((c b.1 b.2).map q).property
      exact (Components.subset _ _ (hopen a t ht)) (hQP _ hxQ)
  have hreg : ∀ e, RegularOpenEdge W (edge e) := by
    intro e
    exact ((c e.1 e.2).imageMap_regular (C e.1) W Subtype.val
      (hsm e.1) (himm e.1)).1
  obtain ⟨G,hvertex,hcarrier,hforward,_⟩ := embeddedGraph_of_finite_edges W V hV edge h0 h1 hinj havoid hdisj hreg
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcarrier]
    ext x
    constructor
    · rintro (hx | hx)
      · obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i,y.property⟩
      · obtain ⟨e,t,rfl⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨e.1,((c e.1 e.2).map t).property⟩
    · intro hx
      obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
      by_cases hxP : (⟨x,hxi⟩ : K i) ∈ P i
      · exact Or.inl (mem_iUnion.mpr ⟨i,⟨x,hxi⟩,hxP,rfl⟩)
      · have hxC : (⟨x,hxi⟩ : K i) ∈ ⋃ a, componentSet ((P i)ᶜ) a := by
          rw [Components.union_eq]
          exact hxP
        obtain ⟨a,ha⟩ := mem_iUnion.mp hxC
        obtain ⟨t,ht,htx⟩ := (c i a).open_image ▸ ha
        exact Or.inr (mem_iUnion.mpr ⟨⟨i,a⟩, t, by exact congrArg Subtype.val htx⟩)
  · intro i j hij x hx
    rw [hvertex]
    apply mem_iUnion.mpr
    refine ⟨i, ⟨x,hx.1⟩, hQP i ?_, rfl⟩
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hij,hx⟩⟩
  · intro e
    obtain ⟨a,ha⟩ := hforward e
    rw [ha]
    exact ((c a.1 a.2).imageMap_regular (C a.1) W Subtype.val
      (hsm a.1) (himm a.1)).2
  · intro e
    obtain ⟨a,ha⟩ := hforward e
    refine ⟨a.1, fun t => ?_⟩
    rw [ha]
    exact ((c a.1 a.2).map t).property
  · intro e
    obtain ⟨a, ha⟩ := hforward e
    rw [ha]
    intro t d hd htd
    exact (c a.1 a.2).regular_image_germs (C a.1) W Subtype.val
      (hsm a.1) (himm a.1) t d hd htd

namespace Arrangement
variable {X : Type u} [TopologicalSpace X]
variable {W : SmoothManifold 2 .euclidean X} {K : Set X}
variable {A : Set (ModelChart 2 .euclidean X)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)

/-- Actual smooth structures of all arrangement curves, retaining the seam
and circle inclusions rather than introducing independent curve labels. -/
def curveManifold (k : Option (Fin T.count)) :
    SmoothManifold 1 .euclidean (arrangementCurve B.carrier T.disk T.radius k) :=
  match k with
  | none => B.manifold
  | some i => (T.circle i).manifold

theorem curve_embedding (k : Option (Fin T.count)) :
    SmoothManifolds.MapClassData.IsSmoothEmbedding (curveManifold T k) W Subtype.val := by
  cases k with
  | none => exact B.embedding
  | some i => exact (T.circle i).embedding

theorem curve_compact (k : Option (Fin T.count)) :
    IsCompact (arrangementCurve B.carrier T.disk T.radius k) := by
  cases k with
  | none => exact B.compact
  | some i =>
    exact (isCompact_sphere (T.disk i).center (T.radius i)).image_of_continuousOn
      ((T.disk i).chart.symm.continuousOn.mono
        (Metric.sphere_subset_closedBall.trans
          (ChartDisk.closedBall_subset_target _ (T.radius_bounds i).2.le)))

theorem finite_curve_intersection (i j : Option (Fin T.count)) (hij : i ≠ j) :
    (arrangementCurve B.carrier T.disk T.radius i ∩
      arrangementCurve B.carrier T.disk T.radius j).Finite := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some b => simpa only [arrangementCurve, inter_comm] using T.finite_seam b
  | some a =>
    cases j with
    | none => exact T.finite_seam a
    | some b => exact T.finite_pairs a b (fun h => hij (congrArg some h))


end Arrangement


/-- Relatively open model sets lying in the model's ambient interior are open
in the full ambient space. -/
theorem isOpen_subtype_image_of_interior
    {Y : Type*} [TopologicalSpace Y] {K : Set Y} {V : Set K}
    (hV : IsOpen V) (hinterior : Subtype.val '' V ⊆ interior K) :
    IsOpen (Subtype.val '' V) := by
  obtain ⟨W, hW, hWV⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hV
  have heq : Subtype.val '' V = W ∩ interior K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨by rw [← hWV] at hz; exact hz, hinterior (mem_image_of_mem _ hz)⟩
    · rintro ⟨hyW, hyint⟩
      refine ⟨⟨y, interior_subset hyint⟩, ?_, rfl⟩
      rw [← hWV]
      exact hyW
  rw [heq]
  exact hW.inter isOpen_interior

/-- The coordinate image of an open set avoiding the true boundary is open
in the full plane, even if the original surface uses a half-space model. -/
theorem isOpen_coordinate_image_away_boundary
    {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (e : ModelChart 2 kind X)
    (he : e ∈ S.smoothStructure.val) {C : Set X}
    (hopen : IsOpen C) (hsource : C ⊆ e.source)
    (hmiss : Disjoint C (intrinsicBoundary S)) :
    IsOpen (coordinates e '' C) := by
  have hmodel : IsOpen (e '' C) := e.isOpen_image_of_subset_source hopen hsource
  have hinterior : Subtype.val '' (e '' C) ⊆ interior (modelSet 2 kind) := by
    rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    by_contra hni
    have hface := (SmoothManifolds.mem_modelFace_iff_not_mem_interior (e x)).mpr hni
    exact Set.disjoint_left.mp hmiss hx ⟨e, he, hsource hx, hface⟩
  have hamb := isOpen_subtype_image_of_interior hmodel hinterior
  convert toPlane.toHomeomorph.isOpenMap _ hamb using 1
  rw [image_image, image_image]
  rfl

/-- Chart coordinates are continuous on the actual chart source. -/
theorem continuousOn_coordinates {X : Type u} [TopologicalSpace X]
    {kind : ModelKind} (e : ModelChart 2 kind X) :
    ContinuousOn (coordinates e) e.source :=
  toPlane.continuous.comp_continuousOn
    (continuous_subtype_val.comp_continuousOn e.continuousOn)

/-- Chart coordinates remain injective before passing to the ambient plane. -/
theorem coordinates_injOn {X : Type u} [TopologicalSpace X]
    {kind : ModelKind} (e : ModelChart 2 kind X) :
    InjOn (coordinates e) e.source := by
  intro x hx y hy hxy
  exact e.injOn hx hy (Subtype.ext (toPlane.injective hxy))

/-- Compact containment makes closure commute with ambient chart coordinates,
including at original boundary points of the surface. -/
theorem closure_coordinate_image {X : Type u} [TopologicalSpace X]
    {kind : ModelKind} (e : ModelChart 2 kind X) {C : Set X}
    (hcompact : IsCompact (closure C)) (hsource : closure C ⊆ e.source) :
    closure (coordinates e '' C) = coordinates e '' closure C := by
  have hc : ContinuousOn (coordinates e) (closure C) :=
    (continuousOn_coordinates e).mono hsource
  exact le_antisymm
    (closure_minimal (image_mono subset_closure) (hcompact.image_of_continuousOn hc).isClosed)
    hc.image_closure

/-- The full-plane frontier is exactly the coordinate image of the actual
component frontier, with no missing seam portion. -/
theorem frontier_coordinate_image_away_boundary
    {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (e : ModelChart 2 kind X)
    (he : e ∈ S.smoothStructure.val) {C : Set X}
    (hopen : IsOpen C) (hcompact : IsCompact (closure C))
    (hsource : closure C ⊆ e.source) (hmiss : Disjoint C (intrinsicBoundary S)) :
    frontier (coordinates e '' C) = coordinates e '' frontier C := by
  have hopen' := isOpen_coordinate_image_away_boundary S e he hopen
    (subset_closure.trans hsource) hmiss
  rw [frontier, hopen'.interior_eq, closure_coordinate_image e hcompact hsource,
    frontier, hopen.interior_eq]
  exact ((coordinates_injOn e).mono hsource).image_sdiff_subset subset_closure |>.symm

/-- The restricted arrangement contains the original intrinsic boundary,
using exactly the designated seam from the smooth double. -/
theorem intrinsicBoundary_subset_restricted_arrangement
    {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B) :
    intrinsicBoundary S ⊆
      P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T := by
  intro x hx
  apply Or.inl
  rw [hB]
  refine ⟨x, hx, ?_⟩
  exact Quotient.sound ⟨rfl, Or.inr hx⟩

/-- Each actual arrangement component supplies a nonempty connected open
full-plane domain with compact closure, all in one original chart. Its closure
and boundary are precisely the coordinate images of the actual closure and
boundary in the surface, including at the seam. -/
theorem arrangement_component_coordinate_domain
    {X : Type u} [TopologicalSpace X] {kind : ModelKind} [CompactSpace X]
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    (hsubordinate : CopySubordinate S D s A)
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (a : ConnectedComponents
      ((P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)ᶜ : Set X)) :
    let C := componentSet
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T)ᶜ a
    ∃ e : ModelChart 2 kind X, e ∈ S.smoothStructure.val ∧
      closure C ⊆ e.source ∧ IsOpen (coordinates e '' C) ∧
      IsConnected (coordinates e '' C) ∧ IsCompact (coordinates e '' closure C) ∧
      closure (coordinates e '' C) = coordinates e '' closure C ∧
      frontier (coordinates e '' C) = coordinates e '' frontier C ∧
      (frontier (coordinates e '' C)).Nonempty := by
  let := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  let G := f ⁻¹' arrangementCarrier T
  let C := componentSet Gᶜ a
  have hG : IsClosed G := (Arrangement.isClosed_carrier T).preimage
    (D.copy_closedEmbedding s).continuous
  have hopen : IsOpen C := Components.isOpen Gᶜ hG.isOpen_compl a
  have hconn : IsConnected C := Components.isConnected Gᶜ a
  have hcompact : IsCompact (closure C) := isClosed_closure.isCompact
  have hmiss : Disjoint C (intrinsicBoundary S) := Set.disjoint_left.mpr (by
    intro x hx hxb
    exact Components.subset Gᶜ a hx
      (intrinsicBoundary_subset_restricted_arrangement S D s hB T hxb))
  obtain ⟨i, e, he, hi, hc, hsource⟩ :=
    arrangement_component_in_original_chart S D s hsubordinate T a
  have hopen' := isOpen_coordinate_image_away_boundary S e he hopen
    (subset_closure.trans hsource) hmiss
  have hfront := frontier_coordinate_image_away_boundary S e he hopen hcompact hsource hmiss
  refine ⟨e, he, hsource, hopen',
    hconn.image _ ((continuousOn_coordinates e).mono (subset_closure.trans hsource)),
    hcompact.image_of_continuousOn ((continuousOn_coordinates e).mono hsource),
    closure_coordinate_image e hcompact hsource, hfront, ?_⟩
  rw [hfront]
  exact (arrangement_component_frontier_nonempty S D s hsubordinate T a).image _


namespace NormalSectors

def axisComplement (J : Set (Fin 2)) (r : ℝ) : Set Plane :=
  {z | z ∈ Metric.ball 0 r ∧ ∀ a ∈ J, z a ≠ 0}

theorem component_eq_chamber (J : Set (Fin 2)) (r : ℝ)
    (a : ConnectedComponents (axisComplement J r)) {x : Plane}
    (hx : x ∈ componentSet (axisComplement J r) a) :
    componentSet (axisComplement J r) a = chamber J r (fun i => decide (0 < x i)) := by
  classical
  have hxU := Components.subset _ a hx
  have hxch : x ∈ chamber J r (fun i => decide (0 < x i)) := by
    refine ⟨hxU.1, mem_iInter₂.mpr ?_⟩
    intro i hi
    simp only [decide_eq_true_eq]
    split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (le_of_not_gt h) (hxU.2 i hi)
  apply Set.Subset.antisymm
  · intro y hy
    refine ⟨(Components.subset _ a hy).1, mem_iInter₂.mpr ?_⟩
    intro i hi
    have hpre := (Components.isConnected (axisComplement J r) a).isPreconnected
    have hcont : ContinuousOn (fun z : Plane => z i) (componentSet (axisComplement J r) a) :=
      (EuclideanSpace.proj i).continuous.continuousOn
    have hne : ∀ z ∈ componentSet (axisComplement J r) a, z i ≠ 0 :=
      fun z hz => (Components.subset _ a hz).2 i hi
    simp only [decide_eq_true_eq]
    split_ifs with h
    · exact hpre.lt_of_ne hcont hne ⟨x, hx, h⟩ hy
    · exact hpre.gt_of_ne hcont hne
        ⟨x, hx, lt_of_le_of_ne (le_of_not_gt h) (hxU.2 i hi)⟩ hy
  · apply Components.contains_preconnected _ (convex_chamber J r _).isPreconnected _ a
      ⟨x, hxch, hx⟩
    intro z hz
    change z ∈ {z | z ∈ Metric.ball 0 r ∧ ∀ a ∈ J, z a ≠ 0}
    rw [← union_chambers J r]
    exact mem_iUnion.mpr ⟨_, hz⟩

/-- Every pair of points in distinct actual axis-complement components has
opposite signs on some active axis. Quantification is over all points. -/
theorem component_separated_by_axis (J : Set (Fin 2)) (r : ℝ)
    (a b : ConnectedComponents (axisComplement J r)) (hab : a ≠ b)
    {x y : Plane} (hx : x ∈ componentSet (axisComplement J r) a)
    (hy : y ∈ componentSet (axisComplement J r) b) :
    ∃ i ∈ J, ¬ (x i < 0 ↔ y i < 0) := by
  classical
  by_contra hn
  push Not at hn
  have hxU := Components.subset _ a hx
  have hyU := Components.subset _ b hy
  have hya : y ∈ componentSet (axisComplement J r) a := by
    rw [component_eq_chamber J r a hx]
    refine ⟨hyU.1, mem_iInter₂.mpr ?_⟩
    intro i hi
    simp only [decide_eq_true_eq]
    split_ifs with h
    · have hny : ¬ y i < 0 := by
        intro hyneg
        have := (hn i hi).mpr hyneg
        linarith
      exact lt_of_le_of_ne (le_of_not_gt hny) (hyU.2 i hi).symm
    · exact (hn i hi).mp (lt_of_le_of_ne (le_of_not_gt h) (hxU.2 i hi))
  exact Set.disjoint_left.mp (Components.disjoint _ a b hab) hya hy

end NormalSectors

namespace Arrangement
open SmoothManifolds.AtlasData SmoothManifolds.ModelData
variable {X : Type*} [TopologicalSpace X]
variable {W : SmoothManifold 2 .euclidean X} {K : Set X}
variable {A : Set (ModelChart 2 .euclidean X)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)
variable {p : X} {O : Set X}
variable (F : ArrangementNormalForm W B.carrier T.disk T.radius p O)

def normalInverse (z : Plane) : X := F.chart.symm (euclideanModelPlane.symm z)

theorem normalInverse_target {z : Plane} (hz : z ∈ Metric.ball (0 : Plane) F.radius) :
    euclideanModelPlane.symm z ∈ F.chart.target := by
  apply F.ball_in_target
  change euclideanModelPlane (euclideanModelPlane.symm z) ∈ Metric.ball 0 F.radius
  simpa only [Homeomorph.apply_symm_apply] using hz

theorem normalInverse_continuous : ContinuousOn (normalInverse T F) (Metric.ball 0 F.radius) :=
  F.chart.symm.continuousOn.comp euclideanModelPlane.symm.continuous.continuousOn
    (fun _ hz => normalInverse_target T F hz)

theorem normalInverse_coordinates {z : Plane} (hz : z ∈ Metric.ball (0 : Plane) F.radius) :
    coordinates F.chart (normalInverse T F z) = z := by
  change euclideanModelPlane (F.chart (F.chart.symm (euclideanModelPlane.symm z))) = z
  rw [F.chart.right_inv (normalInverse_target T F hz), Homeomorph.apply_symm_apply]

theorem normalInverse_mem_complement {z : Plane}
    (hz : z ∈ NormalSectors.axisComplement (activeAxes T F) F.radius) :
    normalInverse T F z ∈ normalNeighborhood T F \ arrangementCarrier T := by
  have hxN : normalInverse T F z ∈ normalNeighborhood T F :=
    ⟨F.chart.map_target (normalInverse_target T F hz.1), by
      change coordinates F.chart (normalInverse T F z) ∈ Metric.ball 0 F.radius
      rw [normalInverse_coordinates T F hz.1]
      exact hz.1⟩
  refine ⟨hxN, ?_⟩
  intro hxG
  obtain ⟨a, ha, hax⟩ := (carrier_iff_axis T F hxN).mp hxG
  rw [normalInverse_coordinates T F hz.1] at hax
  exact hz.2 a ha hax

theorem coordinates_normalComplement {x : X}
    (hx : x ∈ normalNeighborhood T F \ arrangementCarrier T) :
    coordinates F.chart x ∈ NormalSectors.axisComplement (activeAxes T F) F.radius := by
  refine ⟨hx.1.2, ?_⟩
  intro a ha hzero
  exact hx.2 ((carrier_iff_axis T F hx.1).mpr ⟨a, ha, hzero⟩)

def normalChamber (σ : Fin 2 → Bool) : Set X :=
  normalInverse T F '' NormalSectors.chamber (activeAxes T F) F.radius σ

theorem normalChamber_preconnected (σ : Fin 2 → Bool) :
    IsPreconnected (normalChamber T F σ) :=
  (NormalSectors.convex_chamber _ _ σ).isPreconnected.image _
    ((normalInverse_continuous T F).mono inter_subset_left)

theorem normalChamber_subset (σ : Fin 2 → Bool) :
    normalChamber T F σ ⊆ normalNeighborhood T F \ arrangementCarrier T := by
  rintro x ⟨z, hz, rfl⟩
  apply normalInverse_mem_complement T F
  change z ∈ {z | z ∈ Metric.ball 0 F.radius ∧ ∀ a ∈ activeAxes T F, z a ≠ 0}
  rw [← NormalSectors.union_chambers (activeAxes T F) F.radius]
  exact mem_iUnion.mpr ⟨σ, hz⟩

/-- An actual local complementary component equals the image of one entire
convex coordinate sign chamber, not merely a subset or component label. -/
theorem component_eq_normalChamber
    (a : ConnectedComponents (normalNeighborhood T F \ arrangementCarrier T : Set X))
    {x : X} (hx : x ∈ componentSet (normalNeighborhood T F \ arrangementCarrier T) a) :
    componentSet (normalNeighborhood T F \ arrangementCarrier T) a =
      normalChamber T F (fun i => decide (0 < coordinates F.chart x i)) := by
  classical
  let U := normalNeighborhood T F \ arrangementCarrier T
  have hxU : x ∈ U := Components.subset U a hx
  have hxc := coordinates_normalComplement T F hxU
  have hback : ∀ y ∈ U, normalInverse T F (coordinates F.chart y) = y := by
    intro y hy
    change F.chart.symm (euclideanModelPlane.symm (euclideanModelPlane (F.chart y))) = y
    rw [Homeomorph.symm_apply_apply, F.chart.left_inv hy.1.1]
  have hxch : coordinates F.chart x ∈
      NormalSectors.chamber (activeAxes T F) F.radius
        (fun i => decide (0 < coordinates F.chart x i)) := by
    refine ⟨hxc.1, mem_iInter₂.mpr ?_⟩
    intro i hi
    simp only [decide_eq_true_eq]
    split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (le_of_not_gt h) (hxc.2 i hi)
  apply Set.Subset.antisymm
  · intro y hy
    have hyU : y ∈ U := Components.subset U a hy
    refine ⟨coordinates F.chart y, ⟨hyU.1.2, mem_iInter₂.mpr ?_⟩, hback y hyU⟩
    intro i hi
    have hpre := (Components.isConnected U a).isPreconnected
    have hcont : ContinuousOn (fun z : X => coordinates F.chart z i) (componentSet U a) := by
      have hc : ContinuousOn (coordinates F.chart) (componentSet U a) :=
        ((toPlane.continuous.comp continuous_subtype_val).comp_continuousOn
          F.chart.continuousOn).mono (fun z hz => (Components.subset U a hz).1.1)
      exact (EuclideanSpace.proj i).continuous.comp_continuousOn hc
    have hne : ∀ z ∈ componentSet U a, coordinates F.chart z i ≠ 0 :=
      fun z hz => (coordinates_normalComplement T F (Components.subset U a hz)).2 i hi
    simp only [decide_eq_true_eq]
    split_ifs with h
    · exact hpre.lt_of_ne hcont hne ⟨x, hx, h⟩ hy
    · exact hpre.gt_of_ne hcont hne
        ⟨x, hx, lt_of_le_of_ne (le_of_not_gt h) (hxc.2 i hi)⟩ hy
  · exact Components.contains_preconnected U (normalChamber_preconnected T F _)
      (normalChamber_subset T F _) a ⟨x, ⟨_, hxch, hback x hxU⟩, hx⟩

/-- Distinct actual sectors in the full ambient normal-form disk are separated
by an active curve axis. A seam axis is allowed in this ambient statement. -/
theorem normal_components_separated
    (a b : ConnectedComponents (normalNeighborhood T F \ arrangementCarrier T : Set X))
    (hab : a ≠ b) {x y : X}
    (hx : x ∈ componentSet (normalNeighborhood T F \ arrangementCarrier T) a)
    (hy : y ∈ componentSet (normalNeighborhood T F \ arrangementCarrier T) b) :
    ∃ k : Option (Fin T.count), ∃ i : Fin 2, F.axis k = some i ∧
      ¬ (coordinates F.chart x i < 0 ↔ coordinates F.chart y i < 0) := by
  classical
  let U := normalNeighborhood T F \ arrangementCarrier T
  have hxU : x ∈ U := Components.subset U a hx
  have hyU : y ∈ U := Components.subset U b hy
  have hxc := coordinates_normalComplement T F hxU
  have hyc := coordinates_normalComplement T F hyU
  by_contra hn
  push Not at hn
  have hsign : ∀ i ∈ activeAxes T F,
      coordinates F.chart x i < 0 ↔ coordinates F.chart y i < 0 := by
    intro i hi
    obtain ⟨k, hk⟩ := hi
    exact hn k i hk
  have hych : coordinates F.chart y ∈
      NormalSectors.chamber (activeAxes T F) F.radius
        (fun i => decide (0 < coordinates F.chart x i)) := by
    refine ⟨hyc.1, mem_iInter₂.mpr ?_⟩
    intro i hi
    simp only [decide_eq_true_eq]
    split_ifs with h
    · have hny : ¬ coordinates F.chart y i < 0 := by
        intro hyneg
        have := (hsign i hi).mpr hyneg
        linarith
      exact lt_of_le_of_ne (le_of_not_gt hny) (hyc.2 i hi).symm
    · exact (hsign i hi).mp (lt_of_le_of_ne (le_of_not_gt h) (hxc.2 i hi))
  have hya : y ∈ componentSet U a := by
    rw [component_eq_normalChamber T F a hx]
    refine ⟨_, hych, ?_⟩
    change F.chart.symm (euclideanModelPlane.symm (euclideanModelPlane (F.chart y))) = y
    rw [Homeomorph.symm_apply_apply, F.chart.left_inv hyU.1.1]
  exact Set.disjoint_left.mp (Components.disjoint U a b hab) hya hy

end Arrangement

/-- If an edge cannot switch sides across a subset, retain precisely its
whole contained edges and the contained original vertices. -/
theorem embeddedGraph_restrict {kind : ModelKind} (W : SmoothManifold 2 kind X)
    (G : EmbeddedGraph W) (L : Set X)
    (hselect : ∀ i, ((G.edge i '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1}) ∩ L).Nonempty →
      range (G.edge i) ⊆ L) :
    ∃ H : EmbeddedGraph W,
      range H.vertex = range G.vertex ∩ L ∧
      H.carrier = G.carrier ∩ L ∧
      (∀ i, ∃ j, range (G.edge j) ⊆ L ∧ H.edge i = G.edge j) ∧
      (∀ j, range (G.edge j) ⊆ L → ∃ i, H.edge i = G.edge j) := by
  classical
  let V : Set X := range G.vertex ∩ L
  have hV : V.Finite := (Set.finite_range G.vertex).subset inter_subset_left
  let E := {i : Fin G.edgeCount // range (G.edge i) ⊆ L}
  let c : E → C(unitInterval, X) := fun i => G.edge i.val
  have h0 : ∀ i, c i 0 ∈ V := by
    intro i
    exact ⟨⟨G.initial i.val, (G.at_zero i.val).symm⟩,
      i.property (mem_range_self 0)⟩
  have h1 : ∀ i, c i 1 ∈ V := by
    intro i
    exact ⟨⟨G.terminal i.val, (G.at_one i.val).symm⟩,
      i.property (mem_range_self 1)⟩
  have havoid : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → c i t ∉ V := by
    intro i t ht ht' hmem
    exact G.avoids_vertices i.val t ht ht' hmem.1
  have hdisj : Pairwise (fun i j => Disjoint
      (c i '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1})
      (c j '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1})) := by
    intro i j hij
    exact G.disjoint_open_edges (Subtype.val_injective.ne hij)
  obtain ⟨H,hvertex,hcarrier,hforward,hreverse⟩ := embeddedGraph_of_finite_edges
    W V hV c (fun i => h0 i) (fun i => h1 i) (fun i => G.open_injective i.val)
    havoid hdisj (fun i => G.regular i.val)
  refine ⟨H,hvertex,?_,?_,?_⟩
  · rw [hcarrier]
    apply Set.Subset.antisymm
    · rintro x (hx | hx)
      · exact ⟨Or.inl hx.1,hx.2⟩
      · obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hx
        exact ⟨Or.inr (mem_iUnion.mpr ⟨i.val,mem_range_self t⟩),
          i.property (mem_range_self t)⟩
    · rintro x ⟨(hx | hx),hxL⟩
      · exact Or.inl ⟨hx,hxL⟩
      · obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hx
        by_cases ht0 : t = 0
        · subst t
          exact Or.inl ⟨⟨G.initial i, (G.at_zero i).symm⟩,hxL⟩
        by_cases ht1 : t = 1
        · subst t
          exact Or.inl ⟨⟨G.terminal i, (G.at_one i).symm⟩,hxL⟩
        have ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
          constructor
          · exact lt_of_le_of_ne t.property.1 (by intro h; exact ht0 (Subtype.ext h.symm))
          · exact lt_of_le_of_ne t.property.2 (by intro h; exact ht1 (Subtype.ext h))
        have hcontain : range (G.edge i) ⊆ L := hselect i ⟨G.edge i t, ⟨t,ht,rfl⟩,hxL⟩
        exact Or.inr (mem_iUnion.mpr ⟨⟨i,hcontain⟩,t,rfl⟩)
  · intro i
    obtain ⟨j,hj⟩ := hforward i
    exact ⟨j.val,j.property,hj⟩
  · intro j hj
    exact hreverse ⟨j,hj⟩

namespace Arrangement
variable {X : Type u} [TopologicalSpace X]
variable {W : SmoothManifold 2 .euclidean X} {K : Set X}
variable {A : Set (ModelChart 2 .euclidean X)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)

/-- Cutting the actual compact seam and circles constructs a finite embedded
ambient graph. Every crossing is a vertex and every edge has smooth regular
endpoint germs. No prior graph or one-manifold classification is assumed. -/
theorem ambient_graph :
    ∃ G : EmbeddedGraph W, G.carrier = arrangementCarrier T ∧
      (∀ i j : Option (Fin T.count), i ≠ j →
        arrangementCurve B.carrier T.disk T.radius i ∩
          arrangementCurve B.carrier T.disk T.radius j ⊆ range G.vertex) ∧
      (∀ e, RegularEdgeEndpoints W (G.edge e)) ∧
      (∀ e, ∃ i : Option (Fin T.count), ∀ t : unitInterval,
        G.edge e t ∈ arrangementCurve B.carrier T.disk T.radius i) ∧
      (∀ e, RegularCoordinateGerms W (G.edge e)) := by
  let C := arrangementCurve B.carrier T.disk T.radius
  let inst (i : Option (Fin T.count)) : CompactSpace (C i) :=
    isCompact_iff_compactSpace.mp (curve_compact T i)
  obtain ⟨G, hG, hcross, hends, hcurve, hgerms⟩ := embeddedGraph_of_finite_smooth_curves W
    C (curveManifold T) (fun i => (curve_embedding T i).1)
    (fun i => (curve_embedding T i).2.2.1) (finite_curve_intersection T)
  exact ⟨G, hG.trans (carrier_eq_iUnion T).symm, hcross, hends, hcurve, hgerms⟩


end Arrangement

namespace Arrangement
variable {X : Type u} [TopologicalSpace X]
variable {W : SmoothManifold 2 .euclidean X} {K : Set X}
variable {A : Set (ModelChart 2 .euclidean X)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)

/-- After cutting at actual crossings, each nonseam open edge misses the seam.
Consequently every edge meeting one closed side in its open part lies entirely
in that side; seam edges are already contained in the side. -/
theorem graph_edge_in_closed_side
    (G : EmbeddedGraph W)
    (hcross : ∀ i : Fin T.count,
      (T.disk i).circleAtRadius (T.radius i) ∩ B.carrier ⊆ range G.vertex)
    (hcurve : ∀ e, ∃ k : Option (Fin T.count), ∀ t : unitInterval,
      G.edge e t ∈ arrangementCurve B.carrier T.disk T.radius k)
    {L R : Set X} (hL : IsClosed L) (hR : IsClosed R) (hcover : L ∪ R = univ)
    (hseam : B.carrier ⊆ L) (hoverlap : L ∩ R ⊆ B.carrier)
    (e : Fin G.edgeCount)
    (hmeet : ((G.edge e '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}) ∩ L).Nonempty) :
    range (G.edge e) ⊆ L := by
  let := W.topologicalManifold.hausdorff
  obtain ⟨k, hk⟩ := hcurve e
  cases k with
  | none =>
    rintro x ⟨t, rfl⟩
    exact hseam (hk t)
  | some i =>
    apply edge_range_subset_closed_side (G.edge e) hL hR hcover _ hmeet
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ hxLR
    exact G.avoids_vertices e t ht.1 ht.2 (hcross i ⟨hk t, hoverlap hxLR⟩)


end Arrangement

namespace Arrangement
variable {X : Type u} [TopologicalSpace X]
variable {W : SmoothManifold 2 .euclidean X} {K : Set X}
variable {A : Set (ModelChart 2 .euclidean X)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)

/-- The finite actual arrangement can be restricted to either member of a
closed cover meeting exactly along its seam. Edges meeting that side are
retained whole, including their smooth regular endpoint germs. -/
theorem graph_on_closed_side {L R : Set X}
    (hL : IsClosed L) (hR : IsClosed R) (hcover : L ∪ R = univ)
    (hseam : B.carrier ⊆ L) (hoverlap : L ∩ R ⊆ B.carrier) :
    ∃ G : EmbeddedGraph W, G.carrier = L ∩ arrangementCarrier T ∧
      (∀ e, RegularEdgeEndpoints W (G.edge e)) ∧
      (∀ e, ∃ k : Option (Fin T.count), ∀ t : unitInterval,
        G.edge e t ∈ arrangementCurve B.carrier T.disk T.radius k) ∧
      (∀ e, RegularCoordinateGerms W (G.edge e)) := by
  obtain ⟨G, hG, hcross, hends, hcurve, hgerms⟩ := ambient_graph T
  have hcross' : ∀ i : Fin T.count,
      (T.disk i).circleAtRadius (T.radius i) ∩ B.carrier ⊆ range G.vertex := by
    intro i
    exact hcross (some i) none (by simp)
  obtain ⟨H, hV, hH, hforward, hreverse⟩ := embeddedGraph_restrict W G L
    (graph_edge_in_closed_side T G hcross' hcurve hL hR hcover hseam hoverlap)
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · rw [hH, hG, inter_comm]
  · intro e
    obtain ⟨j, hj, heq⟩ := hforward e
    rw [heq]
    exact hends j
  · intro e
    obtain ⟨j, hj, heq⟩ := hforward e
    rw [heq]
    exact hcurve j
  · intro e
    obtain ⟨j, hj, heq⟩ := hforward e
    rw [heq]
    exact hgerms j

end Arrangement
variable {X : Type u} [TopologicalSpace X]

/-- A finite graph of genuine compact regular arcs on the designated copy,
currently expressed in the double. Its carrier is exactly the restricted
arrangement. Pullback to the original atlas is a separate smoothness step. -/
theorem arrangement_graph_on_copy {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B) :
    ∃ G : EmbeddedGraph D.manifold,
      G.carrier = range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s) ∩
        arrangementCarrier T ∧
      (∀ e, RegularEdgeEndpoints D.manifold (G.edge e)) ∧
      (∀ e, ∃ k : Option (Fin T.count), ∀ t : unitInterval,
        G.edge e t ∈ arrangementCurve B.carrier T.disk T.radius k) ∧
      (∀ e, RegularCoordinateGerms D.manifold (G.edge e)) := by
  let L := range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)
  let R := range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) (!s))
  have hcover : L ∪ R = univ := by
    cases s
    · exact D.copies_cover
    · simpa only [L, R, Bool.not_true, union_comm] using D.copies_cover
  have hoverlap : L ∩ R = B.carrier := by
    rw [hB]
    cases s
    · exact D.copies_intersect
    · simpa only [L, R, Bool.not_true, inter_comm] using D.copies_intersect
  exact Arrangement.graph_on_closed_side T
    (D.copy_closedEmbedding s).isClosed_range (D.copy_closedEmbedding (!s)).isClosed_range
    hcover (by rw [← hoverlap]; exact inter_subset_left)
    (by rw [hoverlap])


namespace Arrangement
open SmoothManifolds.AtlasData SmoothManifolds.ModelData
variable {X : Type*} [TopologicalSpace X]
variable {W : SmoothManifold 2 .euclidean X} {K : Set X}
variable {A : Set (ModelChart 2 .euclidean X)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)
variable {p : X} {O : Set X}
variable (F : ArrangementNormalForm W B.carrier T.disk T.radius p O)
/-- Every disk's exact frontier is part of the full removed carrier. -/
theorem disk_frontier_subset_carrier (i : Fin T.count) :
    frontier ((T.disk i).openAtRadius (T.radius i)) ⊆ arrangementCarrier T := by
  let := W.topologicalManifold.hausdorff
  rw [ChartDisk.frontier_openAtRadius _
    ((T.disk i).inner_pos.trans (T.radius_bounds i).1) (T.radius_bounds i).2.le]
  exact fun x hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩)

/-- Disk membership is constant even on actual local sectors, by inclusion
into the ambient global complementary component. -/
theorem local_disk_membership_constant (i : Fin T.count)
    (a : ConnectedComponents (normalNeighborhood T F \ arrangementCarrier T : Set X))
    {x y : X} (hx : x ∈ componentSet (normalNeighborhood T F \ arrangementCarrier T) a)
    (hy : y ∈ componentSet (normalNeighborhood T F \ arrangementCarrier T) a) :
    x ∈ (T.disk i).openAtRadius (T.radius i) ↔
      y ∈ (T.disk i).openAtRadius (T.radius i) := by
  let incl := Components.inclusion (arrangementCarrier T)ᶜ
    (fun _ hz => hz.2 : normalNeighborhood T F \ arrangementCarrier T ⊆ (arrangementCarrier T)ᶜ)
  apply Components.disk_membership_constant (arrangementCarrier T) _
    (ChartDisk.isOpen_openAtRadius _ _) (disk_frontier_subset_carrier T i) (incl a)
  · exact Components.subset_inclusion _ _ a hx
  · exact Components.subset_inclusion _ _ a hy

/-- Away from the seam axis, all distinct local sectors have different disk
memberships. The witness disk works for every point in both actual sectors. -/
theorem normal_components_separated_by_disks (hseam : F.axis none = none)
    (a b : ConnectedComponents (normalNeighborhood T F \ arrangementCarrier T : Set X))
    (hab : a ≠ b) :
    ∃ i : Fin T.count,
      ∀ x ∈ componentSet (normalNeighborhood T F \ arrangementCarrier T) a,
      ∀ y ∈ componentSet (normalNeighborhood T F \ arrangementCarrier T) b,
      ¬ (x ∈ (T.disk i).openAtRadius (T.radius i) ↔
         y ∈ (T.disk i).openAtRadius (T.radius i)) := by
  obtain ⟨x, hx⟩ := Components.nonempty _ a
  obtain ⟨y, hy⟩ := Components.nonempty _ b
  obtain ⟨k, i, hki, hxy⟩ := normal_components_separated T F a b hab hx hy
  cases k with
  | none => simp only [hseam, reduceCtorEq] at hki
  | some j =>
    have hxU := Components.subset _ a hx
    have hyU := Components.subset _ b hy
    have hxyD : ¬ (x ∈ (T.disk j).openAtRadius (T.radius j) ↔
        y ∈ (T.disk j).openAtRadius (T.radius j)) := by
      rw [F.disk_sign j x hxU.1.1 hxU.1.2, F.disk_sign j y hyU.1.1 hyU.1.2, hki]
      exact hxy
    refine ⟨j, ?_⟩
    intro u hu v hv huv
    apply hxyD
    exact (local_disk_membership_constant T F j a hx hu).trans
      (huv.trans (local_disk_membership_constant T F j b hy hv).symm)

/-- The source's no-return conclusion at points where the seam is inactive. -/
theorem normal_component_inclusion_injective (hseam : F.axis none = none) :
    Function.Injective (Components.inclusion (arrangementCarrier T)ᶜ
      (fun _ hz => hz.2 : normalNeighborhood T F \ arrangementCarrier T ⊆
        (arrangementCarrier T)ᶜ)) := by
  apply Components.inclusion_injective_of_disk_memberships (arrangementCarrier T)
    (normalNeighborhood T F) (fun i => (T.disk i).openAtRadius (T.radius i))
    (fun i => ChartDisk.isOpen_openAtRadius _ _) (disk_frontier_subset_carrier T)
  intro a b hab
  obtain ⟨i, hi⟩ := normal_components_separated_by_disks T F hseam a b hab
  obtain ⟨x, hx⟩ := Components.nonempty _ a
  obtain ⟨y, hy⟩ := Components.nonempty _ b
  exact ⟨i, x, hx, y, hy, hi x hx y hy⟩


end Arrangement

section GraphPullback
variable {Y : Type v} [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z]
/-- The actual inverse of an embedding, restricted to points in its range. -/
def liftPoint {f : X → Y} (hf : IsEmbedding f) (y : Y) (hy : y ∈ range f) : X :=
  hf.toHomeomorph.symm ⟨y,hy⟩

theorem map_liftPoint {f : X → Y} (hf : IsEmbedding f) (y : Y)
    (hy : y ∈ range f) : f (liftPoint hf y hy) = y := by
  exact congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply ⟨y,hy⟩)

/-- Lifting a continuous map through an embedding retains the actual topology. -/
def liftContinuousMap {f : X → Y} (hf : IsEmbedding f) (c : C(Z,Y))
    (hc : range c ⊆ range f) : C(Z,X) :=
  ⟨fun z => liftPoint hf (c z) (hc (mem_range_self z)),
    hf.toHomeomorph.symm.continuous.comp (c.continuous.subtype_mk _)⟩

theorem map_liftContinuousMap {f : X → Y} (hf : IsEmbedding f)
    (c : C(Z,Y)) (hc : range c ⊆ range f) (z : Z) :
    f (liftContinuousMap hf c hc z) = c z := map_liftPoint hf _ _

namespace EmbeddedGraph
variable {kindX kindY : ModelKind}
variable {S : SmoothManifold 2 kindX X} {W : SmoothManifold 2 kindY Y}

/-- Each closed edge is contained in the actual graph carrier. -/
theorem edge_subset_carrier (G : EmbeddedGraph W) (i : Fin G.edgeCount) :
    range (G.edge i) ⊆ G.carrier :=
  fun _ hx => Or.inr (mem_iUnion.mpr ⟨i,hx⟩)

/-- The continuous pullback of one whole edge whose image lies in the embedding. -/
def liftEdge (G : EmbeddedGraph W) {f : X → Y} (hf : IsEmbedding f)
    (hG : G.carrier ⊆ range f) (i : Fin G.edgeCount) : C(unitInterval,X) :=
  liftContinuousMap hf (G.edge i) ((edge_subset_carrier G i).trans hG)

theorem map_liftEdge (G : EmbeddedGraph W) {f : X → Y} (hf : IsEmbedding f)
    (hG : G.carrier ⊆ range f) (i : Fin G.edgeCount) (t : unitInterval) :
    f (liftEdge G hf hG i t) = G.edge i t := map_liftContinuousMap hf _ _ t

/-- A graph carried by an embedded copy pulls back with the same incidence
and edge labels. Smooth regularity is supplied independently by the actual
coordinate transport; topology alone is never used to infer it. -/
def pullback (S : SmoothManifold 2 kindX X) (G : EmbeddedGraph W)
    {f : X → Y} (hf : IsEmbedding f) (hG : G.carrier ⊆ range f)
    (hreg : ∀ i, RegularOpenEdge S (liftEdge G hf hG i)) : EmbeddedGraph S := by
  let vertex : Fin G.vertexCount → X := fun i =>
    liftPoint hf (G.vertex i) (hG (Or.inl (mem_range_self i)))
  have hv : ∀ i, f (vertex i) = G.vertex i := fun i => map_liftPoint hf _ _
  exact {
    vertexCount := G.vertexCount
    edgeCount := G.edgeCount
    vertex := vertex
    vertex_injective := by
      intro i j hij
      apply G.vertex_injective
      simpa only [hv] using congrArg f hij
    edge := liftEdge G hf hG
    initial := G.initial
    terminal := G.terminal
    at_zero := by
      intro i
      apply hf.injective
      rw [map_liftEdge G hf hG i 0, hv, G.at_zero]
    at_one := by
      intro i
      apply hf.injective
      rw [map_liftEdge G hf hG i 1, hv, G.at_one]
    open_injective := by
      intro i t ht q hq htq
      apply G.open_injective i ht hq
      simpa only [map_liftEdge G] using congrArg f htq
    avoids_vertices := by
      intro i t ht ht' hmem
      obtain ⟨j,hj⟩ := hmem
      apply G.avoids_vertices i t ht ht'
      refine ⟨j,?_⟩
      simpa only [hv,map_liftEdge G] using congrArg f hj
    disjoint_open_edges := by
      intro i j hij
      apply Set.disjoint_left.mpr
      rintro x ⟨t,ht,rfl⟩ ⟨q,hq,hqt⟩
      apply Set.disjoint_left.mp (G.disjoint_open_edges hij)
        (show G.edge i t ∈ G.edge i '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1} from ⟨t,ht,rfl⟩)
      refine ⟨q,hq,?_⟩
      simpa only [map_liftEdge G] using congrArg f hqt
    regular := hreg }

@[simp] theorem pullback_edge (S : SmoothManifold 2 kindX X) (G : EmbeddedGraph W)
    {f : X → Y} (hf : IsEmbedding f) (hG : G.carrier ⊆ range f)
    (hreg : ∀ i, RegularOpenEdge S (liftEdge G hf hG i)) (i : Fin G.edgeCount) :
    (pullback S G hf hG hreg).edge i = liftEdge G hf hG i := rfl

theorem map_pullback_vertex (S : SmoothManifold 2 kindX X) (G : EmbeddedGraph W)
    {f : X → Y} (hf : IsEmbedding f) (hG : G.carrier ⊆ range f)
    (hreg : ∀ i, RegularOpenEdge S (liftEdge G hf hG i)) (i : Fin G.vertexCount) :
    f ((pullback S G hf hG hreg).vertex i) = G.vertex i := map_liftPoint hf _ _

theorem map_pullback_edge (S : SmoothManifold 2 kindX X) (G : EmbeddedGraph W)
    {f : X → Y} (hf : IsEmbedding f) (hG : G.carrier ⊆ range f)
    (hreg : ∀ i, RegularOpenEdge S (liftEdge G hf hG i))
    (i : Fin G.edgeCount) (t : unitInterval) :
    f ((pullback S G hf hG hreg).edge i t) = G.edge i t := map_liftEdge G hf hG i t

/-- Both edges and vertices are pulled back exactly, not merely included. -/
theorem pullback_carrier (S : SmoothManifold 2 kindX X) (G : EmbeddedGraph W)
    {f : X → Y} (hf : IsEmbedding f) (hG : G.carrier ⊆ range f)
    (hreg : ∀ i, RegularOpenEdge S (liftEdge G hf hG i)) :
    (pullback S G hf hG hreg).carrier = f ⁻¹' G.carrier := by
  ext x
  constructor
  · rintro (⟨i,rfl⟩ | hx)
    · exact Or.inl ⟨i,(map_pullback_vertex S G hf hG hreg i).symm⟩
    · obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨i,t,(map_pullback_edge S G hf hG hreg i t).symm⟩)
  · rintro (⟨i,hi⟩ | hx)
    · exact Or.inl ⟨i,hf.injective ((map_pullback_vertex S G hf hG hreg i).trans hi)⟩
    · obtain ⟨i,t,ht⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨i,t,hf.injective ((map_pullback_edge S G hf hG hreg i t).trans ht)⟩)

/-- The vertex set is the exact preimage of the ambient vertex set. -/
theorem pullback_vertices (S : SmoothManifold 2 kindX X) (G : EmbeddedGraph W)
    {f : X → Y} (hf : IsEmbedding f) (hG : G.carrier ⊆ range f)
    (hreg : ∀ i, RegularOpenEdge S (liftEdge G hf hG i)) :
    range (pullback S G hf hG hreg).vertex = f ⁻¹' range G.vertex := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i,(map_pullback_vertex S G hf hG hreg i).symm⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,hf.injective ((map_pullback_vertex S G hf hG hreg i).trans hi)⟩
end EmbeddedGraph

end GraphPullback

section CopyGermTransport
open Filter SmoothManifolds.MapData

/-- Equality of one-sided parameter germs suffices to compare ambient derivatives
at either endpoint of the actual compact parameter interval. -/
theorem deriv_eq_of_unitInterval_germs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → E) (t : unitInterval)
    (hF : DifferentiableAt ℝ F (t : ℝ)) (hG : DifferentiableAt ℝ G (t : ℝ))
    {δ : ℝ} (hδ : 0 < δ)
    (heq : ∀ q : unitInterval, |(q : ℝ) - (t : ℝ)| < δ → F q = G q) :
    deriv F (t : ℝ) = deriv G (t : ℝ) := by
  have hevent : F =ᶠ[𝓝[Icc (0 : ℝ) 1] (t : ℝ)] G := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (t : ℝ) hδ)] with s hs hst
    apply heq ⟨s, hs⟩
    simpa only [Metric.mem_ball, Real.dist_eq] using hst
  have huniq := uniqueDiffOn_Icc_zero_one (t : ℝ) t.property
  have hFG := hF.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    hevent.symm t.property
  exact (hFG.derivWithin huniq).symm.trans (hG.hasDerivAt.hasDerivWithinAt.derivWithin huniq)

/-- A forward smooth coordinate expression detects a nonzero velocity of any
ambient inverse-coordinate germ, including at endpoints. -/
theorem deriv_ne_zero_of_composition_germ
    (H K : ℝ → Plane) (B : Plane → Plane) (t : unitInterval)
    (hH : DifferentiableAt ℝ H (t : ℝ)) (hK : DifferentiableAt ℝ K (t : ℝ))
    (hB : DifferentiableAt ℝ B (K t))
    (hne : deriv H (t : ℝ) ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (heq : ∀ q : unitInterval, |(q : ℝ) - (t : ℝ)| < δ → H q = B (K q)) :
    deriv K (t : ℝ) ≠ 0 := by
  intro hzero
  have hc := hB.hasFDerivAt.comp_hasDerivAt (t : ℝ) hK.hasDerivAt
  have hd : deriv (fun s => B (K s)) (t : ℝ) = 0 := by
    change deriv (B ∘ K) (t : ℝ) = 0
    rw [hc.deriv, hzero, map_zero]
  have heqd := deriv_eq_of_unitInterval_germs H (fun s => B (K s)) t hH
    (hB.comp (t : ℝ) hK) hδ heq
  exact hne (heqd.trans hd)

/-- A regular ambient coordinate germ on the double pulls back to a regular
ambient germ in any original chart. Smoothness uses the supplied local inverse
extensions; nonzero velocity is detected by the smooth forward copy map. -/
theorem copy_regular_chart_germ
    {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool) (c : C(unitInterval, X)) (t : unitInterval)
    (e : ModelChart 2 kind X) (he : e ∈ S.smoothStructure.val) (hte : c t ∈ e.source)
    (hambient : ∀ d ∈ D.manifold.smoothStructure.val,
      P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s (c t) ∈ d.source →
      ∃ (δ : ℝ) (H : ℝ → Plane), 0 < δ ∧
        ContDiffOn ℝ ∞ H (Ioo ((t : ℝ) - δ) ((t : ℝ) + δ)) ∧
        deriv H (t : ℝ) ≠ 0 ∧
        ∀ q : unitInterval, |(q : ℝ) - (t : ℝ)| < δ →
          P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s (c q) ∈ d.source ∧
          H (q : ℝ) = coordinates d
            (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s (c q))) :
    ∃ (δ : ℝ) (K : ℝ → Plane), 0 < δ ∧
      ContDiffOn ℝ ∞ K (Ioo ((t : ℝ) - δ) ((t : ℝ) + δ)) ∧
      deriv K (t : ℝ) ≠ 0 ∧
      ∀ q : unitInterval, |(q : ℝ) - (t : ℝ)| < δ →
        c q ∈ e.source ∧ K (q : ℝ) = coordinates e (c q) := by
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  have hf : Continuous f := (D.copy_closedEmbedding s).continuous
  let p := f (c t)
  obtain ⟨O, hO, hpO, hOe, F, hFs, hFeq⟩ :=
    D.inverse_coordinate_extensions s e he (c t) hte
  obtain ⟨d, hd, hpd⟩ := D.manifold.smoothStructure.property.1.1 p
  obtain ⟨V, hV, hpV, J, hJ, hJeq⟩ := (hFs p hpO).2 d hd hpd
  obtain ⟨δH, H, hδH, hH, hHne, hHmatch⟩ := hambient d hd hpd
  let H₀ : ℝ → Euclidean 2 := fun r => toPlane.symm (H r)
  let K : ℝ → Plane := fun r => toPlane (J (H₀ r))
  have hH₀ : ContDiffOn ℝ ∞ H₀ (Ioo ((t : ℝ) - δH) ((t : ℝ) + δH)) :=
    toPlane.symm.contDiff.comp_contDiffOn hH
  have hHt : H₀ (t : ℝ) = (d p).val := by
    change toPlane.symm (H (t : ℝ)) = (d p).val
    rw [(hHmatch t (by simpa only [sub_self, abs_zero] using hδH)).2]
    exact toPlane.symm_apply_apply _
  let N := Ioo ((t : ℝ) - δH) ((t : ℝ) + δH) ∩ H₀ ⁻¹' V
  have hN : IsOpen N := hH₀.continuousOn.isOpen_inter_preimage isOpen_Ioo hV
  have htN : (t : ℝ) ∈ N := by
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    change H₀ (t : ℝ) ∈ V
    rw [hHt]
    exact hpV
  have hK : ContDiffOn ℝ ∞ K N :=
    toPlane.contDiff.comp_contDiffOn
      (hJ.comp (hH₀.mono inter_subset_left) (fun _ hx => hx.2))
  obtain ⟨δK, hδK, hKball⟩ := Metric.isOpen_iff.mp hN (t : ℝ) htN
  have hKdiff := (hK.contDiffAt (hN.mem_nhds htN)).differentiableAt
    (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)
  have hct : ContinuousAt (fun q : unitInterval => f (c q)) t :=
    hf.continuousAt.comp c.continuous.continuousAt
  have hJnear := hct.eventually hJeq
  have hOnear := hct.eventually (hO.mem_nhds hpO)
  obtain ⟨δI, hδI, hI⟩ := Metric.mem_nhds_iff.mp (hJnear.and hOnear)
  have hKmatch : ∀ q : unitInterval, |(q : ℝ) - (t : ℝ)| < min δH δI →
      c q ∈ e.source ∧ K (q : ℝ) = coordinates e (c q) := by
    intro q hq
    have hqI : dist q t < δI := by
      rw [Subtype.dist_eq, Real.dist_eq]
      exact hq.trans_le (min_le_right _ _)
    obtain ⟨hqJ, hqO⟩ := hI hqI
    refine ⟨hOe hqO, ?_⟩
    change toPlane (J (toPlane.symm (H (q : ℝ)))) = toPlane (e (c q)).val
    rw [(hHmatch q (hq.trans_le (min_le_left _ _))).2]
    simp only [coordinates, toPlane.symm_apply_apply]
    exact congrArg toPlane (hqJ.trans (hFeq (c q) hqO))
  have hKt : K (t : ℝ) = coordinates e (c t) :=
    (hKmatch t (by simpa only [sub_self, abs_zero] using lt_min hδH hδI)).2
  obtain ⟨W, hW, hpW, L, hL, hLeq⟩ :=
    ((D.copy_smooth s) (c t)).2 e he d hd hte hpd
  have hLnear := c.continuous.continuousAt.eventually hLeq
  obtain ⟨δL, hδL, hLnear'⟩ := Metric.mem_nhds_iff.mp hLnear
  let B : Plane → Plane := fun z => toPlane (L (toPlane.symm z))
  have hBdiff : DifferentiableAt ℝ B (K (t : ℝ)) := by
    have hLdiff := (hL.contDiffAt (hW.mem_nhds hpW)).differentiableAt
      (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)
    have harg : toPlane.symm (K (t : ℝ)) = (e (c t)).val := by
      rw [hKt]
      exact toPlane.symm_apply_apply _
    have hinner := toPlane.symm.differentiableAt (x := K (t : ℝ))
    have hcomp : DifferentiableAt ℝ (fun z => L (toPlane.symm z)) (K (t : ℝ)) := by
      apply DifferentiableAt.comp (K (t : ℝ)) _ hinner
      rwa [harg]
    exact toPlane.differentiableAt.comp _ hcomp
  have hKne : deriv K (t : ℝ) ≠ 0 := by
    apply deriv_ne_zero_of_composition_germ H K B t
      ((hH.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).differentiableAt
        (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)) hKdiff hBdiff hHne
      (lt_min (lt_min hδH hδI) hδL)
    intro q hq
    have hqL : dist q t < δL := by
      rw [Subtype.dist_eq, Real.dist_eq]
      exact hq.trans_le (min_le_right _ _)
    change H (q : ℝ) = toPlane (L (toPlane.symm (K (q : ℝ))))
    rw [(hKmatch q (hq.trans_le (min_le_left _ _))).2]
    simp only [coordinates, toPlane.symm_apply_apply]
    exact (hHmatch q
      ((hq.trans_le (min_le_left _ _)).trans_le (min_le_left _ _))).2.trans
      (congrArg toPlane (hLnear' hqL)).symm
  refine ⟨min δK (min δH δI), K, lt_min hδK (lt_min hδH hδI),
    hK.mono ?_, hKne, ?_⟩
  · intro r hr
    apply hKball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left δK (min δH δI), hr.1, hr.2]
  · intro q hq
    exact hKmatch q (hq.trans_le (min_le_right _ _))


end CopyGermTransport

namespace Components
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

/-- The canonical component map induced by the actual map on a pullback set. -/
def pullbackMap (hf : Continuous f) (U : Set Y) :
    ConnectedComponents (f ⁻¹' U) → ConnectedComponents U := by
  let g : (f ⁻¹' U) → U := fun x => ⟨f x, x.property⟩
  have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk
    (fun x : f ⁻¹' U => x.property)
  exact hg.connectedComponentsMap

/-- A whole original component maps into its indicated actual ambient component. -/
theorem image_subset_pullbackMap (hf : Continuous f) (U : Set Y)
    (a : ConnectedComponents (f ⁻¹' U)) :
    f '' componentSet (f ⁻¹' U) a ⊆ componentSet U (pullbackMap hf U a) := by
  apply contains_preconnected U
    ((isConnected (f ⁻¹' U) a).isPreconnected.image f hf.continuousOn)
  · rintro y ⟨x, hx, rfl⟩
    exact subset (f ⁻¹' U) a hx
  · obtain ⟨q, hq⟩ := ConnectedComponents.surjective_coe a
    refine ⟨f q, ⟨q, ⟨q, hq, rfl⟩, rfl⟩, ?_⟩
    rw [← hq]
    unfold pullbackMap
    rw [Continuous.connectedComponentsMap_mk]
    exact ⟨_, rfl, rfl⟩

/-- The closed-cover argument proves preconnectedness of the complete preimage
of every actual ambient complementary component. -/
theorem preconnected_preimage_component_of_closed_cover
    (hf : IsClosedEmbedding f) (R G N : Set Y)
    (hR : IsClosed R) (hcover : range f ∪ R = univ) (hinter : range f ∩ R ⊆ G)
    (a : ConnectedComponents (N \ G : Set Y)) :
    IsPreconnected (f ⁻¹' componentSet (N \ G) a) := by
  apply hf.isEmbedding.isInducing.isPreconnected_image.mp
  rw [image_preimage_eq_inter_range]
  exact preconnected_inter_closed_cover hf.isClosed_range hR hcover hinter
    (isConnected (N \ G) a).isPreconnected
    (Set.disjoint_left.mpr (fun y hy hyG => (subset (N \ G) a hy).2 hyG))

/-- An original local component is the complete preimage of its actual ambient
local component. Closed-copy restriction cannot split an ambient component. -/
theorem preimage_component_eq_of_closed_cover
    (hf : IsClosedEmbedding f) (R G N : Set Y)
    (hR : IsClosed R) (hcover : range f ∪ R = univ) (hinter : range f ∩ R ⊆ G)
    (a : ConnectedComponents (f ⁻¹' (N \ G))) :
    f ⁻¹' componentSet (N \ G) (pullbackMap hf.continuous (N \ G) a) =
      componentSet (f ⁻¹' (N \ G)) a := by
  have hforward : componentSet (f ⁻¹' (N \ G)) a ⊆
      f ⁻¹' componentSet (N \ G) (pullbackMap hf.continuous (N \ G) a) := by
    intro x hx
    exact image_subset_pullbackMap hf.continuous (N \ G) a ⟨x, hx, rfl⟩
  apply Set.Subset.antisymm _ hforward
  apply contains_preconnected (f ⁻¹' (N \ G))
    (preconnected_preimage_component_of_closed_cover hf R G N hR hcover hinter _)
    (preimage_mono (subset (N \ G) _)) a
  obtain ⟨x, hx⟩ := nonempty (f ⁻¹' (N \ G)) a
  exact ⟨x, hforward hx, hx⟩

/-- Exact ambient-image correspondence, retaining the chosen copy/range. -/
theorem image_component_eq_inter_range_of_closed_cover
    (hf : IsClosedEmbedding f) (R G N : Set Y)
    (hR : IsClosed R) (hcover : range f ∪ R = univ) (hinter : range f ∩ R ⊆ G)
    (a : ConnectedComponents (f ⁻¹' (N \ G))) :
    f '' componentSet (f ⁻¹' (N \ G)) a =
      componentSet (N \ G) (pullbackMap hf.continuous (N \ G) a) ∩ range f := by
  rw [← preimage_component_eq_of_closed_cover hf R G N hR hcover hinter a,
    image_preimage_eq_inter_range]

/-- Distinct components on a closed copy stay distinct in the ambient local
complement. No signed coordinate or manifold classification is assumed. -/
theorem pullbackMap_injective_of_closed_cover
    (hf : IsClosedEmbedding f) (R G N : Set Y)
    (hR : IsClosed R) (hcover : range f ∪ R = univ) (hinter : range f ∩ R ⊆ G) :
    Function.Injective (pullbackMap hf.continuous (N \ G)) := by
  intro a b hab
  have heq : componentSet (f ⁻¹' (N \ G)) a = componentSet (f ⁻¹' (N \ G)) b := by
    rw [← preimage_component_eq_of_closed_cover hf R G N hR hcover hinter a,
      ← preimage_component_eq_of_closed_cover hf R G N hR hcover hinter b, hab]
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty (f ⁻¹' (N \ G)) a
  have hxb : x ∈ componentSet (f ⁻¹' (N \ G)) b := heq ▸ hx
  exact Set.disjoint_left.mp (disjoint _ a b hne) hx hxb


end Components

variable {X : Type u} [TopologicalSpace X]

/-- Strong regular coordinate germs descend along the actual smooth copy,
using its smooth forward map and local inverse coordinate extensions. -/
theorem copy_regularCoordinateGerms {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool) (c : C(unitInterval, X))
    (a : C(unitInterval, P202Specs.SmoothSurfaceDouble.SurfaceDouble S))
    (hcopy : ∀ t, P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s (c t) = a t)
    (ha : RegularCoordinateGerms D.manifold a) : RegularCoordinateGerms S c := by
  intro t e he hte
  apply copy_regular_chart_germ S D s c t e he hte
  simpa only [hcopy] using ha t

/-- The actual restricted arrangement is a finite embedded smooth graph on
the ORIGINAL surface, with exact carrier and edge provenance and nonzero
smooth one-sided endpoint extensions in every original chart. -/
theorem arrangement_graph {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B) :
    ∃ G : EmbeddedGraph S,
      G.carrier = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        arrangementCarrier T ∧
      intrinsicBoundary S ⊆ G.carrier ∧
      (∀ e, RegularEdgeEndpoints S (G.edge e)) ∧
      (∀ e, ∃ k : Option (Fin T.count), ∀ t : unitInterval,
        P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s (G.edge e t) ∈
          arrangementCurve B.carrier T.disk T.radius k) := by
  obtain ⟨H, hH, hends, hcurve, hgerms⟩ := arrangement_graph_on_copy S D s hB T
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  have hf : IsEmbedding f := (D.copy_closedEmbedding s).isEmbedding
  have hinside : H.carrier ⊆ range f := by
    rw [hH]
    exact inter_subset_left
  have hstrong : ∀ i, RegularCoordinateGerms S (EmbeddedGraph.liftEdge H hf hinside i) := by
    intro i
    exact copy_regularCoordinateGerms S D s (EmbeddedGraph.liftEdge H hf hinside i)
      (H.edge i) (EmbeddedGraph.map_liftEdge H hf hinside i) (hgerms i)
  let hreg := fun i => (hstrong i).regular.1
  let G := EmbeddedGraph.pullback S H hf hinside hreg
  have hcarrier : G.carrier = f ⁻¹' arrangementCarrier T := by
    rw [EmbeddedGraph.pullback_carrier S H hf hinside hreg, hH]
    ext x
    exact and_iff_right (mem_range_self x)
  refine ⟨G, hcarrier, ?_, ?_, ?_⟩
  · rw [hcarrier]
    exact intrinsicBoundary_subset_restricted_arrangement S D s hB T
  · intro i
    exact (hstrong i).regular.2
  · intro i
    obtain ⟨k, hk⟩ := hcurve i
    refine ⟨k, ?_⟩
    intro t
    change f ((EmbeddedGraph.pullback S H hf hinside hreg).edge i t) ∈ _
    have heq := EmbeddedGraph.map_pullback_edge S H hf hinside hreg i t
    exact heq.symm ▸ hk t


open P202Specs.SmoothSurfaceDouble
open P202.SmoothSurfaceDouble
open SmoothManifolds.CollarData

/-- Every seam point is approached from the interior of either labelled copy. -/
theorem seam_subset_closure_copy_sdiff_seam {kind : ModelKind}
    {S : SmoothManifold 2 kind X} (D : SmoothDouble S) (s : Bool) :
    seam (intrinsicBoundary S) ⊆
      closure (range (copy (intrinsicBoundary S) s) \ seam (intrinsicBoundary S)) := by
  rintro p ⟨x, hx, rfl⟩
  let q : intrinsicBoundary S := ⟨x, hx⟩
  let F : CollarTime → SurfaceDouble S := fun t =>
    copy (intrinsicBoundary S) s (D.collar.toHomeomorph (q, t)).val
  have hF : Continuous F := (continuous_copy _ _).comp
    (continuous_subtype_val.comp (D.collar.toHomeomorph.continuous.comp
      (continuous_const.prodMk continuous_id)))
  have hzero : timeZero ∈ closure (Ioi timeZero : Set CollarTime) := by
    rw [closure_Ioi (timeZero : CollarTime)]
    exact (show (timeZero : CollarTime) ≤ timeZero from le_rfl)
  have hsub : F '' Ioi timeZero ⊆
      range (copy (intrinsicBoundary S) s) \ seam (intrinsicBoundary S) := by
    rintro z ⟨t, ht, rfl⟩
    refine ⟨mem_range_self _, ?_⟩
    rw [copy_mem_seam, collar_mem_boundary_iff]
    exact ne_of_gt ht
  have hcl := closure_mono hsub (mem_closure_image hF.continuousAt hzero)
  change copy (intrinsicBoundary S) s (D.collar.toHomeomorph (q, timeZero)).val ∈ _ at hcl
  rw [D.collar.zero_section] at hcl
  rw [copy_boundary_eq (intrinsicBoundary S) s false q] at hcl
  exact hcl

/-- Two closed sides of a cover which both occur off their common zero set
must occupy opposite halves of a neighborhood with connected strict halves. -/
theorem closed_cover_sign_halves {L R N : Set X} (f : X → ℝ)
    (hL : IsClosed L) (hR : IsClosed R) (hcover : L ∪ R = univ)
    (hzero : ∀ x ∈ N, x ∈ L ∩ R ↔ f x = 0)
    (hneg : IsPreconnected (N ∩ {x | f x < 0}))
    (hpos : IsPreconnected (N ∩ {x | 0 < f x}))
    (hmeetL : (N ∩ (L \ R)).Nonempty)
    (hmeetR : (N ∩ (R \ L)).Nonempty) :
    ∃ σ : Bool, ∀ x ∈ N, (x ∈ L ↔ if σ then 0 ≤ f x else f x ≤ 0) := by
  have hmissneg : Disjoint (N ∩ {x | f x < 0}) (L ∩ R) :=
    Set.disjoint_left.mpr (fun x hx hz => (ne_of_lt hx.2) ((hzero x hx.1).mp hz))
  have hmisspos : Disjoint (N ∩ {x | 0 < f x}) (L ∩ R) :=
    Set.disjoint_left.mpr (fun x hx hz => (ne_of_gt hx.2) ((hzero x hx.1).mp hz))
  obtain ⟨l, hlN, hlL, hlR⟩ := hmeetL
  obtain ⟨r, hrN, hrR, hrL⟩ := hmeetR
  have hlne : f l ≠ 0 := fun h => hlR ((hzero l hlN).mpr h).2
  have hrne : f r ≠ 0 := fun h => hrL ((hzero r hrN).mpr h).1
  rcases lt_or_gt_of_ne hlne with hlneg | hlpos
  · have hnegL : N ∩ {x | f x < 0} ⊆ L :=
      preconnected_subset_closed_side hL hR hcover hneg hmissneg ⟨l, ⟨hlN, hlneg⟩, hlL⟩
    have hrpos : 0 < f r := lt_of_le_of_ne
      (le_of_not_gt (fun hrneg => hrL (hnegL ⟨hrN, hrneg⟩))) hrne.symm
    have hposR : N ∩ {x | 0 < f x} ⊆ R :=
      preconnected_subset_closed_side hR hL (by rw [union_comm]; exact hcover)
        hpos (by simpa only [inter_comm] using hmisspos) ⟨r, ⟨hrN, hrpos⟩, hrR⟩
    refine ⟨false, ?_⟩
    intro x hxN
    simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro hxL
      by_contra hn
      have hxpos : 0 < f x := lt_of_not_ge hn
      have hxR := hposR ⟨hxN, hxpos⟩
      exact (ne_of_gt hxpos) ((hzero x hxN).mp ⟨hxL, hxR⟩)
    · intro hxle
      rcases hxle.eq_or_lt with hxzero | hxneg
      · exact ((hzero x hxN).mpr hxzero).1
      · exact hnegL ⟨hxN, hxneg⟩
  · have hposL : N ∩ {x | 0 < f x} ⊆ L :=
      preconnected_subset_closed_side hL hR hcover hpos hmisspos ⟨l, ⟨hlN, hlpos⟩, hlL⟩
    have hrneg : f r < 0 := lt_of_le_of_ne
      (le_of_not_gt (fun hrpos => hrL (hposL ⟨hrN, hrpos⟩))) hrne
    have hnegR : N ∩ {x | f x < 0} ⊆ R :=
      preconnected_subset_closed_side hR hL (by rw [union_comm]; exact hcover)
        hneg (by simpa only [inter_comm] using hmissneg) ⟨r, ⟨hrN, hrneg⟩, hrR⟩
    refine ⟨true, ?_⟩
    intro x hxN
    simp only [↓reduceIte]
    constructor
    · intro hxL
      by_contra hn
      have hxneg : f x < 0 := lt_of_not_ge hn
      have hxR := hnegR ⟨hxN, hxneg⟩
      exact (ne_of_lt hxneg) ((hzero x hxN).mp ⟨hxL, hxR⟩)
    · intro hxle
      rcases hxle.eq_or_lt with hxzero | hxpos
      · exact ((hzero x hxN).mpr hxzero.symm).1
      · exact hposL ⟨hxN, hxpos⟩

namespace Arrangement
variable {W : SmoothManifold 2 .euclidean X} {K : Set X}
variable {A : Set (ModelChart 2 .euclidean X)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)
variable {p : X} {O : Set X}
variable (F : ArrangementNormalForm W B.carrier T.disk T.radius p O)

/-- Cutting a normal disk by just one coordinate axis has connected strict
halves, even when a second arrangement curve crosses the first one. -/
theorem normal_half_preconnected (a : Fin 2) (σ : Bool) :
    IsPreconnected (normalNeighborhood T F ∩
      {x | if σ then 0 < coordinates F.chart x a else coordinates F.chart x a < 0}) := by
  let H : Set Plane := Metric.ball 0 F.radius ∩
    {z | if σ then 0 < z a else z a < 0}
  have hH : Convex ℝ H := by
    apply (convex_ball (0 : Plane) F.radius).inter
    have hlinear : IsLinearMap ℝ (fun z : Plane => z a) :=
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    cases σ
    · exact convex_halfSpace_lt hlinear 0
    · exact convex_halfSpace_gt hlinear 0
  have heq : normalInverse T F '' H = normalNeighborhood T F ∩
      {x | if σ then 0 < coordinates F.chart x a else coordinates F.chart x a < 0} := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      refine ⟨⟨F.chart.map_target (normalInverse_target T F hz.1), ?_⟩, ?_⟩
      · change coordinates F.chart (normalInverse T F z) ∈ Metric.ball 0 F.radius
        simpa only [normalInverse_coordinates T F hz.1] using hz.1
      · change (if σ then 0 < coordinates F.chart (normalInverse T F z) a
          else coordinates F.chart (normalInverse T F z) a < 0)
        have hs : if σ then 0 < z a else z a < 0 := hz.2
        simpa only [normalInverse_coordinates T F hz.1] using hs
    · rintro x ⟨hxN, hxsign⟩
      refine ⟨coordinates F.chart x, ⟨hxN.2, hxsign⟩, ?_⟩
      change F.chart.symm (euclideanModelPlane.symm (euclideanModelPlane (F.chart x))) = x
      rw [Homeomorph.symm_apply_apply, F.chart.left_inv hxN.1]
  rw [← heq]
  exact hH.isPreconnected.image _ ((normalInverse_continuous T F).mono inter_subset_left)

/-- Both sides of a genuine seam normal form occupy opposite coordinate
half-disks. Accumulation of both copies at the seam rules out an entire disk
being incorrectly assigned to a single copy. -/
theorem normal_closed_cover_halves (L R : Set X)
    (hL : IsClosed L) (hR : IsClosed R) (hcover : L ∪ R = univ)
    (hinter : L ∩ R = B.carrier)
    (haccL : p ∈ closure (L \ R)) (haccR : p ∈ closure (R \ L))
    (a : Fin 2) (ha : F.axis none = some a) :
    ∃ σ : Bool, ∀ x ∈ normalNeighborhood T F,
      (x ∈ L ↔ if σ then 0 ≤ coordinates F.chart x a else coordinates F.chart x a ≤ 0) := by
  apply closed_cover_sign_halves (fun x => coordinates F.chart x a) hL hR hcover
  · intro x hx
    rw [hinter]
    change x ∈ arrangementCurve B.carrier T.disk T.radius none ↔ _
    rw [F.curve_eq none x hx.1 hx.2]
    simp only [ha, Option.some.injEq]
    exact ⟨fun ⟨b, hb, hz⟩ => hb ▸ hz, fun hz => ⟨a, rfl, hz⟩⟩
  · simpa only [Bool.false_eq_true, ↓reduceIte] using normal_half_preconnected T F a false
  · simpa only [↓reduceIte] using normal_half_preconnected T F a true
  · obtain ⟨x, hxN, hx⟩ := mem_closure_iff_nhds.mp haccL _
      ((isOpen_normalNeighborhood T F).mem_nhds (mem_normalNeighborhood T F))
    exact ⟨x, hxN, hx⟩
  · obtain ⟨x, hxN, hx⟩ := mem_closure_iff_nhds.mp haccR _
      ((isOpen_normalNeighborhood T F).mem_nhds (mem_normalNeighborhood T F))
    exact ⟨x, hxN, hx⟩

end Arrangement
/-- In a normal form based at a seam point the chosen actual copy is
precisely one closed coordinate half-ball. The sign is derived from the
topological double and its actual smooth collar. -/
theorem normal_copy_halfball {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (copy (intrinsicBoundary S) s)) A B)
    {p : SurfaceDouble S} {O : Set (SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius p O)
    (a : Fin 2) (ha : F.axis none = some a) :
    ∃ σ : Bool, ∀ x ∈ Arrangement.normalNeighborhood T F,
      (x ∈ range (copy (intrinsicBoundary S) s) ↔
        if σ then 0 ≤ coordinates F.chart x a else coordinates F.chart x a ≤ 0) := by
  let L := range (copy (intrinsicBoundary S) s)
  let R := range (copy (intrinsicBoundary S) (!s))
  have hcover : L ∪ R = univ := by
    cases s
    · exact D.copies_cover
    · simpa only [L, R, Bool.not_true, union_comm] using D.copies_cover
  have hinter : L ∩ R = seam (intrinsicBoundary S) := by
    cases s
    · exact D.copies_intersect
    · simpa only [L, R, Bool.not_true, inter_comm] using D.copies_intersect
  have hp : p ∈ seam (intrinsicBoundary S) := by
    rw [← hB]
    exact (F.active_iff none).mp (by rw [ha]; exact Option.some_ne_none a)
  have hacc (t : Bool) : p ∈ closure
      (range (copy (intrinsicBoundary S) t) \ seam (intrinsicBoundary S)) :=
    seam_subset_closure_copy_sdiff_seam D t hp
  apply Arrangement.normal_closed_cover_halves T F L R
    (D.copy_closedEmbedding s).isClosed_range
    (D.copy_closedEmbedding (!s)).isClosed_range hcover (hinter.trans hB.symm)
  · apply closure_mono _ (hacc s)
    intro x hx
    exact ⟨hx.1, fun hxR => hx.2 (hinter ▸ ⟨hx.1, hxR⟩)⟩
  · apply closure_mono _ (hacc (!s))
    intro x hx
    exact ⟨hx.1, fun hxL => hx.2 (hinter ▸ ⟨hxL, hx.1⟩)⟩
  · exact ha


namespace Arrangement
variable {W : SmoothManifold 2 .euclidean X} {K : Set X}
variable {A : Set (ModelChart 2 .euclidean X)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)
variable {p : X} {O : Set X}
variable (F : ArrangementNormalForm W B.carrier T.disk T.radius p O)

theorem preconnected_normalNeighborhood : IsPreconnected (normalNeighborhood T F) := by
  have heq : normalInverse T F '' Metric.ball (0 : Plane) F.radius = normalNeighborhood T F := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      refine ⟨F.chart.map_target (normalInverse_target T F hz), ?_⟩
      change coordinates F.chart (normalInverse T F z) ∈ Metric.ball 0 F.radius
      simpa only [normalInverse_coordinates T F hz] using hz
    · intro x hx
      refine ⟨coordinates F.chart x, hx.2, ?_⟩
      change F.chart.symm (euclideanModelPlane.symm (euclideanModelPlane (F.chart x))) = x
      rw [Homeomorph.symm_apply_apply, F.chart.left_inv hx.1]
  rw [← heq]
  exact (convex_ball (0 : Plane) F.radius).isPreconnected.image _ (normalInverse_continuous T F)
end Arrangement

/-- If the seam axis is inactive, the entire normal disk based on the copy
lies in that copy. This is the interior counterpart of normal_copy_halfball. -/
theorem normal_copy_ball {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (copy (intrinsicBoundary S) s)) A B)
    {p : X} {O : Set (SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (copy (intrinsicBoundary S) s p) O)
    (ha : F.axis none = none) :
    Arrangement.normalNeighborhood T F ⊆ range (copy (intrinsicBoundary S) s) := by
  let L := range (copy (intrinsicBoundary S) s)
  let R := range (copy (intrinsicBoundary S) (!s))
  have hcover : L ∪ R = univ := by
    cases s
    · exact D.copies_cover
    · simpa only [L, R, Bool.not_true, union_comm] using D.copies_cover
  have hinter : L ∩ R = seam (intrinsicBoundary S) := by
    cases s
    · exact D.copies_intersect
    · simpa only [L, R, Bool.not_true, inter_comm] using D.copies_intersect
  apply preconnected_subset_closed_side (D.copy_closedEmbedding s).isClosed_range
    (D.copy_closedEmbedding (!s)).isClosed_range hcover
    (Arrangement.preconnected_normalNeighborhood T F)
  · apply Set.disjoint_left.mpr
    intro x hx hxint
    have hxB : x ∈ B.carrier := by rw [hB, ← hinter]; exact hxint
    have hxaxis := (F.curve_eq none x hx.1 hx.2).mp hxB
    simp [ha] at hxaxis
  · exact ⟨_, Arrangement.mem_normalNeighborhood T F, mem_range_self p⟩

/-- Distinct actual sectors in the designated copy are distinguished by a
disk membership, including when an active seam axis bounds that copy. -/
theorem normal_copy_components_separated_by_disks {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (copy (intrinsicBoundary S) s)) A B)
    {p : SurfaceDouble S} {O : Set (SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius p O)
    (a b : ConnectedComponents (copy (intrinsicBoundary S) s ⁻¹'
      (Arrangement.normalNeighborhood T F \ arrangementCarrier T))) (hab : a ≠ b) :
    ∃ i : Fin T.count,
      ∀ x ∈ componentSet (copy (intrinsicBoundary S) s ⁻¹'
        (Arrangement.normalNeighborhood T F \ arrangementCarrier T)) a,
      ∀ y ∈ componentSet (copy (intrinsicBoundary S) s ⁻¹'
        (Arrangement.normalNeighborhood T F \ arrangementCarrier T)) b,
      ¬ (copy (intrinsicBoundary S) s x ∈ (T.disk i).openAtRadius (T.radius i) ↔
         copy (intrinsicBoundary S) s y ∈ (T.disk i).openAtRadius (T.radius i)) := by
  let f := copy (intrinsicBoundary S) s
  let R := range (copy (intrinsicBoundary S) (!s))
  let N := Arrangement.normalNeighborhood T F
  let G := arrangementCarrier T
  let U := f ⁻¹' (N \ G)
  have hf : IsClosedEmbedding f := D.copy_closedEmbedding s
  have hR : IsClosed R := (D.copy_closedEmbedding (!s)).isClosed_range
  have hcover : range f ∪ R = univ := by
    cases s
    · exact D.copies_cover
    · simpa only [f, R, Bool.not_true, union_comm] using D.copies_cover
  have hinter : range f ∩ R ⊆ G := by
    have heq : range f ∩ R = seam (intrinsicBoundary S) := by
      cases s
      · exact D.copies_intersect
      · simpa only [f, R, Bool.not_true, inter_comm] using D.copies_intersect
    rw [heq, ← hB]
    exact subset_union_left
  let φ := Components.pullbackMap hf.continuous (N \ G)
  have hinj : Function.Injective φ :=
    Components.pullbackMap_injective_of_closed_cover hf R G N hR hcover hinter
  have hab' : φ a ≠ φ b := fun h => hab (hinj h)
  obtain ⟨x, hx⟩ := Components.nonempty U a
  obtain ⟨y, hy⟩ := Components.nonempty U b
  have hx' : f x ∈ componentSet (N \ G) (φ a) :=
    Components.image_subset_pullbackMap hf.continuous (N \ G) a ⟨x, hx, rfl⟩
  have hy' : f y ∈ componentSet (N \ G) (φ b) :=
    Components.image_subset_pullbackMap hf.continuous (N \ G) b ⟨y, hy, rfl⟩
  have hxU := Components.subset U a hx
  have hyU := Components.subset U b hy
  obtain ⟨k, i, hki, hxy⟩ := Arrangement.normal_components_separated T F (φ a) (φ b) hab' hx' hy'
  cases k with
  | none =>
    obtain ⟨σ, hσ⟩ := normal_copy_halfball S D s hB T F i hki
    have hxs := (hσ (f x) hxU.1).mp (mem_range_self x)
    have hys := (hσ (f y) hyU.1).mp (mem_range_self y)
    have hxn := (Arrangement.coordinates_normalComplement T F hxU).2 i ⟨none, hki⟩
    have hyn := (Arrangement.coordinates_normalComplement T F hyU).2 i ⟨none, hki⟩
    apply False.elim
    apply hxy
    cases σ <;> simp only [Bool.false_eq_true, ↓reduceIte] at hxs hys
    · exact iff_of_true (lt_of_le_of_ne hxs hxn) (lt_of_le_of_ne hys hyn)
    · exact iff_of_false (not_lt.mpr hxs) (not_lt.mpr hys)
  | some j =>
    have hxyD : ¬ (f x ∈ (T.disk j).openAtRadius (T.radius j) ↔
        f y ∈ (T.disk j).openAtRadius (T.radius j)) := by
      rw [F.disk_sign j (f x) hxU.1.1 hxU.1.2, F.disk_sign j (f y) hyU.1.1 hyU.1.2, hki]
      exact hxy
    refine ⟨j, ?_⟩
    intro z hz w hw hzw
    have hz' : f z ∈ componentSet (N \ G) (φ a) :=
      Components.image_subset_pullbackMap hf.continuous (N \ G) a ⟨z, hz, rfl⟩
    have hw' : f w ∈ componentSet (N \ G) (φ b) :=
      Components.image_subset_pullbackMap hf.continuous (N \ G) b ⟨w, hw, rfl⟩
    apply hxyD
    exact (Arrangement.local_disk_membership_constant T F j (φ a) hx' hz').trans
      (hzw.trans (Arrangement.local_disk_membership_constant T F j (φ b) hy' hw').symm)

namespace Components
variable {X : Type u} [TopologicalSpace X]

/-- Injectivity of the actual local-to-global map gives exact occupancy, using
`N \ G` directly rather than an extensionally equal intersection. -/
theorem component_inter_sdiff_eq_of_inclusion_injective (G N : Set X)
    (hinj : Function.Injective
      (inclusion Gᶜ (fun _ hx => hx.2 : N \ G ⊆ Gᶜ)))
    (a : ConnectedComponents (N \ G : Set X)) :
    componentSet Gᶜ (inclusion Gᶜ (fun _ hx => hx.2) a) ∩ N =
      componentSet (N \ G) a := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxN⟩
    let b := ConnectedComponents.mk
      (⟨x, hxN, subset Gᶜ _ hx⟩ : (N \ G : Set X))
    have hxb : x ∈ componentSet (N \ G) b := ⟨_, rfl, rfl⟩
    have hx' := subset_inclusion Gᶜ (fun _ hz => hz.2 : N \ G ⊆ Gᶜ) b hxb
    have hab : inclusion Gᶜ (fun _ hz => hz.2 : N \ G ⊆ Gᶜ) a =
        inclusion Gᶜ (fun _ hz => hz.2 : N \ G ⊆ Gᶜ) b := by
      by_contra hne
      exact Set.disjoint_left.mp (disjoint Gᶜ _ _ hne) hx hx'
    exact hinj hab ▸ hxb
  · intro x hx
    exact ⟨subset_inclusion Gᶜ (fun _ hz => hz.2 : N \ G ⊆ Gᶜ) a hx,
      (subset (N \ G) a hx).1⟩

/-- Both exact sector clauses follow from local-to-global injectivity. The
first applies to all closure-incident global components; the second includes
existence and uniqueness of the global component occupying every local one. -/
theorem sector_occupancy_of_inclusion_injective (G N : Set X) {p : X}
    (hN : IsOpen N) (hpN : p ∈ N)
    (hinj : Function.Injective
      (inclusion Gᶜ (fun _ hx => hx.2 : N \ G ⊆ Gᶜ))) :
    (∀ c : ConnectedComponents (Gᶜ : Set X), p ∈ closure (componentSet Gᶜ c) →
      ∃ a : ConnectedComponents (N \ G : Set X),
        componentSet Gᶜ c ∩ N = componentSet (N \ G) a) ∧
    (∀ a : ConnectedComponents (N \ G : Set X),
      ∃! c : ConnectedComponents (Gᶜ : Set X),
        componentSet Gᶜ c ∩ N = componentSet (N \ G) a) := by
  constructor
  · intro c hp
    obtain ⟨x, hxN, hx⟩ := mem_closure_iff_nhds.mp hp N (hN.mem_nhds hpN)
    let a := ConnectedComponents.mk (⟨x, hxN, subset Gᶜ c hx⟩ : (N \ G : Set X))
    have hxa : x ∈ componentSet (N \ G) a := ⟨_, rfl, rfl⟩
    have hx' := subset_inclusion Gᶜ (fun _ hz => hz.2 : N \ G ⊆ Gᶜ) a hxa
    have heq : c = inclusion Gᶜ (fun _ hz => hz.2 : N \ G ⊆ Gᶜ) a := by
      by_contra hne
      exact Set.disjoint_left.mp (disjoint Gᶜ _ _ hne) hx hx'
    refine ⟨a, ?_⟩
    rw [heq]
    exact component_inter_sdiff_eq_of_inclusion_injective G N hinj a
  · intro a
    refine ⟨inclusion Gᶜ (fun _ hx => hx.2 : N \ G ⊆ Gᶜ) a,
      component_inter_sdiff_eq_of_inclusion_injective G N hinj a, ?_⟩
    intro c hc
    obtain ⟨x, hx⟩ := nonempty (N \ G) a
    have hxc : x ∈ componentSet Gᶜ c := (show x ∈ componentSet Gᶜ c ∩ N by
      rw [hc]
      exact hx).1
    have hx' := subset_inclusion Gᶜ (fun _ hz => hz.2 : N \ G ⊆ Gᶜ) a hx
    by_contra hne
    exact Set.disjoint_left.mp (disjoint Gᶜ _ _ hne) hxc hx'

end Components

/-- A graph star whose distinct actual local components have distinct disk
memberships satisfies the exact sector requirement, with any finite indexing
of the actual global complementary components. -/
theorem graphStar_sector_occupancy_of_disk_memberships {kind : ModelKind}
    {X : Type u} [TopologicalSpace X] {S : SmoothManifold 2 kind X}
    (G : EmbeddedGraph S) {p : X} (g : GraphStar G p)
    {ι : Type*} (D : ι → Set X) (hD : ∀ i, IsOpen (D i))
    (hfrontier : ∀ i, frontier (D i) ⊆ G.carrier)
    (hseparate : ∀ a b : ConnectedComponents (g.neighborhood \ G.carrier : Set X), a ≠ b →
      ∃ i, ∃ x ∈ componentSet (g.neighborhood \ G.carrier) a,
        ∃ y ∈ componentSet (g.neighborhood \ G.carrier) b,
        ¬ (x ∈ D i ↔ y ∈ D i))
    {n : ℕ} (component : Fin n ≃ ConnectedComponents (G.carrierᶜ : Set X)) :
    (∀ j, p ∈ closure (componentSet G.carrierᶜ (component j)) →
      ∃ a : ConnectedComponents (g.neighborhood \ G.carrier : Set X),
        componentSet G.carrierᶜ (component j) ∩ g.neighborhood =
          componentSet (g.neighborhood \ G.carrier) a) ∧
    (∀ a : ConnectedComponents (g.neighborhood \ G.carrier : Set X),
      ∃! j, componentSet G.carrierᶜ (component j) ∩ g.neighborhood =
        componentSet (g.neighborhood \ G.carrier) a) := by
  have hinj := Components.inclusion_injective_of_disk_memberships
    G.carrier g.neighborhood D hD hfrontier hseparate
  obtain ⟨hincident, hlocal⟩ := Components.sector_occupancy_of_inclusion_injective
    G.carrier g.neighborhood (GraphStar.isOpen_neighborhood g) (GraphStar.mem_neighborhood g) hinj
  constructor
  · intro j hp
    exact hincident (component j) hp
  · intro a
    obtain ⟨c, hc, huniq⟩ := hlocal a
    refine ⟨component.symm c, ?_, ?_⟩
    · simpa only [component.apply_symm_apply] using hc
    · intro j hj
      apply component.injective
      rw [component.apply_symm_apply]
      exact huniq (component j) hj


/-- Every actual restricted disk has its frontier in the restricted carrier. -/
theorem copy_disk_frontier_subset_carrier {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (T : TransverseDiskArrangement D.manifold
      (range (copy (intrinsicBoundary S) s)) A B) (i : Fin T.count) :
    frontier (copy (intrinsicBoundary S) s ⁻¹' (T.disk i).openAtRadius (T.radius i)) ⊆
      copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T := by
  exact ((D.copy_closedEmbedding s).continuous.frontier_preimage_subset _).trans
    (preimage_mono (Arrangement.disk_frontier_subset_carrier T i))

/-- Actual local components on the original surface cannot return through a
second sector, even at seam points. -/
theorem normal_copy_component_inclusion_injective {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (copy (intrinsicBoundary S) s)) A B)
    {p : SurfaceDouble S} {O : Set (SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius p O) :
    Function.Injective (Components.inclusion
      (copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)ᶜ
      (fun _ hx => hx.2 :
        copy (intrinsicBoundary S) s ⁻¹' Arrangement.normalNeighborhood T F \
          copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T ⊆
        (copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)ᶜ)) := by
  let f := copy (intrinsicBoundary S) s
  apply Components.inclusion_injective_of_disk_memberships
    (f ⁻¹' arrangementCarrier T) (f ⁻¹' Arrangement.normalNeighborhood T F)
    (fun i => f ⁻¹' (T.disk i).openAtRadius (T.radius i))
    (fun i => (ChartDisk.isOpen_openAtRadius _ _).preimage (D.copy_closedEmbedding s).continuous)
    (copy_disk_frontier_subset_carrier S D s T)
  intro a b hab
  obtain ⟨i, hi⟩ := normal_copy_components_separated_by_disks S D s hB T F a b hab
  obtain ⟨x, hx⟩ := Components.nonempty _ a
  obtain ⟨y, hy⟩ := Components.nonempty _ b
  exact ⟨i, x, hx, y, hy, hi x hx y hy⟩

/-- The local connected components of arbitrarily small normal neighborhoods
on the original surface satisfy both exact global-region occupancy clauses. -/
theorem normal_copy_sector_occupancy {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (copy (intrinsicBoundary S) s)) A B)
    {p : X} {O : Set (SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (copy (intrinsicBoundary S) s p) O) :
    let G := copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T
    let N := copy (intrinsicBoundary S) s ⁻¹' Arrangement.normalNeighborhood T F
    (∀ c : ConnectedComponents (Gᶜ : Set X), p ∈ closure (componentSet Gᶜ c) →
      ∃ a : ConnectedComponents (N \ G : Set X),
        componentSet Gᶜ c ∩ N = componentSet (N \ G) a) ∧
    (∀ a : ConnectedComponents (N \ G : Set X),
      ∃! c : ConnectedComponents (Gᶜ : Set X),
        componentSet Gᶜ c ∩ N = componentSet (N \ G) a) := by
  dsimp only
  exact Components.sector_occupancy_of_inclusion_injective _ _
    ((Arrangement.isOpen_normalNeighborhood T F).preimage (D.copy_closedEmbedding s).continuous)
    (Arrangement.mem_normalNeighborhood T F)
    (normal_copy_component_inclusion_injective S D s hB T F)

/-- Arbitrarily small actual neighborhoods of the restricted arrangement have
finitely many connected sectors, uniform disk separation, and exact global
component occupancy. These are conclusions for actual subset components. -/
theorem restricted_arrangement_local_sectors {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (copy (intrinsicBoundary S) s)) A B)
    (p : X) (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    let G := copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T
    ∃ N : Set X, IsOpen N ∧ p ∈ N ∧ N ⊆ O ∧
      Finite (ConnectedComponents (N \ G : Set X)) ∧
      (∀ a b : ConnectedComponents (N \ G : Set X), a ≠ b →
        ∃ i : Fin T.count,
          ∀ x ∈ componentSet (N \ G) a, ∀ y ∈ componentSet (N \ G) b,
            ¬ (copy (intrinsicBoundary S) s x ∈ (T.disk i).openAtRadius (T.radius i) ↔
               copy (intrinsicBoundary S) s y ∈ (T.disk i).openAtRadius (T.radius i))) ∧
      (∀ c : ConnectedComponents (Gᶜ : Set X), p ∈ closure (componentSet Gᶜ c) →
        ∃ a : ConnectedComponents (N \ G : Set X),
          componentSet Gᶜ c ∩ N = componentSet (N \ G) a) ∧
      (∀ a : ConnectedComponents (N \ G : Set X),
        ∃! c : ConnectedComponents (Gᶜ : Set X),
          componentSet Gᶜ c ∩ N = componentSet (N \ G) a) := by
  dsimp only
  let f := copy (intrinsicBoundary S) s
  have hf : IsClosedEmbedding f := D.copy_closedEmbedding s
  obtain ⟨U, hU, hpre⟩ := hf.isEmbedding.isInducing.isOpen_iff.mp hO
  have hfp : f p ∈ U := by change p ∈ f ⁻¹' U; rwa [hpre]
  obtain ⟨F⟩ := T.normal_forms (f p) U hU hfp
  let N := f ⁻¹' Arrangement.normalNeighborhood T F
  let G := f ⁻¹' arrangementCarrier T
  have hN : IsOpen N := (Arrangement.isOpen_normalNeighborhood T F).preimage hf.continuous
  have hpN : p ∈ N := Arrangement.mem_normalNeighborhood T F
  have hNO : N ⊆ O := by
    rw [← hpre]
    exact preimage_mono F.neighborhood_subset
  have hfin : Finite (ConnectedComponents (N \ G : Set X)) := by
    let := Arrangement.finite_local_components T F
    let R := range (copy (intrinsicBoundary S) (!s))
    have hcover : range f ∪ R = univ := by
      cases s
      · exact D.copies_cover
      · simpa only [f, R, Bool.not_true, union_comm] using D.copies_cover
    have hinter : range f ∩ R ⊆ arrangementCarrier T := by
      have heq : range f ∩ R = seam (intrinsicBoundary S) := by
        cases s
        · exact D.copies_intersect
        · simpa only [f, R, Bool.not_true, inter_comm] using D.copies_intersect
      rw [heq, ← hB]
      exact subset_union_left
    exact finite_preimage_components_of_closed_cover hf R (arrangementCarrier T) (Arrangement.normalNeighborhood T F)
      (D.copy_closedEmbedding (!s)).isClosed_range hcover hinter
  obtain ⟨hincident, hsector⟩ := normal_copy_sector_occupancy S D s hB T F
  exact ⟨N, hN, hpN, hNO, hfin,
    normal_copy_components_separated_by_disks S D s hB T F, hincident, hsector⟩

end P202.SurfaceRegionConstruction

open Filter
open SmoothManifolds.MapData

namespace P202.SurfaceRegionConstruction
/-- An actual pulled-back normal chart belongs to the original maximal atlas.
The affine formula is used in both directions, with the double's local inverse
extensions providing the inverse smooth germ even along the boundary. -/
theorem affine_copy_chart_mem {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool) (d : ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))
    (hd : d ∈ D.manifold.smoothStructure.val)
    (e : ModelChart 2 kind X) (L : Euclidean 2 ≃L[ℝ] Euclidean 2) (b : Euclidean 2)
    (hsource : ∀ x ∈ e.source,
      P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s x ∈ d.source)
    (hcoords : ∀ x ∈ e.source, (e x).val =
      L (d (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s x)).val + b) :
    e ∈ S.smoothStructure.val := by
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  have hf : Continuous f := (D.copy_closedEmbedding s).continuous
  have hmax : maximalExtension (⊤ : ℕ∞) S.smoothStructure.val = S.smoothStructure.val :=
    S.smoothStructure.property.2 _
      (SmoothManifolds.maximalExtension_isContDiffAtlas S.smoothStructure.property.1)
      (SmoothManifolds.subset_maximalExtension S.smoothStructure.property.1)
  rw [← hmax]
  intro c hc
  apply SmoothManifolds.contDiffCompatible_of_germs
  · intro x hxe hxc
    obtain ⟨U,hU,hfxU,hUc,F,hF,hFeq⟩ := D.inverse_coordinate_extensions s c hc x hxc
    have hFext := (hF (f x) hfxU).2 d hd (hsource x hxe)
    have hpre : LocalCoordinateExtension (⊤ : ℕ∞)
        (fun y => (d (f y)).val) (fun y => F (f y)) x :=
      SmoothManifolds.LocalCoordinateExtension.precomp hFext hf.continuousAt rfl
    have hFc : LocalCoordinateExtension (⊤ : ℕ∞)
        (fun y => (d (f y)).val) (fun y => (c y).val) x := by
      apply SmoothManifolds.LocalCoordinateExtension.congr hpre
      filter_upwards [hf.continuousAt.eventually (hU.mem_nhds hfxU)] with y hy
      exact hFeq y hy
    have hde : LocalCoordinateExtension (⊤ : ℕ∞)
        (fun y => (e y).val) (fun y => (d (f y)).val) x := by
      refine ⟨univ,isOpen_univ,mem_univ _,fun z => L.symm (z-b),
        (L.symm.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn,?_⟩
      filter_upwards [e.open_source.mem_nhds hxe] with y hy
      rw [hcoords y hy,add_sub_cancel_right,L.symm_apply_apply]
    exact SmoothManifolds.LocalCoordinateExtension.comp hFc hde
  · intro x hxc hxe
    have hdc : LocalCoordinateExtension (⊤ : ℕ∞)
        (fun y => (c y).val) (fun y => (d (f y)).val) x :=
      ((D.copy_smooth s) x).2 c hc d hd hxc (hsource x hxe)
    have hed : LocalCoordinateExtension (⊤ : ℕ∞)
        (fun y => (d (f y)).val) (fun y => (e y).val) x := by
      refine ⟨univ,isOpen_univ,mem_univ _,fun z => L z+b,
        (L.contDiff.add contDiff_const).contDiffOn,?_⟩
      filter_upwards [e.open_source.mem_nhds hxe] with y hy
      exact (hcoords y hy).symm
    exact SmoothManifolds.LocalCoordinateExtension.comp hed hdc
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
/-- Restrict a genuine ambient chart to a closed embedded copy whenever its
exact image is an affine half-space (or all of the Euclidean model). -/
theorem exists_affine_pullback_chart {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {kind : ModelKind} {f : X → Y} (hf : IsEmbedding f)
    (d : ModelChart 2 .euclidean Y) (L : Euclidean 2 ≃L[ℝ] Euclidean 2)
    (b : Euclidean 2) (p : X) (hp : f p ∈ d.source)
    (hside : ∀ y ∈ d.source,
      y ∈ range f ↔ L (d y).val + b ∈ modelSet 2 kind) :
    ∃ e : ModelChart 2 kind X,
      e.source = f ⁻¹' d.source ∧
      e.target = {z | (⟨L.symm (z.val-b), mem_univ _⟩ : ModelSpace 2 .euclidean) ∈ d.target} ∧
      ∀ x ∈ e.source, (e x).val = L (d (f x)).val+b := by
  let U : Set X := f ⁻¹' d.source
  let V : Set (ModelSpace 2 kind) :=
    {z | (⟨L.symm (z.val-b), mem_univ _⟩ : ModelSpace 2 .euclidean) ∈ d.target}
  have hU : IsOpen U := d.open_source.preimage hf.continuous
  have hV : IsOpen V := d.open_target.preimage
    ((L.symm.continuous.comp (continuous_subtype_val.sub continuous_const)).subtype_mk _)
  have hin (z : ModelSpace 2 kind) (hz : z ∈ V) :
      d.symm ⟨L.symm (z.val-b),mem_univ _⟩ ∈ range f := by
    apply (hside _ (d.map_target hz)).mpr
    rw [d.right_inv hz,L.apply_symm_apply,sub_add_cancel]
    exact z.property
  let H : U ≃ₜ V := {
    toFun := fun x => ⟨⟨L (d (f x)).val+b,
      (hside (f x) x.property).mp (mem_range_self x.val)⟩,by
        change (⟨L.symm ((L (d (f x)).val+b)-b),mem_univ _⟩ : ModelSpace 2 .euclidean) ∈ d.target
        simpa only [add_sub_cancel_right,L.symm_apply_apply] using d.map_source x.property⟩
    invFun := fun z => ⟨liftPoint hf _ (hin z.val z.property),by
      change f (liftPoint hf _ (hin z.val z.property)) ∈ d.source
      rw [map_liftPoint hf]
      exact d.map_target z.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply hf.injective
      dsimp only
      rw [map_liftPoint hf]
      simp only [add_sub_cancel_right,L.symm_apply_apply]
      exact d.left_inv x.property
    right_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      dsimp only
      rw [map_liftPoint hf,d.right_inv z.property,L.apply_symm_apply,sub_add_cancel]
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (L.continuous.comp
        (continuous_subtype_val.comp ((d.continuousOn.comp_continuous
          (hf.continuous.comp continuous_subtype_val) (fun x => x.property))))).add continuous_const
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply hf.continuous_iff.mpr
      have harg : Continuous (fun z : V =>
          (⟨L.symm (z.val.val-b),mem_univ _⟩ : ModelSpace 2 .euclidean)) :=
        (L.symm.continuous.comp
          ((continuous_subtype_val.comp continuous_subtype_val).sub continuous_const)).subtype_mk _
      have hc := d.symm.continuousOn.comp_continuous harg (fun z => z.property)
      exact hc.congr (fun z => (map_liftPoint hf _ _).symm) }
  let : Nonempty U := ⟨⟨p,hp⟩⟩
  let : Nonempty V := ⟨H ⟨p,hp⟩⟩
  let : Nonempty (ModelSpace 2 kind) := ⟨(H ⟨p,hp⟩).val⟩
  let e₀ := H.toOpenPartialHomeomorph.trans ((⟨V,hV⟩ : TopologicalSpace.Opens (ModelSpace 2 kind)).openPartialHomeomorphSubtypeCoe ‹Nonempty V›)
  let e := e₀.lift_openEmbedding hU.isOpenEmbedding_subtypeVal
  refine ⟨e,?_,?_,?_⟩
  · dsimp only [e]
    rw [OpenPartialHomeomorph.lift_openEmbedding_source]
    change Subtype.val '' {x : U | x ∈ univ ∧ H x ∈ univ} = U
    simp
  · dsimp only [e]
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    simp only [e₀, OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target, Set.preimage_univ, inter_univ]
    rfl
  · intro x hx
    have hxU : x ∈ U := by
      change x ∈ (e₀.lift_openEmbedding hU.isOpenEmbedding_subtypeVal).source at hx
      rw [OpenPartialHomeomorph.lift_openEmbedding_source] at hx
      obtain ⟨z,_,hz⟩ := hx
      exact hz ▸ z.property
    change (e₀.lift_openEmbedding hU.isOpenEmbedding_subtypeVal x).val = _
    have heapply := OpenPartialHomeomorph.lift_openEmbedding_apply e₀ hU.isOpenEmbedding_subtypeVal
      (x := (⟨x,hxU⟩ : U))
    exact congrArg Subtype.val heapply
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
namespace AxisRays

def direction (q : Fin 2 × Bool) : Plane :=
  if q.2 then axisTangent q.1 else -axisTangent q.1

theorem tangent_norm (a : Fin 2) : ‖axisTangent a‖ = 1 := by
  fin_cases a <;> norm_num [axisTangent, toPlane, EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem direction_norm (q : Fin 2 × Bool) : ‖direction q‖ = 1 := by
  simp only [direction]
  split_ifs <;> simp [tangent_norm]

theorem direction_injective : Function.Injective direction := by
  rintro ⟨a,s⟩ ⟨b,t⟩ h
  fin_cases a <;> fin_cases b <;> cases s <;> cases t <;>
    simp_all [direction, axisTangent, toPlane, PiLp.ext_iff, funext_iff, Fin.forall_fin_two] <;> norm_num at h

theorem axis_line_eq (z : Plane) (a : Fin 2) (hz : z a = 0) :
    z = z a.rev • axisTangent a := by
  fin_cases a <;> ext j <;> fin_cases j <;>
    simp_all [axisTangent, toPlane, Fin.rev]

theorem decompose {z : Plane} (hz : z ≠ 0) (a : Fin 2) (ha : z a = 0) :
    ∃ q : Fin 2 × Bool, q.1 = a ∧ ∃ t : ℝ, 0 < t ∧ t = ‖z‖ ∧ z = t • direction q := by
  have heq := axis_line_eq z a ha
  have hnorm : ‖z‖ = |z a.rev| := by
    conv_lhs => rw [heq]
    rw [norm_smul, tangent_norm, mul_one, Real.norm_eq_abs]
  by_cases hpos : 0 < z a.rev
  · refine ⟨(a,true),rfl,z a.rev,hpos,?_,?_⟩
    · rw [hnorm,abs_of_pos hpos]
    · simpa only [direction,↓reduceIte] using heq
  · have hneg : z a.rev < 0 := by
      apply lt_of_le_of_ne (le_of_not_gt hpos)
      intro hzero
      exact hz (by simpa only [hzero,zero_smul] using heq)
    refine ⟨(a,false),rfl,-z a.rev,neg_pos.mpr hneg,?_,?_⟩
    · rw [hnorm,abs_of_neg hneg]
    · simpa only [direction, Bool.false_eq_true,↓reduceIte,neg_smul,smul_neg,neg_neg] using heq

end AxisRays
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
/-- Exact straight axes in an actual original smooth chart form a graph star.
Admissible signed axes are selected by the elementary model inequalities. -/
theorem graphStar_of_axes {X : Type*} [TopologicalSpace X] {kind : ModelKind}
    {S : SmoothManifold 2 kind X} (G : EmbeddedGraph S) (p : X)
    (e : ModelChart 2 kind X) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (r : ℝ) (hr : 0 < r)
    (hball : ∀ z : ModelSpace 2 kind,
      toPlane z.val ∈ Metric.ball (coordinates e p) r → z ∈ e.target)
    (J : Set (Fin 2)) (P : Fin 2 × Bool → Prop)
    (hadmit : ∀ q, P q → ∀ t : ℝ, 0 < t → t < r →
      toPlane.symm (coordinates e p+t • AxisRays.direction q) ∈ modelSet 2 kind)
    (hdetect : ∀ q (t : ℝ), 0 < t → t < r →
      toPlane.symm (coordinates e p+t • AxisRays.direction q) ∈ modelSet 2 kind → P q)
    (hgraph : ∀ x ∈ e.source, coordinates e x ∈ Metric.ball (coordinates e p) r →
      (x ∈ G.carrier ↔ x = p ∨ ∃ a ∈ J, (coordinates e x-coordinates e p) a = 0)) :
    ∃ g : GraphStar G p, g.chart = e ∧ g.radius = r := by
  classical
  let I := {q : Fin 2 × Bool // q.1 ∈ J ∧ P q}
  let E : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let dir : Fin (Fintype.card I) → Plane := fun i => AxisRays.direction (E i).val
  refine ⟨{
    chart := e
    chart_mem := he
    mem_source := hp
    radius := r
    radius_pos := hr
    ball_in_target := hball
    rayCount := Fintype.card I
    direction := dir
    direction_injective := ?_
    direction_unit := fun i => AxisRays.direction_norm _
    rays_in_model := ?_
    graph_eq := ?_ },rfl,rfl⟩
  · intro i j hij
    apply E.injective
    apply Subtype.ext
    exact AxisRays.direction_injective hij
  · intro i t ht htr
    exact hadmit (E i).val (E i).property.2 t ht htr
  · intro x hx hxr
    rw [hgraph x hx hxr]
    constructor
    · rintro (hxp | ⟨a,ha,hza⟩)
      · exact Or.inl hxp
      · by_cases hxp : x = p
        · exact Or.inl hxp
        have hne : coordinates e x-coordinates e p ≠ 0 := by
          intro hz
          exact hxp (coordinates_injOn e hx hp (sub_eq_zero.mp hz))
        obtain ⟨q,hqa,t,ht,htnorm,hzt⟩ := AxisRays.decompose hne a hza
        have htr : t < r := by
          rw [htnorm]
          simpa only [Metric.mem_ball,dist_eq_norm] using hxr
        have hxformula : coordinates e x = coordinates e p+t • AxisRays.direction q := by
          rw [← hzt]
          abel
        have hP : P q := hdetect q t ht htr (by
          rw [← hxformula]
          simpa only [coordinates,toPlane.symm_apply_apply] using (e x).property)
        let qi : I := ⟨q,hqa ▸ ha,hP⟩
        refine Or.inr ⟨E.symm qi,t,ht,htr,?_⟩
        change coordinates e x = coordinates e p+t • AxisRays.direction (E (E.symm qi)).val
        rw [E.apply_symm_apply]
        exact hxformula
    · rintro (hxp | ⟨i,t,ht,htr,hxi⟩)
      · exact Or.inl hxp
      · refine Or.inr ⟨(E i).val.1,(E i).property.1,?_⟩
        rw [hxi,add_sub_cancel_left]
        change (t • AxisRays.direction (E i).val) (E i).val.1 = 0
        simp only [AxisRays.direction]
        split_ifs <;> simp [axisTangent,toPlane]
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction

theorem graphStar_of_centered_axes {X : Type*} [TopologicalSpace X] {kind : ModelKind}
    {S : SmoothManifold 2 kind X} (G : EmbeddedGraph S) (p : X)
    (e : ModelChart 2 kind X) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (hcenter : coordinates e p = 0) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z : ModelSpace 2 kind,
      toPlane z.val ∈ Metric.ball 0 r → z ∈ e.target)
    (J : Set (Fin 2))
    (hgraph : ∀ x ∈ e.source, coordinates e x ∈ Metric.ball 0 r →
      (x ∈ G.carrier ↔ x = p ∨ ∃ a ∈ J, coordinates e x a = 0)) :
    ∃ g : GraphStar G p, g.chart = e ∧ g.radius = r := by
  apply graphStar_of_axes G p e he hp r hr (by simpa only [hcenter] using hball) J
    (fun q => toPlane.symm (AxisRays.direction q) ∈ modelSet 2 kind)
  · intro q hq t ht htr
    rw [hcenter,zero_add,map_smul]
    cases kind
    · change 0 ≤ t * toPlane.symm (AxisRays.direction q) (Fin.last 1)
      exact mul_nonneg ht.le hq
    · trivial
  · intro q t ht htr hq
    rw [hcenter,zero_add,map_smul] at hq
    cases kind
    · change 0 ≤ toPlane.symm (AxisRays.direction q) (Fin.last 1)
      exact nonneg_of_mul_nonneg_right hq ht
    · trivial
  · simpa only [hcenter,sub_zero] using hgraph

theorem graphStar_of_full_ball_axes {X : Type*} [TopologicalSpace X] {kind : ModelKind}
    {S : SmoothManifold 2 kind X} (G : EmbeddedGraph S) (p : X)
    (e : ModelChart 2 kind X) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (r : ℝ) (hr : 0 < r)
    (hball : ∀ z : ModelSpace 2 kind,
      toPlane z.val ∈ Metric.ball (coordinates e p) r → z ∈ e.target)
    (hfull : ∀ z ∈ Metric.ball (coordinates e p) r, toPlane.symm z ∈ modelSet 2 kind)
    (J : Set (Fin 2))
    (hgraph : ∀ x ∈ e.source, coordinates e x ∈ Metric.ball (coordinates e p) r →
      (x ∈ G.carrier ↔ x = p ∨ ∃ a ∈ J, (coordinates e x-coordinates e p) a = 0)) :
    ∃ g : GraphStar G p, g.chart = e ∧ g.radius = r := by
  apply graphStar_of_axes G p e he hp r hr hball J (fun _ => True) _ _ hgraph
  · intro q hq t ht htr
    apply hfull
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,
      AxisRays.direction_norm,mul_one,Real.norm_eq_abs,abs_of_pos ht]
    exact htr
  · intros; trivial

namespace AxisRays

def reorient (a : Fin 2) (σ : Bool) : Euclidean 2 ≃L[ℝ] Euclidean 2 :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 2 => ℝ) (Equiv.swap a 1)).trans
    (if σ then ContinuousLinearEquiv.refl ℝ _ else ContinuousLinearEquiv.neg ℝ)

theorem reorient_last (a : Fin 2) (σ : Bool) (z : Euclidean 2) :
    reorient a σ z (Fin.last 1) = if σ then z a else -z a := by
  cases σ <;> simp [reorient,ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft]

theorem reorient_norm (a : Fin 2) (σ : Bool) (z : Euclidean 2) :
    ‖toPlane (reorient a σ z)‖ = ‖toPlane z‖ := by
  fin_cases a <;> cases σ <;>
    simp [reorient,ContinuousLinearEquiv.piCongrLeft,Equiv.piCongrLeft,toPlane,EuclideanSpace.norm_eq,
      Fin.sum_univ_two,add_comm]

end AxisRays
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction.AxisRays

theorem reorient_apply (a : Fin 2) (σ : Bool) (z : Euclidean 2) (i : Fin 2) :
    reorient a σ z i = if σ then z (Equiv.swap a 1 i) else -z (Equiv.swap a 1 i) := by
  cases σ <;> simp [reorient,ContinuousLinearEquiv.piCongrLeft,Equiv.piCongrLeft]

theorem reorient_axes (a : Fin 2) (σ : Bool) (z : Plane) (J : Set (Fin 2)) :
    (∃ i ∈ J, z i = 0) ↔
      ∃ j ∈ (Equiv.swap a 1) ⁻¹' J,
        (toPlane (reorient a σ (toPlane.symm z))) j = 0 := by
  constructor
  · rintro ⟨i,hi,hzi⟩
    refine ⟨Equiv.swap a 1 i,?_,?_⟩
    · simpa only [mem_preimage,Equiv.swap_apply_self] using hi
    · change reorient a σ (toPlane.symm z) (Equiv.swap a 1 i) = 0
      rw [reorient_apply,Equiv.swap_apply_self]
      cases σ with
      | false => change -z i = 0; simpa only [neg_eq_zero] using hzi
      | true => change z i = 0; exact hzi
  · rintro ⟨j,hj,hzj⟩
    refine ⟨Equiv.swap a 1 j,hj,?_⟩
    change reorient a σ (toPlane.symm z) j = 0 at hzj
    rw [reorient_apply] at hzj
    cases σ with
    | false => change -z (Equiv.swap a 1 j) = 0 at hzj; exact neg_eq_zero.mp hzj
    | true => change z (Equiv.swap a 1 j) = 0 at hzj; exact hzj

end P202.SurfaceRegionConstruction.AxisRays
namespace P202.SurfaceRegionConstruction
open Arrangement
/-- Construct an actual original-atlas chart from the exact normal disk on a
chosen copy and an affine model identification. Its source is the whole actual
pulled-back normal disk, and the same radius is retained. -/
theorem normal_copy_chart {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    {p : X} {O : Set (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p) O)
    (L : Euclidean 2 ≃L[ℝ] Euclidean 2) (b : Euclidean 2)
    (hL : ∀ z, ‖toPlane (L z)‖ = ‖toPlane z‖)
    (hside : ∀ y ∈ normalNeighborhood T F,
      y ∈ range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s) ↔
        L (F.chart y).val+b ∈ modelSet 2 kind) :
    ∃ e : ModelChart 2 kind X,
      e ∈ S.smoothStructure.val ∧
      e.source = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        normalNeighborhood T F ∧
      p ∈ e.source ∧ coordinates e p = toPlane b ∧
      (∀ z : ModelSpace 2 kind,
        toPlane z.val ∈ Metric.ball (toPlane b) F.radius → z ∈ e.target) ∧
      (∀ x ∈ e.source, (e x).val =
        L (F.chart (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s x)).val+b) ∧
      (∀ x ∈ e.source, coordinates e x ∈ Metric.ball (toPlane b) F.radius) := by
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  let N := normalNeighborhood T F
  have hN : IsOpen N := isOpen_normalNeighborhood T F
  have hpN : f p ∈ N := mem_normalNeighborhood T F
  let d := F.chart.restr N
  have hd : d.source = N := by
    rw [OpenPartialHomeomorph.restr_source' _ _ hN]
    exact inter_eq_self_of_subset_right inter_subset_left
  have hLd : ∀ y ∈ d.source, y ∈ range f ↔ L (d y).val+b ∈ modelSet 2 kind := by
    intro y hy
    have hyN : y ∈ N := by rwa [hd] at hy
    exact hside y hyN
  obtain ⟨e,hes,het,hecoords⟩ := exists_affine_pullback_chart
    (D.copy_closedEmbedding s).isEmbedding d L b p (hd ▸ hpN) hLd
  have hesN : e.source = f ⁻¹' N := by rw [hes,hd]
  have hep : p ∈ e.source := by rw [hesN]; exact hpN
  have hcoords : ∀ x ∈ e.source, (e x).val = L (F.chart (f x)).val+b := hecoords
  have hemem : e ∈ S.smoothStructure.val :=
    affine_copy_chart_mem S D s F.chart F.chart_mem e L b
      (fun x hx => (show f x ∈ N from (Set.ext_iff.mp hesN x).mp hx).1) hcoords
  have hecenter : coordinates e p = toPlane b := by
    change toPlane (e p).val = toPlane b
    rw [hcoords p hep]
    have hzero : (F.chart (f p)).val = 0 := toPlane.injective F.centered
    rw [hzero,map_zero,zero_add]
  have hLinv : ∀ z, ‖toPlane (L.symm z)‖ = ‖toPlane z‖ := by
    intro z
    simpa only [L.apply_symm_apply] using (hL (L.symm z)).symm
  have hball : ∀ z : ModelSpace 2 kind,
      toPlane z.val ∈ Metric.ball (toPlane b) F.radius → z ∈ e.target := by
    intro z hz
    rw [het]
    let w : ModelSpace 2 .euclidean := ⟨L.symm (z.val-b),mem_univ _⟩
    have hwball : toPlane w.val ∈ Metric.ball (0 : Plane) F.radius := by
      change ‖toPlane (L.symm (z.val-b))-0‖ < F.radius
      rw [sub_zero,hLinv,map_sub]
      simpa only [Metric.mem_ball,dist_eq_norm] using hz
    have hwt : w ∈ F.chart.target := F.ball_in_target w hwball
    change w ∈ d.target
    change w ∈ F.chart.target ∧ F.chart.symm w ∈ interior N
    refine ⟨hwt,?_⟩
    rw [hN.interior_eq]
    refine ⟨F.chart.map_target hwt,?_⟩
    change coordinates F.chart (F.chart.symm w) ∈ Metric.ball 0 F.radius
    change toPlane (F.chart (F.chart.symm w)).val ∈ Metric.ball 0 F.radius
    rw [F.chart.right_inv hwt]
    exact hwball
  refine ⟨e,hemem,hesN,hep,hecenter,hball,hcoords,?_⟩
  intro x hx
  have hxN : f x ∈ N := (Set.ext_iff.mp hesN x).mp hx
  change ‖coordinates e x-toPlane b‖ < F.radius
  change ‖toPlane (e x).val-toPlane b‖ < F.radius
  rw [hcoords x hx,map_add,add_sub_cancel_right,hL]
  have hxball : coordinates F.chart (f x) ∈ Metric.ball 0 F.radius := hxN.2
  simpa only [Metric.mem_ball,dist_eq_norm,sub_zero,coordinates] using hxball
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement
/-- An affine signed-permutation identification of the chosen copy turns an
ambient arrangement normal disk into an exact actual original graph star. -/
theorem normal_copy_graphStar_of_affine {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (G : EmbeddedGraph S)
    (hcarrier : G.carrier = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
      arrangementCarrier T)
    {p : X} (hpG : p ∈ G.carrier) {O : Set (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p) O)
    (L : Euclidean 2 ≃L[ℝ] Euclidean 2) (b : Euclidean 2)
    (hL : ∀ z, ‖toPlane (L z)‖ = ‖toPlane z‖)
    (hside : ∀ y ∈ normalNeighborhood T F,
      y ∈ range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s) ↔
        L (F.chart y).val+b ∈ modelSet 2 kind)
    (J : Set (Fin 2))
    (haxes : ∀ z : Plane, (∃ a ∈ activeAxes T F, z a = 0) ↔
      ∃ a ∈ J, (toPlane (L (toPlane.symm z))) a = 0)
    (hmodel : toPlane b = 0 ∨ ∀ z ∈ Metric.ball (toPlane b) F.radius,
      toPlane.symm z ∈ modelSet 2 kind) :
    ∃ g : GraphStar G p, g.neighborhood =
      P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' normalNeighborhood T F := by
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  obtain ⟨e,he,hes,hep,hecenter,heball,hecoords,hebound⟩ :=
    normal_copy_chart S D s T F L b hL hside
  have hgraph : ∀ x ∈ e.source,
      coordinates e x ∈ Metric.ball (coordinates e p) F.radius →
      (x ∈ G.carrier ↔ x = p ∨ ∃ a ∈ J, (coordinates e x-coordinates e p) a = 0) := by
    intro x hx hxb
    have hxN : f x ∈ normalNeighborhood T F := (Set.ext_iff.mp hes x).mp hx
    have hcoord : coordinates e x-coordinates e p =
        toPlane (L (toPlane.symm (coordinates F.chart (f x)))) := by
      change toPlane (e x).val-coordinates e p = _
      rw [hecoords x hx,hecenter,map_add,add_sub_cancel_right]
      simp only [coordinates,toPlane.symm_apply_apply]
      rfl
    have hiff : x ∈ G.carrier ↔ ∃ a ∈ J, (coordinates e x-coordinates e p) a = 0 := by
      rw [hcarrier]
      change f x ∈ arrangementCarrier T ↔ _
      rw [carrier_iff_axis T F hxN,haxes,hcoord]
    constructor
    · intro hxG
      exact Or.inr (hiff.mp hxG)
    · rintro (rfl | hxaxes)
      · exact hpG
      · exact hiff.mpr hxaxes
  have hex : ∃ g : GraphStar G p, g.chart = e ∧ g.radius = F.radius := by
    rcases hmodel with hzero | hfull
    · have hcenter : coordinates e p = 0 := hecenter.trans hzero
      apply graphStar_of_centered_axes G p e he hep hcenter F.radius F.radius_pos
        (by simpa only [hzero] using heball) J
      simpa only [hcenter,sub_zero] using hgraph
    · exact graphStar_of_full_ball_axes G p e he hep F.radius F.radius_pos
        (by simpa only [hecenter] using heball)
        (by simpa only [hecenter] using hfull) J hgraph
  obtain ⟨g,hge,hgr⟩ := hex
  refine ⟨g,?_⟩
  change g.chart.source ∩ coordinates g.chart ⁻¹'
    Metric.ball (coordinates g.chart p) g.radius = _
  rw [hge,hgr,hecenter]
  ext x
  constructor
  · intro hx
    exact (Set.ext_iff.mp hes x).mp hx.1
  · intro hx
    have hxe : x ∈ e.source := (Set.ext_iff.mp hes x).mpr hx
    exact ⟨hxe,hebound x hxe⟩
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement
/-- Exact original half-disk graph stars at all seam points, with the whole
original normal neighborhood retained and the chart in the original atlas. -/
theorem normal_copy_graphStar_seam {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold 2 .halfSpace X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (G : EmbeddedGraph S)
    (hcarrier : G.carrier = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
      arrangementCarrier T)
    {p : X} (hpG : p ∈ G.carrier) {O : Set (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p) O)
    (a : Fin 2) (ha : F.axis none = some a) :
    ∃ g : GraphStar G p, g.neighborhood =
      P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' normalNeighborhood T F := by
  obtain ⟨σ,hσ⟩ := normal_copy_halfball S D s hB T F a ha
  apply normal_copy_graphStar_of_affine S D s T G hcarrier hpG F
    (AxisRays.reorient a σ) 0 (AxisRays.reorient_norm a σ) _
    ((Equiv.swap a 1) ⁻¹' activeAxes T F)
    (fun z => AxisRays.reorient_axes a σ z (activeAxes T F))
    (Or.inl (map_zero _))
  intro y hy
  rw [hσ y hy]
  change (if σ then 0 ≤ coordinates F.chart y a else coordinates F.chart y a ≤ 0) ↔
    0 ≤ (AxisRays.reorient a σ (F.chart y).val+0) (Fin.last 1)
  rw [add_zero,AxisRays.reorient_last]
  cases σ <;> simp only [Bool.false_eq_true,↓reduceIte,neg_nonneg]
  all_goals rfl
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction.AxisRays

def interiorCenter (kind : ModelKind) (r : ℝ) : Euclidean 2 :=
  match kind with
  | .halfSpace => fun _ => 2*r
  | .euclidean => 0

theorem interiorCenter_ball (kind : ModelKind) (r : ℝ) (hr : 0 < r)
    (z : Plane) (hz : z ∈ Metric.ball (toPlane (interiorCenter kind r)) r) :
    toPlane.symm z ∈ modelSet 2 kind := by
  cases kind with
  | euclidean => trivial
  | halfSpace =>
    have hb := PiLp.norm_apply_le (z-toPlane (interiorCenter .halfSpace r)) (Fin.last 1)
    have hz' : ‖z-toPlane (interiorCenter .halfSpace r)‖ < r := hz
    have hs : |z (Fin.last 1)-2*r| < r := by
      have hlt := lt_of_le_of_lt hb hz'
      change ‖z (Fin.last 1)-2*r‖ < r at hlt
      simpa only [Real.norm_eq_abs] using hlt
    change 0 ≤ z (Fin.last 1)
    have := (abs_lt.mp hs).1
    linarith
end P202.SurfaceRegionConstruction.AxisRays

namespace P202.SurfaceRegionConstruction
open Arrangement
/-- Inactive-seam normal disks give actual interior graph stars, including
interior points in a surface represented by the half-space model. -/
theorem normal_copy_graphStar_interior {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (G : EmbeddedGraph S)
    (hcarrier : G.carrier = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
      arrangementCarrier T)
    {p : X} (hpG : p ∈ G.carrier) {O : Set (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p) O)
    (ha : F.axis none = none) :
    ∃ g : GraphStar G p, g.neighborhood =
      P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' normalNeighborhood T F := by
  let b := AxisRays.interiorCenter kind F.radius
  have hfull := AxisRays.interiorCenter_ball kind F.radius F.radius_pos
  have hcopy := normal_copy_ball S D s hB T F ha
  apply normal_copy_graphStar_of_affine S D s T G hcarrier hpG F
    (ContinuousLinearEquiv.refl ℝ _) b (fun _ => rfl) _
    (activeAxes T F) (fun z => by simp only [ContinuousLinearEquiv.refl_apply,toPlane.apply_symm_apply])
    (Or.inr hfull)
  intro y hy
  constructor
  · intro _
    apply hfull (toPlane ((F.chart y).val+b))
    rw [map_add,Metric.mem_ball,dist_eq_norm,add_sub_cancel_right]
    have hyball : coordinates F.chart y ∈ Metric.ball 0 F.radius := hy.2
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero,coordinates] using hyball
  · intro _
    exact hcopy hy
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement
/-- The actual restricted arrangement has an original-atlas graph star for
every ambient normal disk, in either original model and including the seam. -/
theorem normal_copy_graphStar {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (G : EmbeddedGraph S)
    (hcarrier : G.carrier = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
      arrangementCarrier T)
    {p : X} (hpG : p ∈ G.carrier) {O : Set (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p) O) :
    ∃ g : GraphStar G p, g.neighborhood =
      P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' normalNeighborhood T F := by
  cases ha : F.axis none with
  | none => exact normal_copy_graphStar_interior S D s hB T G hcarrier hpG F ha
  | some a =>
    cases kind with
    | halfSpace => exact normal_copy_graphStar_seam S D s hB T G hcarrier hpG F a ha
    | euclidean =>
      have hpB := (F.active_iff none).mp (by rw [ha]; exact Option.some_ne_none a)
      change P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p ∈ B.carrier at hpB
      rw [hB] at hpB
      obtain ⟨q,hq,_⟩ := hpB
      have hbempty : intrinsicBoundary S = ∅ := SmoothManifolds.intrinsicBoundary_euclidean S
      have : q ∈ (∅ : Set X) := hbempty ▸ hq
      exact this.elim

/-- Arbitrarily small actual original-atlas stars on the extracted graph.
The normal form chosen in the double is pulled back exactly, so its genuine
sector-component correspondence is preserved. -/
theorem arrangement_graph_stars {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (G : EmbeddedGraph S)
    (hcarrier : G.carrier = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
      arrangementCarrier T)
    (p : X) (hpG : p ∈ G.carrier) (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ g : GraphStar G p, g.neighborhood ⊆ O := by
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  let U := (f '' Oᶜ)ᶜ
  have hU : IsOpen U := ((D.copy_closedEmbedding s).isClosedMap _ hO.isClosed_compl).isOpen_compl
  have hfp : f p ∈ U := by
    rintro ⟨q,hq,hqp⟩
    exact hq ((D.copy_closedEmbedding s).injective hqp ▸ hpO)
  obtain ⟨F⟩ := T.normal_forms (f p) U hU hfp
  obtain ⟨g,hg⟩ := normal_copy_graphStar S D s hB T G hcarrier hpG F
  refine ⟨g,?_⟩
  rw [hg]
  intro x hx
  have hfxU : f x ∈ U := F.neighborhood_subset hx
  by_contra hxO
  exact hfxU ⟨x,hxO,rfl⟩
end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction
variable {X : Type u} [TopologicalSpace X]

open P202Specs.SmoothSurfaceDouble

/-- The complete local-sector conclusion for the actual original graph:
arbitrarily small original smooth stars, disk separation, and both exact
occupancy statements. In particular seam sectors cannot return globally. -/
theorem arrangement_graph_star_sectors {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (copy (intrinsicBoundary S) s)) A B)
    (G : EmbeddedGraph S)
    (hcarrier : G.carrier = copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)
    (p : X) (hpG : p ∈ G.carrier) (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ g : GraphStar G p, g.neighborhood ⊆ O ∧
      (∀ a b : ConnectedComponents (g.neighborhood \ G.carrier : Set X), a ≠ b →
        ∃ i : Fin T.count,
          ∀ x ∈ componentSet (g.neighborhood \ G.carrier) a,
          ∀ y ∈ componentSet (g.neighborhood \ G.carrier) b,
            ¬ (copy (intrinsicBoundary S) s x ∈ (T.disk i).openAtRadius (T.radius i) ↔
               copy (intrinsicBoundary S) s y ∈ (T.disk i).openAtRadius (T.radius i))) ∧
      (∀ c : ConnectedComponents (G.carrierᶜ : Set X), p ∈ closure (componentSet G.carrierᶜ c) →
        ∃ a : ConnectedComponents (g.neighborhood \ G.carrier : Set X),
          componentSet G.carrierᶜ c ∩ g.neighborhood =
            componentSet (g.neighborhood \ G.carrier) a) ∧
      (∀ a : ConnectedComponents (g.neighborhood \ G.carrier : Set X),
        ∃! c : ConnectedComponents (G.carrierᶜ : Set X),
          componentSet G.carrierᶜ c ∩ g.neighborhood =
            componentSet (g.neighborhood \ G.carrier) a) := by
  let f := copy (intrinsicBoundary S) s
  have hf : IsClosedEmbedding f := D.copy_closedEmbedding s
  obtain ⟨U, hU, hpre⟩ := hf.isEmbedding.isInducing.isOpen_iff.mp hO
  have hfp : f p ∈ U := by change p ∈ f ⁻¹' U; rwa [hpre]
  obtain ⟨F⟩ := T.normal_forms (f p) U hU hfp
  obtain ⟨g, hg⟩ := normal_copy_graphStar S D s hB T G hcarrier hpG F
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [hg, ← hpre]
    exact preimage_mono F.neighborhood_subset
  · rw [hg, hcarrier]
    exact normal_copy_components_separated_by_disks S D s hB T F
  · rw [hg, hcarrier]
    exact normal_copy_sector_occupancy S D s hB T F
end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction
open P202Specs.SmoothSurfaceDouble
variable {X : Type u} [TopologicalSpace X]

/-- Completed graph-and-sector stage of extraction, with no regional boundary
cycle or planar-domain certificate assumed. All sets and sectors are actual
components of the restricted arrangement on the original surface. -/
theorem arrangement_graph_geometry {kind : ModelKind} [CompactSpace X]
    (S : SmoothManifold 2 kind X) (D : SmoothDouble S) (s : Bool)
    {A : Set (ModelChart 2 .euclidean (SurfaceDouble S))}
    (hsubordinate : CopySubordinate S D s A)
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (copy (intrinsicBoundary S) s)) A B) :
    ∃ G : EmbeddedGraph S,
      G.carrier = copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T ∧
      intrinsicBoundary S ⊆ G.carrier ∧
      (∀ i, RegularEdgeEndpoints S (G.edge i)) ∧
      (∀ i, ∃ k : Option (Fin T.count), ∀ t : unitInterval,
        copy (intrinsicBoundary S) s (G.edge i t) ∈ arrangementCurve B.carrier T.disk T.radius k) ∧
      Finite (ConnectedComponents (G.carrierᶜ : Set X)) ∧
      (∀ a : ConnectedComponents (G.carrierᶜ : Set X),
        ∃ (i : Fin T.count) (e : ModelChart 2 kind X), e ∈ S.smoothStructure.val ∧
          componentSet G.carrierᶜ a ⊆ copy (intrinsicBoundary S) s ⁻¹'
            (T.disk i).openAtRadius (T.radius i) ∧
          closure (componentSet G.carrierᶜ a) ⊆ copy (intrinsicBoundary S) s ⁻¹'
            (T.disk i).closedAtRadius (T.radius i) ∧
          closure (componentSet G.carrierᶜ a) ⊆ e.source) ∧
      (∀ p ∈ G.carrier, ∀ O : Set X, IsOpen O → p ∈ O →
        ∃ g : GraphStar G p, g.neighborhood ⊆ O ∧
          (∀ a b : ConnectedComponents (g.neighborhood \ G.carrier : Set X), a ≠ b →
            ∃ i : Fin T.count,
              ∀ x ∈ componentSet (g.neighborhood \ G.carrier) a,
              ∀ y ∈ componentSet (g.neighborhood \ G.carrier) b,
                ¬ (copy (intrinsicBoundary S) s x ∈ (T.disk i).openAtRadius (T.radius i) ↔
                   copy (intrinsicBoundary S) s y ∈ (T.disk i).openAtRadius (T.radius i))) ∧
          (∀ c : ConnectedComponents (G.carrierᶜ : Set X), p ∈ closure (componentSet G.carrierᶜ c) →
            ∃ a : ConnectedComponents (g.neighborhood \ G.carrier : Set X),
              componentSet G.carrierᶜ c ∩ g.neighborhood =
                componentSet (g.neighborhood \ G.carrier) a) ∧
          (∀ a : ConnectedComponents (g.neighborhood \ G.carrier : Set X),
            ∃! c : ConnectedComponents (G.carrierᶜ : Set X),
              componentSet G.carrierᶜ c ∩ g.neighborhood =
                componentSet (g.neighborhood \ G.carrier) a)) := by
  obtain ⟨G, hcarrier, hboundary, hendpoints, hcurve⟩ := arrangement_graph S D s hB T
  refine ⟨G, hcarrier, hboundary, hendpoints, hcurve, ?_, ?_, ?_⟩
  · rw [hcarrier]
    exact finite_arrangement_components S D s hB T
  · rw [hcarrier]
    exact arrangement_component_in_original_chart S D s hsubordinate T
  · exact arrangement_graph_star_sectors S D s hB T G hcarrier
end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction.Components
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- A component of a complement in a closed two-copy cover which meets one
copy lies wholly in that copy. Thus its lifted component maps onto the ENTIRE
ambient component, rather than just its intersection with the copy range. -/
theorem image_component_eq_of_closed_cover
    (hf : IsClosedEmbedding f) (R G N : Set Y)
    (hR : IsClosed R) (hcover : range f ∪ R = univ) (hinter : range f ∩ R ⊆ G)
    (a : ConnectedComponents (f ⁻¹' (N \ G))) :
    f '' componentSet (f ⁻¹' (N \ G)) a =
      componentSet (N \ G) (pullbackMap hf.continuous (N \ G) a) := by
  rw [image_component_eq_inter_range_of_closed_cover hf R G N hR hcover hinter a]
  apply inter_eq_left.mpr
  apply preconnected_subset_closed_side hf.isClosed_range hR hcover
    (isConnected (N \ G) _).isPreconnected
  · exact Set.disjoint_left.mpr (fun y hy hyint => (subset (N \ G) _ hy).2 (hinter hyint))
  · obtain ⟨x, hx⟩ := nonempty (f ⁻¹' (N \ G)) a
    exact ⟨f x, image_subset_pullbackMap hf.continuous (N \ G) a ⟨x, hx, rfl⟩, mem_range_self x⟩
end P202.SurfaceRegionConstruction.Components

namespace P202.SurfaceRegionConstruction.PlaneSectors
def signedOrthant (A : Set (Fin 2)) (s : Fin 2 → Bool) : Set Plane :=
  {x | ∀ i ∈ A, if s i then 0 < x i else x i < 0}


end P202.SurfaceRegionConstruction.PlaneSectors

namespace P202.SurfaceRegionConstruction.Arrangement
variable {Y : Type*} [TopologicalSpace Y]
variable {W : SmoothManifold 2 .euclidean Y} {K : Set Y}
variable {A : Set (ModelChart 2 .euclidean Y)} {B : CompactSmoothSeam W}
variable (T : TransverseDiskArrangement W K A B)
variable {p : Y} {O : Set Y}
variable (F : ArrangementNormalForm W B.carrier T.disk T.radius p O)

/-- The full coordinate image of an actual ambient normal complementary
component is exactly one whole full-plane sign chamber. -/
theorem coordinates_component_eq_chamber
    (a : ConnectedComponents (normalNeighborhood T F \ arrangementCarrier T : Set Y))
    {x : Y} (hx : x ∈ componentSet (normalNeighborhood T F \ arrangementCarrier T) a) :
    coordinates F.chart '' componentSet (normalNeighborhood T F \ arrangementCarrier T) a =
      NormalSectors.chamber (activeAxes T F) F.radius
        (fun i => decide (0 < coordinates F.chart x i)) := by
  rw [component_eq_normalChamber T F a hx]
  change coordinates F.chart ''
    (normalInverse T F '' NormalSectors.chamber (activeAxes T F) F.radius _) = _
  rw [image_image]
  ext z
  constructor
  · rintro ⟨w,hw,hweq⟩
    change coordinates F.chart (normalInverse T F w) = z at hweq
    rw [normalInverse_coordinates T F hw.1] at hweq
    exact hweq ▸ hw
  · intro hz
    exact ⟨z,hz,normalInverse_coordinates T F hz.1⟩

end P202.SurfaceRegionConstruction.Arrangement
namespace P202.SurfaceRegionConstruction
open Arrangement

/-- Every actual selected-copy local component has the full ambient chamber
as its coordinate image; at the seam the whole chamber lies on the copy's
chosen side. The image equality is in the unrestricted plane. -/
theorem normal_copy_component_coordinates
    {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    {p : X} {O : Set (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p) O)
    (a : ConnectedComponents (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
      (normalNeighborhood T F \ arrangementCarrier T))) :
    ∃ σ : Fin 2 → Bool,
      (fun x => coordinates F.chart (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s x)) ''
        componentSet (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
          (normalNeighborhood T F \ arrangementCarrier T)) a =
        NormalSectors.chamber (activeAxes T F) F.radius σ := by
  let f := P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s
  let R := range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) (!s))
  have hcover : range f ∪ R = univ := by
    cases s
    · exact D.copies_cover
    · simpa only [f,R,Bool.not_true,union_comm] using D.copies_cover
  have hinter : range f ∩ R ⊆ arrangementCarrier T := by
    have heq : range f ∩ R = B.carrier := by
      rw [hB]
      cases s
      · exact D.copies_intersect
      · simpa only [f,R,Bool.not_true,inter_comm] using D.copies_intersect
    rw [heq]
    exact subset_union_left
  have himage := Components.image_component_eq_of_closed_cover (D.copy_closedEmbedding s)
    R (arrangementCarrier T) (normalNeighborhood T F)
    (D.copy_closedEmbedding (!s)).isClosed_range hcover hinter a
  let c := Components.pullbackMap (D.copy_closedEmbedding s).continuous
    (normalNeighborhood T F \ arrangementCarrier T) a
  obtain ⟨y,hy⟩ := Components.nonempty (normalNeighborhood T F \ arrangementCarrier T) c
  refine ⟨fun i => decide (0 < coordinates F.chart y i),?_⟩
  calc
    _ = coordinates F.chart '' (f '' componentSet (f ⁻¹'
        (normalNeighborhood T F \ arrangementCarrier T)) a) := (image_image _ _ _).symm
    _ = coordinates F.chart '' componentSet (normalNeighborhood T F \ arrangementCarrier T) c := by
      rw [himage]
    _ = _ := coordinates_component_eq_chamber T F c hy

end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement

/-- Any actual original chart with the affine normal-coordinate formula sends
an entire original local component onto the entire affine full-plane chamber. -/
theorem affine_copy_component_coordinates
    {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    {p : X} {O : Set (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p) O)
    (e : ModelChart 2 kind X) (L : Euclidean 2 ≃L[ℝ] Euclidean 2) (b : Euclidean 2)
    (hes : e.source = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
      normalNeighborhood T F)
    (hecoords : ∀ x ∈ e.source, (e x).val =
      L (F.chart (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s x)).val+b)
    (a : ConnectedComponents (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
      (normalNeighborhood T F \ arrangementCarrier T))) :
    ∃ σ : Fin 2 → Bool,
      coordinates e '' componentSet (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        (normalNeighborhood T F \ arrangementCarrier T)) a =
      (fun z : Plane => toPlane (L (toPlane.symm z)+b)) ''
        NormalSectors.chamber (activeAxes T F) F.radius σ := by
  obtain ⟨σ,hσ⟩ := normal_copy_component_coordinates S D s hB T F a
  refine ⟨σ,?_⟩
  rw [← hσ,image_image]
  apply Set.image_congr
  intro x hx
  have hxN := (Components.subset _ a hx).1
  have hxe : x ∈ e.source := (Set.ext_iff.mp hes x).mpr hxN
  change toPlane (e x).val = toPlane (L (toPlane.symm
    (toPlane (F.chart (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s x)).val))+b)
  rw [toPlane.symm_apply_apply,hecoords x hxe]

end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction
namespace PlaneSectors

lemma chamber_eq_signedOrthant_inter_ball (J : Set (Fin 2)) (r : ℝ) (σ : Fin 2 → Bool) :
    NormalSectors.chamber J r σ = signedOrthant J σ ∩ Metric.ball 0 r := by
  ext z
  simp only [NormalSectors.chamber,signedOrthant,mem_inter_iff,mem_iInter,mem_ofPred_eq]
  exact and_comm

theorem translate_chamber (J : Set (Fin 2)) (r : ℝ) (σ : Fin 2 → Bool) (b : Plane) :
    (fun z : Plane => z+b) '' NormalSectors.chamber J r σ =
      {z | z-b ∈ signedOrthant J σ} ∩ Metric.ball b r := by
  rw [chamber_eq_signedOrthant_inter_ball]
  ext z
  constructor
  · rintro ⟨w,⟨hw,hwb⟩,rfl⟩
    refine ⟨?_,?_⟩
    · change w+b-b ∈ signedOrthant J σ
      simpa only [add_sub_cancel_right] using hw
    · simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_right,sub_zero] using hwb
  · rintro ⟨hz,hzb⟩
    refine ⟨z-b,⟨hz,?_⟩,sub_add_cancel _ _⟩
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hzb

end PlaneSectors
end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction.AxisRays

def planeReorient (a : Fin 2) (ε : Bool) : Plane ≃L[ℝ] Plane :=
  (toPlane.symm.trans (reorient a ε)).trans toPlane

def reorientedSigns (a : Fin 2) (ε : Bool) (σ : Fin 2 → Bool) : Fin 2 → Bool :=
  fun j => if ε then σ (Equiv.swap a 1 j) else !(σ (Equiv.swap a 1 j))

theorem planeReorient_apply (a : Fin 2) (ε : Bool) (z : Plane) (j : Fin 2) :
    planeReorient a ε z j = if ε then z (Equiv.swap a 1 j) else -z (Equiv.swap a 1 j) := by
  change reorient a ε (toPlane.symm z) j = _
  rw [reorient_apply]
  cases ε <;> rfl

theorem planeReorient_norm (a : Fin 2) (ε : Bool) (z : Plane) :
    ‖planeReorient a ε z‖ = ‖z‖ := by
  change ‖toPlane (reorient a ε (toPlane.symm z))‖ = ‖z‖
  rw [reorient_norm,toPlane.apply_symm_apply]

theorem planeReorient_signedOrthant (a : Fin 2) (ε : Bool) (σ : Fin 2 → Bool)
    (J : Set (Fin 2)) (z : Plane) :
    planeReorient a ε z ∈ PlaneSectors.signedOrthant ((Equiv.swap a 1) ⁻¹' J)
      (reorientedSigns a ε σ) ↔ z ∈ PlaneSectors.signedOrthant J σ := by
  change (∀ j ∈ (Equiv.swap a 1) ⁻¹' J,
    if reorientedSigns a ε σ j then 0 < planeReorient a ε z j
      else planeReorient a ε z j < 0) ↔
    ∀ i ∈ J, if σ i then 0 < z i else z i < 0
  constructor
  · intro hz i hi
    have hj : Equiv.swap a 1 i ∈ (Equiv.swap a 1) ⁻¹' J := by
      simpa only [mem_preimage,Equiv.swap_apply_self] using hi
    have h := hz (Equiv.swap a 1 i) hj
    rw [planeReorient_apply,reorientedSigns,Equiv.swap_apply_self] at h
    cases ε <;> cases hσ : σ i <;> simpa only [hσ,Bool.false_eq_true,↓reduceIte,Bool.not_false,
      Bool.not_true,neg_pos,neg_lt_zero] using h
  · intro hz j hj
    have h := hz (Equiv.swap a 1 j) hj
    rw [planeReorient_apply,reorientedSigns]
    cases ε <;> cases hσ : σ (Equiv.swap a 1 j) <;>
      simpa only [hσ,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,neg_pos,neg_lt_zero] using h

theorem reorient_chamber (a : Fin 2) (ε : Bool) (J : Set (Fin 2))
    (r : ℝ) (σ : Fin 2 → Bool) :
    planeReorient a ε '' NormalSectors.chamber J r σ =
      PlaneSectors.signedOrthant ((Equiv.swap a 1) ⁻¹' J) (reorientedSigns a ε σ) ∩
        Metric.ball 0 r := by
  rw [PlaneSectors.chamber_eq_signedOrthant_inter_ball]
  ext z
  constructor
  · rintro ⟨w,⟨hw,hwball⟩,rfl⟩
    refine ⟨(planeReorient_signedOrthant a ε σ J w).mpr hw,?_⟩
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero,planeReorient_norm] using hwball
  · rintro ⟨hz,hzball⟩
    let w := (planeReorient a ε).symm z
    have hwz : planeReorient a ε w = z := (planeReorient a ε).apply_symm_apply z
    refine ⟨w,⟨?_,?_⟩,hwz⟩
    · apply (planeReorient_signedOrthant a ε σ J w).mp
      rwa [hwz]
    · have hnorm : ‖w‖ = ‖z‖ := by
        rw [← planeReorient_norm a ε w,hwz]
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero,hnorm] using hzball

end P202.SurfaceRegionConstruction.AxisRays
namespace P202.SurfaceRegionConstruction
open Arrangement

/-- Retain an actual original-atlas normal chart and the exact unrestricted
plane image of every local component as one translated signed orthant cut by
the whole normal ball. -/
theorem normal_copy_chamber_chart_of_affine
    {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    {p : X} {O : Set (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p) O)
    (L : Euclidean 2 ≃L[ℝ] Euclidean 2) (b : Euclidean 2)
    (hL : ∀ z, ‖toPlane (L z)‖ = ‖toPlane z‖)
    (hside : ∀ y ∈ normalNeighborhood T F,
      y ∈ range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s) ↔
        L (F.chart y).val+b ∈ modelSet 2 kind)
    (htransform : ∀ σ : Fin 2 → Bool, ∃ (J : Set (Fin 2)) (τ : Fin 2 → Bool),
      (fun z : Plane => toPlane (L (toPlane.symm z)+b)) ''
          NormalSectors.chamber (activeAxes T F) F.radius σ =
        {z | z-toPlane b ∈ PlaneSectors.signedOrthant J τ} ∩ Metric.ball (toPlane b) F.radius) :
    ∃ e : ModelChart 2 kind X,
      e ∈ S.smoothStructure.val ∧
      e.source = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        normalNeighborhood T F ∧ p ∈ e.source ∧
      (∀ z : ModelSpace 2 kind,
        toPlane z.val ∈ Metric.ball (coordinates e p) F.radius → z ∈ e.target) ∧
      (∀ a : ConnectedComponents (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        (normalNeighborhood T F \ arrangementCarrier T)),
        ∃ (J : Set (Fin 2)) (τ : Fin 2 → Bool),
          coordinates e '' componentSet
              (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
                (normalNeighborhood T F \ arrangementCarrier T)) a =
            {z | z-coordinates e p ∈ PlaneSectors.signedOrthant J τ} ∩
              Metric.ball (coordinates e p) F.radius) := by
  obtain ⟨e,he,hes,hep,hecenter,heball,hecoords,hebound⟩ :=
    normal_copy_chart S D s T F L b hL hside
  refine ⟨e,he,hes,hep,?_,?_⟩
  · simpa only [hecenter] using heball
  · intro a
    obtain ⟨σ,hσ⟩ := affine_copy_component_coordinates S D s hB T F e L b hes hecoords a
    obtain ⟨J,τ,hJτ⟩ := htransform σ
    refine ⟨J,τ,?_⟩
    rw [hσ,hJτ,hecenter]

end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement

/-- Exact original coordinate sign chambers at every normal neighborhood,
including all seam cases and interior half-space charts. -/
theorem normal_copy_chamber_chart
    {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    {p : X} {O : Set (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p) O) :
    ∃ e : ModelChart 2 kind X,
      e ∈ S.smoothStructure.val ∧
      e.source = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        normalNeighborhood T F ∧ p ∈ e.source ∧
      (∀ z : ModelSpace 2 kind,
        toPlane z.val ∈ Metric.ball (coordinates e p) F.radius → z ∈ e.target) ∧
      (∀ a : ConnectedComponents (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        (normalNeighborhood T F \ arrangementCarrier T)),
        ∃ (J : Set (Fin 2)) (τ : Fin 2 → Bool),
          coordinates e '' componentSet
              (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
                (normalNeighborhood T F \ arrangementCarrier T)) a =
            {z | z-coordinates e p ∈ PlaneSectors.signedOrthant J τ} ∩
              Metric.ball (coordinates e p) F.radius) := by
  cases ha : F.axis none with
  | none =>
    let b := AxisRays.interiorCenter kind F.radius
    have hfull := AxisRays.interiorCenter_ball kind F.radius F.radius_pos
    have hcopy := normal_copy_ball S D s hB T F ha
    apply normal_copy_chamber_chart_of_affine S D s hB T F
      (ContinuousLinearEquiv.refl ℝ _) b (fun _ => rfl) _ _
    · intro y hy
      constructor
      · intro _
        apply hfull (toPlane ((F.chart y).val+b))
        rw [map_add,Metric.mem_ball,dist_eq_norm,add_sub_cancel_right]
        have hyball : coordinates F.chart y ∈ Metric.ball 0 F.radius := hy.2
        simpa only [Metric.mem_ball,dist_eq_norm,sub_zero,coordinates] using hyball
      · intro _
        exact hcopy hy
    · intro σ
      refine ⟨activeAxes T F,σ,?_⟩
      simpa only [ContinuousLinearEquiv.refl_apply,map_add,toPlane.apply_symm_apply] using
        PlaneSectors.translate_chamber (activeAxes T F) F.radius σ (toPlane b)
  | some a =>
    cases kind with
    | euclidean =>
      have hpB := (F.active_iff none).mp (by rw [ha]; exact Option.some_ne_none a)
      change P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p ∈ B.carrier at hpB
      rw [hB] at hpB
      obtain ⟨q,hq,_⟩ := hpB
      have hbempty : intrinsicBoundary S = ∅ := SmoothManifolds.intrinsicBoundary_euclidean S
      have : q ∈ (∅ : Set X) := hbempty ▸ hq
      exact this.elim
    | halfSpace =>
      obtain ⟨ε,hε⟩ := normal_copy_halfball S D s hB T F a ha
      apply normal_copy_chamber_chart_of_affine S D s hB T F
        (AxisRays.reorient a ε) 0 (AxisRays.reorient_norm a ε) _ _
      · intro y hy
        rw [hε y hy]
        change (if ε then 0 ≤ coordinates F.chart y a else coordinates F.chart y a ≤ 0) ↔
          0 ≤ (AxisRays.reorient a ε (F.chart y).val+0) (Fin.last 1)
        rw [add_zero,AxisRays.reorient_last]
        cases ε <;> simp only [Bool.false_eq_true,↓reduceIte,neg_nonneg]
        all_goals rfl
      · intro σ
        refine ⟨(Equiv.swap a 1) ⁻¹' activeAxes T F,AxisRays.reorientedSigns a ε σ,?_⟩
        simp only [add_zero,map_zero,sub_zero]
        change AxisRays.planeReorient a ε '' NormalSectors.chamber (activeAxes T F) F.radius σ =
          PlaneSectors.signedOrthant ((Equiv.swap a 1) ⁻¹' activeAxes T F)
            (AxisRays.reorientedSigns a ε σ) ∩ Metric.ball 0 F.radius
        exact AxisRays.reorient_chamber a ε (activeAxes T F) F.radius σ

end P202.SurfaceRegionConstruction
namespace P202.SurfaceRegionConstruction
open Arrangement

/-- A closure-incident actual global region occupies precisely one whole
translated signed orthant in an original smooth chart, as an equality of
subsets of the unrestricted ambient plane, including at the seam. -/
theorem normal_copy_incident_chamber
    {X : Type u} [TopologicalSpace X] {kind : ModelKind}
    (S : SmoothManifold 2 kind X) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    {A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S))}
    {B : CompactSmoothSeam D.manifold}
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    {p : X} {O : Set (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)}
    (F : ArrangementNormalForm D.manifold B.carrier T.disk T.radius
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s p) O)
    (c : ConnectedComponents ((P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
      arrangementCarrier T)ᶜ : Set X))
    (hpc : p ∈ closure (componentSet
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)ᶜ c)) :
    ∃ (e : ModelChart 2 kind X) (J : Set (Fin 2)) (τ : Fin 2 → Bool),
      e ∈ S.smoothStructure.val ∧
      e.source = P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        normalNeighborhood T F ∧ p ∈ e.source ∧
      (∀ z : ModelSpace 2 kind,
        toPlane z.val ∈ Metric.ball (coordinates e p) F.radius → z ∈ e.target) ∧
      coordinates e '' (componentSet
          (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)ᶜ c ∩
            e.source) =
        {z | z-coordinates e p ∈ PlaneSectors.signedOrthant J τ} ∩
          Metric.ball (coordinates e p) F.radius ∧
      (∀ z ∈ Metric.ball (coordinates e p) F.radius,
        z-coordinates e p ∈ PlaneSectors.signedOrthant J τ →
          toPlane.symm z ∈ modelSet 2 kind) := by
  obtain ⟨e,he,hes,hep,heball,hechamber⟩ := normal_copy_chamber_chart S D s hB T F
  obtain ⟨a,ha⟩ := (normal_copy_sector_occupancy S D s hB T F).1 c hpc
  obtain ⟨J,τ,hJτ⟩ := hechamber a
  have himage : coordinates e '' (componentSet
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)ᶜ c ∩
        e.source) =
      {z | z-coordinates e p ∈ PlaneSectors.signedOrthant J τ} ∩
        Metric.ball (coordinates e p) F.radius := by
    rw [hes,ha]
    exact hJτ
  refine ⟨e,J,τ,he,hes,hep,heball,himage,?_⟩
  intro z hzball hzsign
  have hzimage : z ∈ coordinates e '' (componentSet
      (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹' arrangementCarrier T)ᶜ c ∩
        e.source) := by
    rw [himage]
    exact ⟨hzsign,hzball⟩
  obtain ⟨x,hx,rfl⟩ := hzimage
  simpa only [coordinates,toPlane.symm_apply_apply] using (e x).property

end P202.SurfaceRegionConstruction

namespace P202.SurfaceRegionConstruction

/-- Full graph-geometry stage, with actual interval edges, original-chart
stars, component topology and chart containment. -/
theorem arrangementGraphGeometry : Expected.arrangementGraphGeometry.{u} := by
  intro kind M _ _ S D s A _hA hsubordinate B hB T
  obtain ⟨G, hcarrier, hboundary, hendpoints, hcurve, hfinite, hcharts, hstars⟩ :=
    arrangement_graph_geometry S D s hsubordinate hB T
  refine ⟨{
    graph := G
    carrier_eq := hcarrier
    contains_boundary := hboundary
    endpoint_germs := hendpoints
    edge_curve := hcurve
    finite_components := hfinite
    component_disk_chart := hcharts
    open_components := EmbeddedGraph.open_component G
    connected_components := Components.isConnected G.carrierᶜ
    compact_closures := EmbeddedGraph.compact_component_closure G
    connected_closures := EmbeddedGraph.connected_component_closure G
    frontiers_on_graph := EmbeddedGraph.frontier_component G
    nonempty_frontiers := ?_
    disjoint_interiors := fun _ _ hne => EmbeddedGraph.disjoint_component_interiors G _ _ hne
    stars := ?_
    empty_case := ?_
  }⟩
  · rw [hcarrier]
    exact arrangement_component_frontier_nonempty S D s hsubordinate T
  · intro p hp O hO hpO
    obtain ⟨g, hgO, hseparate, hincident, hoccupy⟩ := hstars p hp O hO hpO
    letI := hfinite
    have hfront : ∀ i : Fin T.count,
        frontier (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
          (T.disk i).openAtRadius (T.radius i)) ⊆ G.carrier := by
      rw [hcarrier]
      exact copy_disk_frontier_subset_carrier S D s T
    have hinj := Components.inclusion_injective_of_disk_memberships G.carrier g.neighborhood
      (fun i => P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s ⁻¹'
        (T.disk i).openAtRadius (T.radius i))
      (fun i => (ChartDisk.isOpen_openAtRadius _ _).preimage (D.copy_closedEmbedding s).continuous)
      hfront (by
        intro a b hab
        obtain ⟨i, hi⟩ := hseparate a b hab
        obtain ⟨x, hx⟩ := Components.nonempty _ a
        obtain ⟨y, hy⟩ := Components.nonempty _ b
        exact ⟨i, x, hx, y, hy, hi x hx y hy⟩)
    exact ⟨g, hgO, Finite.of_injective _ hinj, hseparate, hincident, hoccupy⟩
  · intro hM
    let := hM
    have hv : G.vertexCount = 0 := by
      by_contra hn
      exact isEmptyElim (G.vertex ⟨0, Nat.pos_of_ne_zero hn⟩)
    have he : G.edgeCount = 0 := by
      by_contra hn
      exact isEmptyElim (G.edge ⟨0, Nat.pos_of_ne_zero hn⟩ 0)
    exact ⟨hv, he, ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance⟩

end P202.SurfaceRegionConstruction
