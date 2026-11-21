import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ArrangementRegionExtraction
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ArrangementGraphGeometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RegionalBoundaryCycles
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RegionalLocalOneSidedness

/-!
Full extraction for paper.tex 5053–5076. The upstream construction supplies
actual finite graph geometry, genuine regional Jordan boundary curves, and
full-plane local one-sidedness. This module assembles their common actual
component domains into planar regions and the original-surface decomposition.
-/
set_option autoImplicit false
noncomputable section
open Set Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BoundaryData
open P202Specs.PlanarRegionTopology (Plane PlanarRegion)
open P202Specs.SurfaceRegionConstruction
universe u

namespace P202.SurfaceRegionConstruction
variable {X : Type u} [TopologicalSpace X]

/-- Once the genuine component regions have been constructed, all remaining
geometric decomposition fields are supplied by the actual graph components.
This constructor changes neither their domains nor their closures. -/
theorem regionDecomposition_of_component_regions {kind : ModelKind} [CompactSpace X]
    (S : SmoothManifold 2 kind X) (G : EmbeddedGraph S)
    (hboundary : intrinsicBoundary S ⊆ G.carrier)
    [Finite (ConnectedComponents (G.carrierᶜ : Set X))]
    (hregions : ∀ a : ConnectedComponents (G.carrierᶜ : Set X),
      ∃ (R : PlanarRegion) (e : ModelChart 2 kind X), e ∈ S.smoothStructure.val ∧
        closure (componentSet G.carrierᶜ a) ⊆ e.source ∧
        coordinates e '' componentSet G.carrierᶜ a = R.domain ∧
        coordinates e '' closure (componentSet G.carrierᶜ a) = R.carrier)
    (hstars : ∀ p ∈ G.carrier, ∀ O : Set X, IsOpen O → p ∈ O →
      ∃ g : GraphStar G p, g.neighborhood ⊆ O ∧
        (∀ c : ConnectedComponents (G.carrierᶜ : Set X),
          p ∈ closure (componentSet G.carrierᶜ c) →
          ∃ a : ConnectedComponents (g.neighborhood \ G.carrier : Set X),
            componentSet G.carrierᶜ c ∩ g.neighborhood =
              componentSet (g.neighborhood \ G.carrier) a) ∧
        (∀ a : ConnectedComponents (g.neighborhood \ G.carrier : Set X),
          ∃! c : ConnectedComponents (G.carrierᶜ : Set X),
            componentSet G.carrierᶜ c ∩ g.neighborhood =
              componentSet (g.neighborhood \ G.carrier) a)) :
    ∃ R : RegionDecomposition S, R.graph = G := by
  classical
  let C := ConnectedComponents (G.carrierᶜ : Set X)
  let : Fintype C := Fintype.ofFinite C
  let component : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  choose region chart hchart hclosure hdomain hcarrier using hregions
  refine ⟨{
    graph := G
    contains_boundary := hboundary
    regionCount := Fintype.card C
    component := component
    region := fun i => region (component i)
    chart := fun i => chart (component i)
    chart_mem := fun i => hchart (component i)
    closure_in_chart := fun i => hclosure (component i)
    domain_coordinates := fun i => hdomain (component i)
    closure_coordinates := fun i => hcarrier (component i)
    open_components := fun i => EmbeddedGraph.open_component G (component i)
    compact_closures := fun i => EmbeddedGraph.compact_component_closure G (component i)
    connected_closures := fun i => EmbeddedGraph.connected_component_closure G (component i)
    frontiers_on_graph := fun i => EmbeddedGraph.frontier_component G (component i)
    disjoint_interiors := fun i j hij => EmbeddedGraph.disjoint_component_interiors G
      (component i) (component j) (fun heq => hij (component.injective heq))
    sectors := ?_
    empty_case := ?_
  }, rfl⟩
  · intro p hp O hO hpO
    obtain ⟨g, hgO, hincident, hlocal⟩ := hstars p hp O hO hpO
    refine ⟨g, hgO, fun j hp => hincident (component j) hp, ?_⟩
    intro a
    obtain ⟨c, hc, huniq⟩ := hlocal a
    refine ⟨component.symm c, ?_, ?_⟩
    · simpa only [component.apply_symm_apply] using hc
    · intro j hj
      apply component.injective
      rw [component.apply_symm_apply]
      exact huniq (component j) hj
  · intro hX
    let := hX
    have hv : G.vertexCount = 0 := by
      by_contra hn
      exact isEmptyElim (G.vertex ⟨0, Nat.pos_of_ne_zero hn⟩)
    have he : G.edgeCount = 0 := by
      by_contra hn
      exact isEmptyElim (G.edge ⟨0, Nat.pos_of_ne_zero hn⟩ 0)
    let : IsEmpty C := ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
    exact ⟨hv, he, Fintype.card_of_isEmpty⟩


/-- The actual coordinate component, with its genuine finite boundary curves,
is a planar region. Its carrier is exactly the image of the component closure. -/
theorem arrangement_component_planarRegion
    {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold 2 kind M) (D : P202Specs.SmoothSurfaceDouble.SmoothDouble S)
    (s : Bool)
    (A : Set (ModelChart 2 .euclidean (P202Specs.SmoothSurfaceDouble.SurfaceDouble S)))
    (hA : A ⊆ D.manifold.smoothStructure.val) (hsub : CopySubordinate S D s A)
    (B : CompactSmoothSeam D.manifold)
    (hB : B.carrier = P202Specs.SmoothSurfaceDouble.seam (intrinsicBoundary S))
    (T : TransverseDiskArrangement D.manifold
      (range (P202Specs.SmoothSurfaceDouble.copy (intrinsicBoundary S) s)) A B)
    (H : ArrangementGraphGeometryData S D s T)
    (a : ConnectedComponents (H.graph.carrierᶜ : Set M))
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hsource : closure (componentSet H.graph.carrierᶜ a) ⊆ e.source) :
    ∃ R : PlanarRegion,
      R.domain = coordinates e '' componentSet H.graph.carrierᶜ a ∧
      R.carrier = coordinates e '' closure (componentSet H.graph.carrierᶜ a) := by
  obtain ⟨curves⟩ := regionalBoundaryCycles S D s A hA hsub B hB T H a e he hsource
  obtain ⟨_, hopen, hconnected, hcompact, hclosure, _, _, hside⟩ :=
    regionalLocalOneSidedness S D s hB T H a e he hsource
  exact ⟨{
    domain := coordinates e '' componentSet H.graph.carrierᶜ a
    open_domain := hopen
    connected_domain := hconnected
    compact_closure := hcompact
    boundaryCount := curves.count
    boundaryCount_pos := curves.count_pos
    curve := curves.curve
    disjoint_curves := curves.disjoint
    boundary_eq := curves.frontier_eq
    one_sided := hside
  }, rfl, hclosure⟩

/-- Full generic extraction on either labelled copy of the actual smooth
double, including empty, disconnected, nonorientable and boundary cases. -/
theorem arrangementRegionExtraction : Expected.arrangementRegionExtraction.{u} := by
  intro kind M _ _ S D s A hA hsub B hB T
  classical
  obtain ⟨H⟩ := arrangementGraphGeometry S D s A hA hsub B hB T
  let C := ConnectedComponents (H.graph.carrierᶜ : Set M)
  letI : Finite C := H.finite_components
  letI : Fintype C := Fintype.ofFinite C
  let component : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  choose disk chart hchart hdisk hclosedDisk hsource using H.component_disk_chart
  have hregions (a : C) : ∃ R : PlanarRegion,
      R.domain = coordinates (chart a) '' componentSet H.graph.carrierᶜ a ∧
      R.carrier = coordinates (chart a) '' closure (componentSet H.graph.carrierᶜ a) :=
    arrangement_component_planarRegion S D s A hA hsub B hB T H a
      (chart a) (hchart a) (hsource a)
  choose region hdomain hcarrier using hregions
  let R : RegionDecomposition S := {
    graph := H.graph
    contains_boundary := H.contains_boundary
    regionCount := Fintype.card C
    component := component
    region := fun j => region (component j)
    chart := fun j => chart (component j)
    chart_mem := fun j => hchart (component j)
    closure_in_chart := fun j => hsource (component j)
    domain_coordinates := fun j => (hdomain (component j)).symm
    closure_coordinates := fun j => (hcarrier (component j)).symm
    open_components := fun j => H.open_components (component j)
    compact_closures := fun j => H.compact_closures (component j)
    connected_closures := fun j => H.connected_closures (component j)
    frontiers_on_graph := fun j => H.frontiers_on_graph (component j)
    disjoint_interiors := fun i j hij => H.disjoint_interiors
      (fun heq => hij (component.injective heq))
    sectors := by
      intro p hp O hO hpO
      obtain ⟨g, hgO, _, _, hincident, hlocal⟩ := H.stars p hp O hO hpO
      refine ⟨g, hgO, fun j hj => hincident (component j) hj, ?_⟩
      intro a
      obtain ⟨c, hc, huniq⟩ := hlocal a
      refine ⟨component.symm c, ?_, ?_⟩
      · simpa only [component.apply_symm_apply] using hc
      · intro j hj
        apply component.injective
        rw [component.apply_symm_apply]
        exact huniq (component j) hj
    empty_case := by
      intro hM
      obtain ⟨hv, he, hempty⟩ := H.empty_case hM
      letI : IsEmpty C := hempty
      exact ⟨hv, he, Fintype.card_of_isEmpty⟩
  }
  refine ⟨R, {
    carrier_eq := H.carrier_eq
    endpoint_germs := H.endpoint_germs
    edge_curve := H.edge_curve
    region_disk := fun j => ⟨disk (component j), hdisk (component j), hclosedDisk (component j)⟩
    separated_stars := ?_
  }⟩
  intro p hp O hO hpO
  obtain ⟨g, hgO, _, hseparated, _, _⟩ := H.stars p hp O hO hpO
  exact ⟨g, hgO, hseparated⟩

end P202.SurfaceRegionConstruction
