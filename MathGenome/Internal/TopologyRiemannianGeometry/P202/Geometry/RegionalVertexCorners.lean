import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RegionalVertexCorners
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RegionalCornerTransport
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RadialGraphSectors
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.FinCases

/-! The local corner ledger for arbitrary actual regional presentations.
Genuine comparison presentations list any omitted graph-vertex joins. Actual
occupied-ray germs partition a metric tangent circle or boundary semicircle;
angular measure gives the literal interior-angle sum, including reflex angles.
Off the vertex set, both genuine boundary velocities lie on the same ray. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
open P202.MetricData
open P202Specs.PlanarRegionTopology P202Specs.PlaneTurning
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler
open P202Specs.GlobalGaussBonnet P202Specs.RegionalVertexCorners

namespace P202.GlobalGaussBonnet.VertexCorners
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

theorem originalPoint : P202Specs.RegionalVertexCorners.Expected.originalPoint.{u} := by
  intro kind M _ S D r i A k
  obtain ⟨p, hp, hs, he⟩ := region_corner_on_graph D r i A k
  refine ⟨p, ⟨hp, hs, he⟩, ?_⟩
  rintro q ⟨_, hq, hqe⟩
  exact P202.SurfaceRegionConstruction.coordinates_injOn (D.chart r) hq hs
    (hqe.trans he.symm)

/-- The source test uniquely determines the original point, even without an
additional closure/graph premise. -/
theorem cornerAt_unique (D : RegionDecomposition S) (r : Fin D.regionCount)
    (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (k : Fin A.count)
    {p q : M} (hp : CornerAt D r i A k p) (hq : CornerAt D r i A k q) : p = q := by
  exact P202.SurfaceRegionConstruction.coordinates_injOn (D.chart r)
    hp.1 hq.1 (hp.2.trans hq.2.symm)

/-- Every point satisfying the literal corner test is on the actual graph
boundary of its original region. -/
theorem cornerAt_mem (D : RegionDecomposition S) (r : Fin D.regionCount)
    (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (k : Fin A.count)
    {p : M} (hp : CornerAt D r i A k p) : p ∈ regionClosure D r ∩ D.graph.carrier := by
  obtain ⟨q, hq, _⟩ := originalPoint D r i A k
  simpa only [cornerAt_unique D r i A k hp hq.2] using hq.1

/-- The original point is constructed, rather than supplied as a certificate. -/
def originalCornerPoint (D : RegionDecomposition S) (r : Fin D.regionCount)
    (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (k : Fin A.count) : M :=
  (originalPoint D r i A k).choose

theorem originalCornerPoint_mem (D : RegionDecomposition S) (r : Fin D.regionCount)
    (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (k : Fin A.count) :
    originalCornerPoint D r i A k ∈ regionClosure D r ∩ D.graph.carrier ∧
      CornerAt D r i A k (originalCornerPoint D r i A k) :=
  (originalPoint D r i A k).choose_spec.1

theorem cornerAt_iff (D : RegionDecomposition S) (r : Fin D.regionCount)
    (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (k : Fin A.count) (p : M) :
    CornerAt D r i A k p ↔ p = originalCornerPoint D r i A k := by
  constructor
  · intro hp
    exact cornerAt_unique D r i A k hp (originalCornerPoint_mem D r i A k).2
  · rintro rfl
    exact (originalCornerPoint_mem D r i A k).2

/-- Within one region, distinct genuine boundary joins have distinct original
points, including the join at the period endpoint. -/
theorem originalCornerPoint_injective (D : RegionDecomposition S) (r : Fin D.regionCount)
    (A : ∀ i, ArcPresentation ((D.region r).curve i)) :
    Function.Injective (fun c : Σ i, Fin (A i).count =>
      originalCornerPoint D r c.1 (A c.1) c.2) := by
  intro c d hcd
  change originalCornerPoint D r c.1 (A c.1) c.2 =
    originalCornerPoint D r d.1 (A d.1) d.2 at hcd
  apply CornerTransport.regionalPresentation_endpoint_injective (D.region r) A
  change (A c.1).arc c.2 1 = (A d.1).arc d.2 1
  rw [← (originalCornerPoint_mem D r c.1 (A c.1) c.2).2.2,
    ← (originalCornerPoint_mem D r d.1 (A d.1) d.2).2.2, hcd]

/-- In particular an actual region has at most one presentation corner at p.
Other incident regions can have corners at the same p, as required. -/
theorem cornerAt_indices_unique (D : RegionDecomposition S) (r : Fin D.regionCount)
    (A : ∀ i, ArcPresentation ((D.region r).curve i)) (p : M)
    (c d : Σ i, Fin (A i).count)
    (hc : CornerAt D r c.1 (A c.1) c.2 p)
    (hd : CornerAt D r d.1 (A d.1) d.2 p) : c = d := by
  apply originalCornerPoint_injective D r A
  change originalCornerPoint D r c.1 (A c.1) c.2 =
    originalCornerPoint D r d.1 (A d.1) d.2
  rw [← (cornerAt_iff D r c.1 (A c.1) c.2 p).mp hc,
    ← (cornerAt_iff D r d.1 (A d.1) d.2 p).mp hd]

/-- Agreement with the already proved loop-sensitive incidence convention. -/
theorem vertexDegree_eq_valence (G : EmbeddedGraph S) (v : Fin G.vertexCount) :
    vertexDegree G v = valence G v := rfl

/-- At a common genuine endpoint, the literal exterior contributions agree. -/
theorem cornerTerm_eq_at_common_endpoint (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount) (G : RegionalChartGeometry g D r)
    (i : Fin (D.region r).boundaryCount)
    (A B : ArcPresentation ((D.region r).curve i)) (s : ℝ)
    (j : Fin A.count) (k : Fin B.count) (hp : A.arc j 1 = B.arc k 1) :
    cornerTerm g D r G i A s j = cornerTerm g D r G i B s k := by
  unfold cornerTerm P202Specs.LocalGaussBonnet.interiorAngle
  rw [CornerTransport.metricCornerAngle_eq_at_common_endpoint
    G.metric G.orientation G.ambientChart G.ambientChart_mem A B j k hp]

/-- A join absent from another actual presentation has zero exterior term. -/
theorem cornerTerm_eq_zero_of_endpoint_unlisted (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount) (G : RegionalChartGeometry g D r)
    (i : Fin (D.region r).boundaryCount)
    (A B : ArcPresentation ((D.region r).curve i)) (s : ℝ) (j : Fin A.count)
    (hne : ∀ k : Fin B.count, A.arc j 1 ≠ B.arc k 1) :
    cornerTerm g D r G i A s j = 0 := by
  unfold cornerTerm P202Specs.LocalGaussBonnet.interiorAngle
  rw [CornerTransport.metricCornerAngle_eq_zero_of_endpoint_unlisted
    G.metric G.orientation G.ambientChart G.ambientChart_mem A B j hne]
  ring

/-- One boundary curve can contribute at most one presentation term at p. -/
theorem sum_cornersAt_eq_single (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount) (G : RegionalChartGeometry g D r)
    (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (s : ℝ)
    (p : M) (j : Fin A.count) (hj : CornerAt D r i A j p) :
    (∑ k, if CornerAt D r i A k p then cornerTerm g D r G i A s k else 0) =
      cornerTerm g D r G i A s j := by
  classical
  rw [Finset.sum_eq_single j]
  · exact ite_eq_left hj
  · intro k _ hkj
    apply ite_eq_right
    intro hk
    apply hkj
    exact CornerTransport.arcPresentation_endpoint_injective A (hk.2.symm.trans hj.2)
  · simp

/-- Presentation invariance holds at each original point, not only after a
global sum. An omitted join is proved to contribute zero through the actual
unlisted-endpoint theorem. No refinement or incidence certificate is assumed. -/
theorem sum_cornersAt_eq_of_presentations (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount) (G : RegionalChartGeometry g D r)
    (i : Fin (D.region r).boundaryCount)
    (A B : ArcPresentation ((D.region r).curve i)) (s : ℝ) (p : M) :
    (∑ j, if CornerAt D r i A j p then cornerTerm g D r G i A s j else 0) =
      ∑ k, if CornerAt D r i B k p then cornerTerm g D r G i B s k else 0 := by
  classical
  by_cases hA : ∃ j, CornerAt D r i A j p
  · obtain ⟨j, hj⟩ := hA
    rw [sum_cornersAt_eq_single g D r G i A s p j hj]
    by_cases hB : ∃ k, CornerAt D r i B k p
    · obtain ⟨k, hk⟩ := hB
      rw [sum_cornersAt_eq_single g D r G i B s p k hk]
      exact cornerTerm_eq_at_common_endpoint g D r G i A B s j k (hj.2.symm.trans hk.2)
    · have hz : cornerTerm g D r G i A s j = 0 := by
        apply cornerTerm_eq_zero_of_endpoint_unlisted g D r G i A B s j
        intro k he
        exact hB ⟨k, hj.1, hj.2.trans he⟩
      rw [hz]
      symm
      apply Finset.sum_eq_zero
      intro k _
      exact ite_eq_right (fun hk => hB ⟨k, hk⟩)
  · have hAz : (∑ j, if CornerAt D r i A j p then cornerTerm g D r G i A s j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact ite_eq_right (fun hj => hA ⟨j, hj⟩)
    rw [hAz]
    symm
    apply Finset.sum_eq_zero
    intro k _
    split_ifs with hk
    · apply cornerTerm_eq_zero_of_endpoint_unlisted g D r G i B A s k
      intro j he
      exact hA ⟨j, hk.1, hk.2.trans he⟩
    · rfl

/-- The full filtered sum at a point is independent of every regional arc
presentation. This applies at graph vertices of any valence and off the graph. -/
theorem cornerSumAt_eq_of_presentations (g : RiemannianMetric S)
    (D : RegionDecomposition S) (G : ∀ r, RegionalChartGeometry g D r)
    (A B : ∀ r i, ArcPresentation ((D.region r).curve i))
    (s : ∀ r, Fin (D.region r).boundaryCount → ℝ) (p : M) :
    cornerSumAt g D G A s p = cornerSumAt g D G B s p := by
  classical
  unfold cornerSumAt
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  exact sum_cornersAt_eq_of_presentations g D r (G r) i (A r i) (B r i) (s r i) p

open Filter
open scoped _root_.Topology
open P202Specs.RegionalCornerTransport
open P202.SurfaceRegionConstruction

/-- Every component of a finite-ray complement in a convex model ball
accumulates at its center. This also handles a star with zero or one ray. -/
lemma zero_mem_closure_ray_component
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (d : Fin n → E) (K : Set E) (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (R : ℝ) (a : ConnectedComponents ((closedRays d)ᶜ ∩ (K ∩ Metric.ball 0 R) : Set E)) :
    (0 : E) ∈ closure (componentSet ((closedRays d)ᶜ ∩ (K ∩ Metric.ball 0 R)) a) := by
  let U := (closedRays d)ᶜ ∩ (K ∩ Metric.ball 0 R)
  obtain ⟨z, hz⟩ := Components.nonempty U a
  have hzU := Components.subset U a hz
  have hf : Continuous (fun t : ℝ => t • z) := continuous_id.smul continuous_const
  have hsub : (fun t : ℝ => t • z) '' Ioc 0 1 ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨CornerTransport.closedRays_compl_smul d t ht.1 z hzU.1, ?_, ?_⟩
    · have hh := hK h0 hzU.2.1 (sub_nonneg.mpr ht.2) ht.1.le (by ring : 1-t+t=1)
      simpa only [smul_zero, zero_add] using hh
    · have hn : ‖t • z‖ ≤ ‖z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
        exact mul_le_of_le_one_left (norm_nonneg z) ht.2
      have hzball : ‖z‖ < R := by
        simpa only [Metric.mem_ball, dist_zero_right] using hzU.2.2
      exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hn.trans_lt hzball)
  have hzc : z ∈ (fun t : ℝ => t • z) '' Ioc 0 1 := ⟨1, by norm_num, one_smul ℝ z⟩
  have hcomp : (fun t : ℝ => t • z) '' Ioc 0 1 ⊆ componentSet U a :=
    Components.contains_preconnected U (isPreconnected_Ioc.image _ hf.continuousOn)
      hsub a ⟨z, hzc, hz⟩
  have hzero : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
    simp
  have hlim := hf.continuousWithinAt.mem_closure_image hzero
  exact closure_mono hcomp (by simpa only [zero_smul] using hlim)

/-- Pulling the center back through the genuine original chart proves that
all actual star components are incident at p. No sector certificate is used. -/
theorem graphStar_center_mem_closure_component {G : EmbeddedGraph S} {p : M}
    (t : GraphStar G p) (a : ConnectedComponents (t.neighborhood \ G.carrier : Set M)) :
    p ∈ closure (componentSet (t.neighborhood \ G.carrier) a) := by
  let U := t.neighborhood \ G.carrier
  let V := (closedRays t.direction)ᶜ ∩ (centeredModel t ∩ Metric.ball 0 t.radius)
  let f := fun q : M => coordinates t.chart q - coordinates t.chart p
  let H : U ≃ₜ V :=
    (P202.RadialGraphSectors.StarHomeomorph.centeredCoordinatesHomeomorph t U
      (fun _ hx => hx.1.1)).trans
        (Homeomorph.setCongr (CornerTransport.graphStar_centered_coordinates_image t))
  have himage : f '' componentSet U a =
      componentSet V (P202.RadialGraphSectors.componentsEquiv H a) :=
    P202.RadialGraphSectors.image_componentSet H f (fun _ => rfl) a
  have h0model : (0 : Plane) ∈ centeredModel t := by
    change toPlane.symm (coordinates t.chart p + 0) ∈ modelSet 2 kind
    simpa only [add_zero, coordinates, toPlane.symm_apply_apply] using (t.chart p).property
  have hzero : (0 : Plane) ∈ closure (f '' componentSet U a) := by
    rw [himage]
    exact zero_mem_closure_ray_component t.direction (centeredModel t)
      (CornerTransport.convex_centeredModel t) h0model t.radius _
  have hsource : componentSet U a ⊆ t.chart.source :=
    fun x hx => (Components.subset U a hx).1.1
  apply (P202.SurfaceRegionConstruction.mem_closure_iff_coordinates_mem_closure_local
    t.chart (componentSet U a) t.mem_source).mpr
  rw [inter_eq_left.mpr hsource]
  have hcont : Continuous (fun z : Plane => z + coordinates t.chart p) :=
    continuous_id.add continuous_const
  have hmem := hcont.continuousWithinAt.mem_closure_image hzero
  simp only [zero_add] at hmem
  apply closure_mono _ hmem
  rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨x, hx, by simp only [f, sub_add_cancel]⟩

/-- An actual graph star gives a bijection between its local sectors and the
original regions incident at its center. It is derived from D.sectors and the
conical local geometry, not assumed of a corner or presentation. -/
theorem exists_incident_region_sector_equiv (D : RegionDecomposition S)
    (p : M) (hp : p ∈ D.graph.carrier)
    (O : Set M) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ t : GraphStar D.graph p, t.neighborhood ⊆ O ∧
      ∃ E : ConnectedComponents (t.neighborhood \ D.graph.carrier : Set M) ≃
        {r : Fin D.regionCount // p ∈ regionClosure D r},
        ∀ a, regionInterior D (E a).val ∩ t.neighborhood =
          componentSet (t.neighborhood \ D.graph.carrier) a := by
  classical
  obtain ⟨t, htO, hinc, hall⟩ := D.sectors p hp O hO hpO
  let U := t.neighborhood \ D.graph.carrier
  choose f hf huniq using hall
  have hincident (a : ConnectedComponents U) : p ∈ regionClosure D (f a) := by
    apply closure_mono (show componentSet U a ⊆ regionInterior D (f a) from ?_)
      (graphStar_center_mem_closure_component t a)
    rw [← hf a]
    exact inter_subset_left
  let F : ConnectedComponents U → {r : Fin D.regionCount // p ∈ regionClosure D r} :=
    fun a => ⟨f a, hincident a⟩
  have hinj : Function.Injective F := by
    intro a b hab
    have hfab : f a = f b := congrArg Subtype.val hab
    have habsets : componentSet U a = componentSet U b := by rw [← hf a, ← hf b, hfab]
    by_contra hne
    obtain ⟨x, hx⟩ := Components.nonempty U a
    exact Set.disjoint_left.mp (Components.disjoint U a b hne) hx (habsets ▸ hx)
  have hsurj : Function.Surjective F := by
    intro r
    obtain ⟨a, ha⟩ := hinc r.val r.property
    refine ⟨a, Subtype.ext ?_⟩
    exact (huniq a r.val ha).symm
  refine ⟨t, htO, Equiv.ofBijective F ⟨hinj, hsurj⟩, ?_⟩
  intro a
  exact hf a

/-- Counts all incident original regions, retaining the zero-ray case until
it is excluded by regional boundary geometry. No d>=2 certificate is used. -/
theorem euclidean_incident_region_card
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
    (D : RegionDecomposition S) (v : Fin D.graph.vertexCount) :
    Nat.card {r : Fin D.regionCount // D.graph.vertex v ∈ regionClosure D r} =
      if vertexDegree D.graph v = 0 then 1 else vertexDegree D.graph v := by
  classical
  have hp : D.graph.vertex v ∈ D.graph.carrier := Or.inl ⟨v, rfl⟩
  obtain ⟨t, _, E, _⟩ := exists_incident_region_sector_equiv D (D.graph.vertex v)
    hp univ isOpen_univ (mem_univ _)
  rw [← Nat.card_congr E]
  have hc := P202.RadialGraphSectors.fullStar_component_card t
    (fun _ _ => mem_univ _)
  have hd : t.rayCount = vertexDegree D.graph v :=
    (valence_eq_graphStar_rayCount D.graph v t).symm.trans
      (vertexDegree_eq_valence D.graph v).symm
  simpa only [hd] using hc

/-- At a genuine boundary vertex, the actual incident regions are precisely
the d-1 half-plane sectors. Both labelled ends of a loop remain counted. -/
theorem boundary_incident_region_card
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
    (D : RegionDecomposition S) (v : Fin D.graph.vertexCount)
    (hp : D.graph.vertex v ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S) :
    Nat.card {r : Fin D.regionCount // D.graph.vertex v ∈ regionClosure D r} =
      vertexDegree D.graph v - 1 := by
  have hpG : D.graph.vertex v ∈ D.graph.carrier := Or.inl ⟨v, rfl⟩
  obtain ⟨t, _, E, _⟩ := exists_incident_region_sector_equiv D (D.graph.vertex v)
    hpG univ isOpen_univ (mem_univ _)
  rw [← Nat.card_congr E]
  have hc := P202.RadialGraphSectors.boundaryStar_component_card t hp D.contains_boundary
  have hd : t.rayCount = vertexDegree D.graph v :=
    (valence_eq_graphStar_rayCount D.graph v t).symm.trans
      (vertexDegree_eq_valence D.graph v).symm
  simpa only [hd] using hc

/-- Boundary nondegeneracy follows from the genuine two seam rays. -/
theorem boundary_vertexDegree_two_le
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
    (D : RegionDecomposition S) (v : Fin D.graph.vertexCount)
    (hp : D.graph.vertex v ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S) :
    2 ≤ vertexDegree D.graph v := by
  have hpG : D.graph.vertex v ∈ D.graph.carrier := Or.inl ⟨v, rfl⟩
  obtain ⟨t, _⟩ := D.sectors (D.graph.vertex v) hpG univ isOpen_univ (mem_univ _)
  rw [vertexDegree_eq_valence, valence_eq_graphStar_rayCount D.graph v t]
  exact P202.RadialGraphSectors.graphStar_boundary_two_le_rayCount t hp D.contains_boundary

open SmoothManifolds.TangentData
open P202.RadialGraphSectors (starMetricSector starMetricAngle)

/-- The complete boundary half-plane metric ledger, indexed by actual
incident original regions. The angle is the genuine original tangent metric
angle. The comparison with literal presentation interior angles is separate. -/
theorem boundary_incident_metric_sectors
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
    (g : RiemannianMetric S) (D : RegionDecomposition S) (v : Fin D.graph.vertexCount)
    (hp : D.graph.vertex v ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (o : Orientation ℝ (TangentSpace S (D.graph.vertex v)) (Fin 2)) :
    ∃ t : GraphStar D.graph (D.graph.vertex v),
      ∃ n : ℕ, ∃ hn : t.rayCount = n + 2,
        let d := fun i : Fin (n + 2) => t.direction (Fin.cast hn.symm i)
        ∃ e : Equiv.Perm (Fin (n + 2)),
          ∃ E : {r : Fin D.regionCount // D.graph.vertex v ∈ regionClosure D r} ≃ Fin (n + 1),
            (∀ r, regionInterior D r.val ∩ t.neighborhood =
              starMetricSector g t o (d (e (E r).castSucc)) (d (e (E r).succ))) ∧
            (∑ r, starMetricAngle g t o
              (d (e (E r).castSucc)) (d (e (E r).succ))) = Real.pi := by
  classical
  have hpG : D.graph.vertex v ∈ D.graph.carrier := Or.inl ⟨v, rfl⟩
  obtain ⟨t, _, Er, hEr⟩ := exists_incident_region_sector_equiv D (D.graph.vertex v)
    hpG univ isOpen_univ (mem_univ _)
  obtain ⟨n, hn, e, Em, hEm, hsum⟩ :=
    P202.RadialGraphSectors.halfStarMetricSectors g t o hp D.contains_boundary
  let E := Er.symm.trans Em
  refine ⟨t, n, hn, e, E, ?_, ?_⟩
  · intro r
    have hr := hEr (Er.symm r)
    rw [Er.apply_symm_apply] at hr
    exact hr.trans (hEm (Er.symm r))
  · exact (Equiv.sum_comp E (fun i : Fin (n + 1) => starMetricAngle g t o
      (t.direction (Fin.cast hn.symm (e i.castSucc)))
      (t.direction (Fin.cast hn.symm (e i.succ))))).trans hsum

/-- Full-plane metric sectors indexed by the actual original incident regions.
The positivity premise is explicit here; excluding the degenerate interior
cases from boundary regularity remains a separate proof obligation. -/
theorem euclidean_incident_metric_sectors
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
    (g : RiemannianMetric S) (D : RegionDecomposition S) (v : Fin D.graph.vertexCount)
    (o : Orientation ℝ (TangentSpace S (D.graph.vertex v)) (Fin 2))
    (hv : 0 < vertexDegree D.graph v) :
    ∃ t : GraphStar D.graph (D.graph.vertex v),
      ∃ e : Equiv.Perm (Fin t.rayCount),
        ∃ E : {r : Fin D.regionCount // D.graph.vertex v ∈ regionClosure D r} ≃ Fin t.rayCount,
          (∀ r, regionInterior D r.val ∩ t.neighborhood =
            starMetricSector g t o (t.direction (e (E r)))
              (t.direction (e (finRotate t.rayCount (E r))))) ∧
          (∑ r, starMetricAngle g t o (t.direction (e (E r)))
            (t.direction (e (finRotate t.rayCount (E r))))) = 2 * Real.pi := by
  classical
  have hpG : D.graph.vertex v ∈ D.graph.carrier := Or.inl ⟨v, rfl⟩
  obtain ⟨t, _, Er, hEr⟩ := exists_incident_region_sector_equiv D (D.graph.vertex v)
    hpG univ isOpen_univ (mem_univ _)
  have htpos : 0 < t.rayCount := by
    rwa [vertexDegree_eq_valence, valence_eq_graphStar_rayCount D.graph v t] at hv
  obtain ⟨e, Em, hEm, hsum⟩ := P202.RadialGraphSectors.fullStarMetricSectors g t o
    (fun _ _ => mem_univ _) htpos
  let E := Er.symm.trans Em
  refine ⟨t, e, E, ?_, ?_⟩
  · intro r
    have hr := hEr (Er.symm r)
    rw [Er.apply_symm_apply] at hr
    exact hr.trans (hEm (Er.symm r))
  · exact (Equiv.sum_comp E (fun i : Fin t.rayCount => starMetricAngle g t o
      (t.direction (e i)) (t.direction (e (finRotate t.rayCount i))))).trans hsum


open SmoothManifolds.BoundaryData
open P202.PlaneTurning

/-- A geometric partition avoiding the original joins in each open interval
produces an actual presentation with exactly its knots. -/
theorem exists_presentation_with_partition (c : RegularJordanCurve)
    (Q : Partition)
    (hno : ∀ (i : Fin Q.count) (t : ℝ),
      t ∈ Ioo (Q.time i.castSucc) (Q.time i.succ) → (t : ParameterCircle) ∉ c.joins) :
    ∃ A : ArcPresentation c, Set.range A.time = Set.range Q.time := by
  have hab (i : Fin Q.count) : Q.time i.castSucc < Q.time i.succ :=
    Q.strictMono (by simp [Fin.lt_def])
  have hex (i : Fin Q.count) := closed_arc_extension c (Q.time i.castSucc)
    (Q.time i.succ) (hab i) (hno i)
  choose F ε hε heq hs using hex
  have hdiff (i : Fin Q.count) (t : ℝ) (ht : t ∈ Icc (Q.time i.castSucc) (Q.time i.succ)) :
      DifferentiableAt ℝ (F i) t :=
    ((hs i).contDiffAt (isOpen_Ioo.mem_nhds
      ⟨by linarith [ht.1, hε i], by linarith [ht.2, hε i]⟩)).differentiableAt (by simp)
  have hreg (i : Fin Q.count) := closed_arc_regular c (hab i) (hε i) (heq i) (hs i) (hno i)
  have hcn (i : Fin Q.count) :
      NormedSpace.normalize (deriv (F i) (Q.time i.succ)) ≠
        -NormedSpace.normalize (deriv (F (finRotate Q.count i))
          (Q.time (finRotate Q.count i).castSucc)) := by
    letI : NeZero Q.count := ⟨by have := Q.at_least_three; omega⟩
    by_cases hi : i.val + 1 < Q.count
    · let j : Fin Q.count := ⟨i.val + 1, hi⟩
      have hrot : finRotate Q.count i = j := by
        rw [finRotate_apply]
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
        exact Nat.mod_eq_of_lt hi
      have ht : Q.time i.succ = Q.time j.castSucc := congrArg Q.time (Fin.ext rfl)
      have heG : EqOn (F j) (P202Specs.PlanarRegionTopology.realLift c.parametrization)
          (Icc (Q.time i.succ) (Q.time j.succ)) := by rw [ht]; exact heq j
      have hdG : DifferentiableAt ℝ (F j) (Q.time i.succ) := by
        rw [ht]; exact hdiff j _ (by exact ⟨le_rfl, (hab j).le⟩)
      have hn := adjacent_arc_noncuspidal c (hab i) (by rw [ht]; exact hab j)
        (hdiff i _ ⟨(hab i).le, le_rfl⟩) hdG (heq i) heG
      simpa only [hrot, ht] using hn
    · let z : Fin Q.count := ⟨0, by have := Q.at_least_three; omega⟩
      have hilast : i.val + 1 = Q.count := by omega
      have hrot : finRotate Q.count i = z := by
        rw [finRotate_apply]
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
        change (i.val + 1) % Q.count = 0
        rw [hilast, Nat.mod_self]
      have hb : Q.time i.succ = 1 :=
        (congrArg Q.time (Fin.ext hilast)).trans Q.last
      have hz : Q.time z.castSucc = 0 := Q.first
      have heF : EqOn (F i) (P202Specs.PlanarRegionTopology.realLift c.parametrization)
          (Icc (Q.time i.castSucc) 1) := by rw [← hb]; exact heq i
      have heG : EqOn (F z) (P202Specs.PlanarRegionTopology.realLift c.parametrization)
          (Icc 0 (Q.time z.succ)) := by rw [← hz]; exact heq z
      have hdF : DifferentiableAt ℝ (F i) 1 := by
        rw [← hb]; exact hdiff i _ ⟨(hab i).le, le_rfl⟩
      have hdG : DifferentiableAt ℝ (F z) 0 := by
        rw [← hz]; exact hdiff z _ ⟨le_rfl, (hab z).le⟩
      have hn := closing_arc_noncuspidal c (by rw [← hb]; exact hab i)
        (by rw [← hz]; exact hab z) hdF hdG heF heG
      simpa only [hrot, hb, hz] using hn
  let arc : Fin Q.count → ℝ → Plane := fun i t =>
    F i (Q.time i.castSucc + (Q.time i.succ - Q.time i.castSucc) * t)
  have hder (i : Fin Q.count) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (arc i) ((Q.time i.succ - Q.time i.castSucc) •
        deriv (F i) (Q.time i.castSucc + (Q.time i.succ - Q.time i.castSucc) * t)) t :=
    affine_arc_deriv (hab i) (hε i) (hs i) ht
  have hnorm (i : Fin Q.count) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      NormedSpace.normalize (deriv (arc i) t) =
        NormedSpace.normalize (deriv (F i)
          (Q.time i.castSucc + (Q.time i.succ - Q.time i.castSucc) * t)) := by
    rw [(hder i t ht).deriv, NormedSpace.normalize_smul_of_pos (sub_pos.mpr (hab i))]
  refine ⟨⟨Q.count, by have := Q.at_least_three; omega, Q.time, Q.strictMono,
    Q.first, Q.last, arc, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro i t ht
    exact heq i (by constructor <;> nlinarith [ht.1, ht.2, hab i])
  · intro i
    exact affine_arc_smooth (hab i) (hε i) (hs i)
  · intro i t ht
    rw [(hder i t ht).deriv]
    apply smul_ne_zero (ne_of_gt (sub_pos.mpr (hab i)))
    exact hreg i _ (by constructor <;> nlinarith [ht.1, ht.2, hab i])
  · intro i
    rw [hnorm i 1 (by simp), hnorm _ 0 (by simp)]
    have he : Q.time i.castSucc + (Q.time i.succ - Q.time i.castSucc) = Q.time i.succ := by ring
    simpa only [mul_one, mul_zero, add_zero, he] using hcn i


/-- A prescribed real parameter can be included among the actual presentation
knots. The new partition also contains all original nonsmooth joins. -/
theorem exists_presentation_listing_parameter (c : RegularJordanCurve)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ A : ArcPresentation c, t ∈ Set.range A.time := by
  classical
  let r : ParameterCircle → ℝ := fun q => (AddCircle.equivIco (1 : ℝ) 0 q).val
  let B : Finset ℝ := {0, 1 / 3, 2 / 3, 1}
  let K := insert t (B ∪ c.joins.image r)
  have hB : B ⊆ K := Finset.subset_union_left.trans (Finset.subset_insert _ _)
  have hcard : 4 ≤ K.card := by
    have hBc : B.card = 4 := by norm_num [B]
    have := Finset.card_le_card hB
    omega
  have hK : ∀ x ∈ K, x ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ht
    rcases Finset.mem_union.mp hx with hx | hx
    · simp only [B, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx
      have h := (AddCircle.equivIco (1 : ℝ) 0 q).property
      exact ⟨h.1, by simpa using h.2.le⟩
  obtain ⟨Q, hQ⟩ := partition_of_finset K hcard hK
    (hB (by simp [B])) (hB (by simp [B]))
  have hno (i : Fin Q.count) (x : ℝ)
      (hx : x ∈ Ioo (Q.time i.castSucc) (Q.time i.succ)) :
      (x : ParameterCircle) ∉ c.joins := by
    intro hj
    have ha := partition_time_mem Q i.castSucc
    have hb := partition_time_mem Q i.succ
    have hx01 : x ∈ Ico (0 : ℝ) (0 + 1) :=
      ⟨by linarith [ha.1, hx.1], by linarith [hb.2, hx.2]⟩
    have hr : r (x : ParameterCircle) = x := AddCircle.equivIco_coe_of_mem hx01
    have hxK : x ∈ K := Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hj, hr⟩))
    obtain ⟨j, hj⟩ : x ∈ Set.range Q.time := by rw [hQ]; exact hxK
    exact partition_no_between Q i j (by rw [hj]; exact hx)
  obtain ⟨A, hA⟩ := exists_presentation_with_partition c Q hno
  exact ⟨A, by rw [hA, hQ]; exact Finset.mem_insert_self _ _⟩

/-- Every actual point of a Jordan curve can be made a literal presentation
endpoint, including the cyclic seam. -/
theorem exists_presentation_listing_point (c : RegularJordanCurve)
    (q : ParameterCircle) :
    ∃ A : ArcPresentation c, ∃ j : Fin A.count, A.arc j 1 = c.parametrization q := by
  let t := (AddCircle.equivIoc (1 : ℝ) 0 q).val
  have ht : t ∈ Ioc (0 : ℝ) 1 := by
    simpa only [zero_add] using (AddCircle.equivIoc (1 : ℝ) 0 q).property
  obtain ⟨A, l, hl⟩ := exists_presentation_listing_parameter c t ⟨ht.1.le, ht.2⟩
  have hl0 : l ≠ 0 := by
    intro he
    rw [he, A.first] at hl
    exact ht.1.ne' hl.symm
  obtain ⟨j, rfl⟩ := (Fin.eq_zero_or_eq_succ l).resolve_left hl0
  refine ⟨A, j, ?_⟩
  rw [A.agrees j 1 (by simp)]
  simp only [mul_one, add_sub_cancel, hl]
  unfold realLift
  exact congrArg c.parametrization (AddCircle.coe_equivIoc (p := (1 : ℝ)) (a := 0))

/-- The literal contribution from one region has at most one nonzero indexed
place at any original point, including the cyclic seam of each curve. -/
theorem region_cornersAt_eq_single (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount) (G : RegionalChartGeometry g D r)
    (A : ∀ i, ArcPresentation ((D.region r).curve i))
    (s : Fin (D.region r).boundaryCount → ℝ)
    (p : M) (i : Fin (D.region r).boundaryCount) (k : Fin (A i).count)
    (hp : CornerAt D r i (A i) k p) :
    (∑ j, ∑ l, if CornerAt D r j (A j) l p then cornerTerm g D r G j (A j) (s j) l else 0) =
      cornerTerm g D r G i (A i) (s i) k := by
  rw [Finset.sum_eq_single i]
  · exact sum_cornersAt_eq_single g D r G i (A i) (s i) p k hp
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro l _
    apply ite_eq_right
    intro hl
    exact hji (congrArg Sigma.fst
      (cornerAt_indices_unique D r A p ⟨j, l⟩ ⟨i, k⟩ hl hp))
  · simp

/-- Regions not incident to p have no actual presentation corner there. -/
theorem region_cornersAt_eq_zero_of_not_incident (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount) (G : RegionalChartGeometry g D r)
    (A : ∀ i, ArcPresentation ((D.region r).curve i))
    (s : Fin (D.region r).boundaryCount → ℝ)
    (p : M) (hp : p ∉ regionClosure D r) :
    (∑ j, ∑ l, if CornerAt D r j (A j) l p then cornerTerm g D r G j (A j) (s j) l else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro l _
  exact ite_eq_right (fun h => hp (cornerAt_mem D r j (A j) l h).1)

/-- Pointwise invariance can be applied to a single region, so comparison
presentations may be chosen independently in different incident regions. -/
theorem region_cornersAt_eq_of_presentations (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount) (G : RegionalChartGeometry g D r)
    (A B : ∀ i, ArcPresentation ((D.region r).curve i))
    (s : Fin (D.region r).boundaryCount → ℝ) (p : M) :
    (∑ i, ∑ j, if CornerAt D r i (A i) j p then cornerTerm g D r G i (A i) (s i) j else 0) =
      ∑ i, ∑ k, if CornerAt D r i (B i) k p then cornerTerm g D r G i (B i) (s i) k else 0 := by
  apply Finset.sum_congr rfl
  intro i _
  exact sum_cornersAt_eq_of_presentations g D r G i (A i) (B i) (s i) p

/-- Any original incident graph point lies on a genuine boundary component
in the region's assigned chart. -/
theorem incident_graph_point_on_boundary (D : RegionDecomposition S)
    (r : Fin D.regionCount) (p : M) (hp : p ∈ regionClosure D r ∩ D.graph.carrier) :
    ∃ i : Fin (D.region r).boundaryCount, ∃ q : ParameterCircle,
      ((D.region r).curve i).parametrization q = coordinates (D.chart r) p := by
  have hb : coordinates (D.chart r) p ∈ (D.region r).boundary := by
    rw [region_boundary_eq_coordinates_graph D r]
    exact ⟨p, hp, rfl⟩
  change coordinates (D.chart r) p ∈ frontier (D.region r).domain at hb
  rw [(D.region r).boundary_eq] at hb
  obtain ⟨i, q, hq⟩ := mem_iUnion.mp hb
  exact ⟨i, q, hq⟩
/-- Every actual incident graph point can be listed by a genuine family of
presentations of the unchanged regional boundary curves. -/
theorem exists_regional_presentation_listing_incident_point
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (A : ∀ i, ArcPresentation ((D.region r).curve i))
    (p : M) (hp : p ∈ regionClosure D r ∩ D.graph.carrier) :
    ∃ B : ∀ i, ArcPresentation ((D.region r).curve i),
      ∃ (i : Fin (D.region r).boundaryCount) (k : Fin (B i).count),
        CornerAt D r i (B i) k p := by
  classical
  obtain ⟨i, q, hq⟩ := incident_graph_point_on_boundary D r p hp
  obtain ⟨Bi, k, hk⟩ := exists_presentation_listing_point ((D.region r).curve i) q
  let B := Function.update A i Bi
  have hi : B i = Bi := Function.update_self _ _ _
  have hlisted : ∃ k : Fin (B i).count, CornerAt D r i (B i) k p := by
    rw [hi]
    exact ⟨k, D.closure_in_chart r hp.1, (hk.trans hq).symm⟩
  obtain ⟨k, hk⟩ := hlisted
  exact ⟨B, i, k, hk⟩


/-- The comparison presentations can list a fixed original graph point in
every incident region at once. No such listing is required of the input A. -/
theorem exists_presentations_listing_incident_point
    (D : RegionDecomposition S)
    (A : ∀ r i, ArcPresentation ((D.region r).curve i))
    (p : M) (hpG : p ∈ D.graph.carrier) :
    ∃ B : ∀ r i, ArcPresentation ((D.region r).curve i),
      ∀ r, p ∈ regionClosure D r →
        ∃ (i : Fin (D.region r).boundaryCount) (k : Fin (B r i).count),
          CornerAt D r i (B r i) k p := by
  classical
  have hex (r : Fin D.regionCount) :
      ∃ B : ∀ i, ArcPresentation ((D.region r).curve i),
        p ∈ regionClosure D r →
          ∃ (i : Fin (D.region r).boundaryCount) (k : Fin (B i).count),
            CornerAt D r i (B i) k p := by
    by_cases hr : p ∈ regionClosure D r
    · obtain ⟨B, i, k, hk⟩ :=
        exists_regional_presentation_listing_incident_point D r (A r) p ⟨hr, hpG⟩
      exact ⟨B, fun _ => ⟨i, k, hk⟩⟩
    · exact ⟨A r, fun h => (hr h).elim⟩
  choose B hB using hex
  exact ⟨B, hB⟩

/-- Once genuine presentation endpoints have been chosen, the local ledger
is exactly pi per incident region minus their literal interior angles. -/
theorem cornerSumAt_eq_incident_angle_sum
    (g : RiemannianMetric S) (D : RegionDecomposition S)
    (G : ∀ r, RegionalChartGeometry g D r)
    (A : ∀ r i, ArcPresentation ((D.region r).curve i))
    (s : ∀ r, Fin (D.region r).boundaryCount → ℝ) (p : M)
    (i : ∀ r : {r : Fin D.regionCount // p ∈ regionClosure D r},
      Fin (D.region r.val).boundaryCount)
    (k : ∀ r : {r : Fin D.regionCount // p ∈ regionClosure D r}, Fin (A r.val (i r)).count)
    (hp : ∀ r, CornerAt D r.val (i r) (A r.val (i r)) (k r) p) :
    cornerSumAt g D G A s p =
      Real.pi * (Nat.card {r : Fin D.regionCount // p ∈ regionClosure D r} : ℝ) -
        ∑ r : {r : Fin D.regionCount // p ∈ regionClosure D r},
          P202Specs.LocalGaussBonnet.interiorAngle
            (G r.val).metric (G r.val).orientation (G r.val).ambientChart
            (G r.val).ambientChart_mem (A r.val (i r)) (s r.val (i r)) (k r) := by
  classical
  let f := fun r : Fin D.regionCount => ∑ j, ∑ l,
    if CornerAt D r j (A r j) l p then cornerTerm g D r (G r) j (A r j) (s r j) l else 0
  have hnon : (∑ r : {r : Fin D.regionCount // p ∉ regionClosure D r}, f r.val) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    exact region_cornersAt_eq_zero_of_not_incident g D r.val (G r.val)
      (A r.val) (s r.val) p r.property
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun r : Fin D.regionCount => p ∈ regionClosure D r) f
  rw [hnon, add_zero] at hsplit
  change (∑ r, f r) = _
  rw [← hsplit]
  have hterm (r : {r : Fin D.regionCount // p ∈ regionClosure D r}) :
      f r.val = cornerTerm g D r.val (G r.val) (i r) (A r.val (i r))
        (s r.val (i r)) (k r) :=
    region_cornersAt_eq_single g D r.val (G r.val) (A r.val) (s r.val) p (i r) (k r) (hp r)
  simp_rw [hterm]
  unfold cornerTerm
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  ring

theorem span_singleton_interior_empty (v : Plane) :
    interior (Submodule.span ℝ {v} : Set Plane) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have ht := (Submodule.span ℝ {v}).eq_top_of_nonempty_interior' ⟨x, hx⟩
  have hf : Module.finrank ℝ (Submodule.span ℝ {v}) ≤ 1 := by
    simpa using (finrank_span_le_card ({v} : Set Plane))
  rw [ht, finrank_top] at hf
  norm_num [P202Specs.PlanarRegionTopology.Plane, finrank_euclideanSpace] at hf

theorem closedRays_nowhereDense {n : ℕ} (d : Fin n → Plane) :
    IsNowhereDense (closedRays d) := by
  have hline (v : Plane) : IsNowhereDense (Submodule.span ℝ {v} : Set Plane) := by
    rw [(Submodule.span ℝ {v}).closed_of_finiteDimensional.isNowhereDense_iff]
    exact span_singleton_interior_empty v
  have hzero : IsNowhereDense ({0} : Set Plane) :=
    (hline 0).mono (by intro x hx; rcases hx with rfl; exact Submodule.zero_mem _)
  apply hzero.union
  apply IsNowhereDense.iUnion
  intro i
  apply (hline (d i)).mono
  rintro x ⟨r, hr, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

lemma closedRays_compl_dense {n : ℕ} (d : Fin n → Plane) :
    Dense (closedRays d)ᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  exact Set.eq_empty_of_subset_empty ((interior_mono subset_closure).trans_eq
    (closedRays_nowhereDense d))

lemma graphStar_neighborhood_subset_closure_compl {G : EmbeddedGraph S} {p : M}
    (t : GraphStar G p)
    (hfull : ∀ z : Plane, ‖z‖ < t.radius →
      toPlane.symm (coordinates t.chart p + z) ∈ modelSet 2 kind) :
    t.neighborhood ⊆ closure (t.neighborhood \ G.carrier) := by
  let U := t.neighborhood \ G.carrier
  let f := fun q : M => coordinates t.chart q - coordinates t.chart p
  have himage : f '' U = (closedRays t.direction)ᶜ ∩ Metric.ball 0 t.radius := by
    rw [CornerTransport.graphStar_centered_coordinates_image]
    ext z
    constructor
    · rintro ⟨hz, _, hzb⟩
      exact ⟨hz, hzb⟩
    · rintro ⟨hz, hzb⟩
      refine ⟨hz, ?_, hzb⟩
      exact hfull z (by simpa only [Metric.mem_ball, dist_zero_right] using hzb)
  intro x hx
  have hxball : f x ∈ Metric.ball 0 t.radius := by
    simpa only [f, Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero] using hx.2
  have hzero : f x ∈ closure (f '' U) := by
    rw [himage]
    simpa only [Set.inter_comm] using
      (closedRays_compl_dense t.direction).open_subset_closure_inter Metric.isOpen_ball hxball
  have hsource : U ⊆ t.chart.source := fun q hq => hq.1.1
  apply (mem_closure_iff_coordinates_mem_closure_local t.chart U hx.1).mpr
  rw [inter_eq_left.mpr hsource]
  have hcont : Continuous (fun z : Plane => z + coordinates t.chart p) :=
    continuous_id.add continuous_const
  have hmem := hcont.continuousWithinAt.mem_closure_image hzero
  simp only [f, sub_add_cancel] at hmem
  apply closure_mono _ hmem
  rintro y ⟨z, ⟨q, hq, rfl⟩, rfl⟩
  exact ⟨q, hq, by simp only [f, sub_add_cancel]⟩

/-- A region cannot contain an open original neighborhood of an interior graph
point in its closure: local one-sidedness in its genuine chart excludes it. -/
lemma regionClosure_not_neighborhood_at_interior_graph (D : RegionDecomposition S)
    {p : M} (hpG : p ∈ D.graph.carrier)
    (r : Fin D.regionCount) (N : Set M) (hN : IsOpen N) (hpN : p ∈ N)
    (hNB : Disjoint N (intrinsicBoundary S)) (hNr : N ⊆ regionClosure D r) : False := by
  let O := N ∩ (D.chart r).source
  have hO : IsOpen O := hN.inter (D.chart r).open_source
  have hpO : p ∈ O := ⟨hpN, D.closure_in_chart r (hNr hpN)⟩
  have hcO : IsOpen (coordinates (D.chart r) '' O) :=
    isOpen_coordinate_image_away_boundary S (D.chart r) (D.chart_mem r)
      hO inter_subset_right (hNB.mono_left inter_subset_left)
  have hsubset : coordinates (D.chart r) '' O ⊆ (D.region r).carrier := by
    rintro z ⟨q, hq, rfl⟩
    rw [← D.closure_coordinates r]
    exact ⟨q, hNr hq.1, rfl⟩
  have hpint : coordinates (D.chart r) p ∈ interior (D.region r).carrier :=
    hcO.subset_interior_iff.mpr hsubset ⟨p, hpO, rfl⟩
  rw [(P202.PlanarRegionTopology.basicProperties (D.region r)).2.2.1] at hpint
  have hpr : p ∈ regionInterior D r :=
    (P202.SurfaceRegionsEuler.coordinates_mem_domain_iff D r ⟨p, hNr hpN⟩).mp hpint
  exact (P202.SurfaceRegionsEuler.componentSet_subset _ hpr) hpG

lemma graphStar_two_le_rayCount_of_occupancy (D : RegionDecomposition S)
    {p : M} (hpG : p ∈ D.graph.carrier) (t : GraphStar D.graph p)
    (hNB : Disjoint t.neighborhood (intrinsicBoundary S))
    (hfull : ∀ z : Plane, ‖z‖ < t.radius →
      toPlane.symm (coordinates t.chart p + z) ∈ modelSet 2 kind)
    (hall : ∀ a : ConnectedComponents (t.neighborhood \ D.graph.carrier : Set M),
      ∃ r : Fin D.regionCount,
        regionInterior D r ∩ t.neighborhood =
          componentSet (t.neighborhood \ D.graph.carrier) a) :
    2 ≤ t.rayCount := by
  by_contra hn
  have hn1 : t.rayCount ≤ 1 := by omega
  let U := t.neighborhood \ D.graph.carrier
  have hc : Nat.card (ConnectedComponents U) = 1 := by
    have he := P202.RadialGraphSectors.fullStar_component_card t hfull
    change Nat.card (ConnectedComponents U) = _ at he
    rw [he]
    split_ifs with hz
    · rfl
    · omega
  obtain ⟨hsub, hne⟩ := Nat.card_eq_one_iff_unique.mp hc
  letI : Subsingleton (ConnectedComponents U) := hsub
  obtain ⟨a⟩ := hne
  obtain ⟨r, hr⟩ := hall a
  have hUr : U ⊆ regionInterior D r := by
    intro x hx
    have hxa : x ∈ componentSet U a :=
      ⟨⟨x, hx⟩, Subsingleton.elim _ _, rfl⟩
    rw [← hr] at hxa
    exact hxa.1
  have hNr : t.neighborhood ⊆ regionClosure D r :=
    (graphStar_neighborhood_subset_closure_compl t hfull).trans (closure_mono hUr)
  exact regionClosure_not_neighborhood_at_interior_graph D hpG r t.neighborhood
    (P202.SurfaceRegionConstruction.GraphStar.isOpen_neighborhood t)
    (P202.SurfaceRegionConstruction.GraphStar.mem_neighborhood t) hNB hNr
/-- A star avoiding the actual boundary contains a full model ball, even when
its ambient manifold is presented using half-space charts. -/
lemma graphStar_full_model_of_avoids_boundary
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
    {G : EmbeddedGraph S} {p : M} (t : GraphStar G p)
    (ht : t.neighborhood ⊆ (intrinsicBoundary S)ᶜ) :
    ∀ z : Plane, ‖z‖ < t.radius →
      toPlane.symm (coordinates t.chart p + z) ∈ modelSet 2 .halfSpace := by
  have hh : 0 ≤ coordinates t.chart p 1 := (t.chart p).property
  have hr : t.radius ≤ coordinates t.chart p 1 := by
    by_contra hn
    have hlt : coordinates t.chart p 1 < t.radius := lt_of_not_ge hn
    let z : Plane := !₂[coordinates t.chart p 0, 0]
    have hzmodel : toPlane.symm z ∈ modelSet 2 .halfSpace := by
      change 0 ≤ z 1
      simp [z]
    let q : ModelSpace 2 .halfSpace := ⟨toPlane.symm z, hzmodel⟩
    have hnrm : ‖z - coordinates t.chart p‖ = coordinates t.chart p 1 := by
      apply (sq_eq_sq₀ (norm_nonneg _) hh).mp
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [z, Fin.sum_univ_two]
    have hqb : toPlane q.val ∈ Metric.ball (coordinates t.chart p) t.radius := by
      change ‖toPlane (toPlane.symm z) - coordinates t.chart p‖ < t.radius
      rw [toPlane.apply_symm_apply, hnrm]
      exact hlt
    have hq := t.ball_in_target q hqb
    have hqs : t.chart.symm q ∈ t.chart.source := t.chart.map_target hq
    have hqcoord : coordinates t.chart (t.chart.symm q) = z := by
      unfold coordinates
      rw [t.chart.right_inv hq]
      exact toPlane.apply_symm_apply z
    have hqB : t.chart.symm q ∈ intrinsicBoundary S := by
      apply (SmoothManifolds.intrinsicBoundary_iff_chart S t.chart t.chart_mem _ hqs).mpr
      change coordinates t.chart (t.chart.symm q) 1 = 0
      rw [hqcoord]
      simp [z]
    apply ht ⟨hqs, ?_⟩ hqB
    change coordinates t.chart (t.chart.symm q) ∈ Metric.ball (coordinates t.chart p) t.radius
    rw [hqcoord]
    simpa only [q, toPlane.apply_symm_apply] using hqb
  intro z hz
  change 0 ≤ (coordinates t.chart p + z) 1
  have hc : |z 1| ≤ ‖z‖ := PiLp.norm_apply_le z 1
  simp only [PiLp.add_apply]
  have := neg_le_abs (z 1)
  linarith

/-- Every actual regional graph vertex has at least two labelled half-edges.
Local one-sidedness rules out isolated and terminal interior graph vertices. -/
theorem two_le_vertexDegree (D : RegionDecomposition S) (v : Fin D.graph.vertexCount) :
    2 ≤ P202Specs.RegionalVertexCorners.vertexDegree D.graph v := by
  classical
  have hpG : D.graph.vertex v ∈ D.graph.carrier := Or.inl ⟨v, rfl⟩
  by_cases hpB : D.graph.vertex v ∈ intrinsicBoundary S
  · cases kind with
    | euclidean =>
      exact False.elim (by
        simpa only [SmoothManifolds.intrinsicBoundary_euclidean, Set.mem_empty_iff_false] using hpB)
    | halfSpace => exact boundary_vertexDegree_two_le D v hpB
  · obtain ⟨t, ht, _, hall⟩ := D.sectors (D.graph.vertex v) hpG
      (intrinsicBoundary S)ᶜ (SmoothManifolds.isClosed_intrinsicBoundary S).isOpen_compl hpB
    have hNB : Disjoint t.neighborhood (intrinsicBoundary S) :=
      Set.disjoint_left.mpr (fun _ hx => ht hx)
    have hfull : ∀ z : Plane, ‖z‖ < t.radius →
        toPlane.symm (coordinates t.chart (D.graph.vertex v) + z) ∈ modelSet 2 kind := by
      cases kind with
      | euclidean => exact fun _ _ => Set.mem_univ _
      | halfSpace => exact graphStar_full_model_of_avoids_boundary t ht
    have htwo := graphStar_two_le_rayCount_of_occupancy D hpG t hNB hfull
      (fun a => (hall a).exists)
    rw [vertexDegree_eq_valence, valence_eq_graphStar_rayCount D.graph v t]
    exact htwo
lemma graphStar_full_model_of_interior_neighborhood
    {G : EmbeddedGraph S} {p : M} (t : GraphStar G p)
    (ht : t.neighborhood ⊆ (intrinsicBoundary S)ᶜ) :
    ∀ z : Plane, ‖z‖ < t.radius →
      toPlane.symm (coordinates t.chart p + z) ∈ modelSet 2 kind := by
  cases kind with
  | euclidean => exact fun _ _ => mem_univ _
  | halfSpace => exact graphStar_full_model_of_avoids_boundary t ht

/-- Interior vertices fill a full metric tangent plane for either original
model kind. Nondegeneracy is derived from the actual regions. -/
theorem interior_incident_metric_sectors
    (g : RiemannianMetric S) (D : RegionDecomposition S) (v : Fin D.graph.vertexCount)
    (hp : D.graph.vertex v ∉ intrinsicBoundary S)
    (o : Orientation ℝ (TangentSpace S (D.graph.vertex v)) (Fin 2)) :
    ∃ t : GraphStar D.graph (D.graph.vertex v),
      ∃ e : Equiv.Perm (Fin t.rayCount),
        ∃ E : {r : Fin D.regionCount // D.graph.vertex v ∈ regionClosure D r} ≃ Fin t.rayCount,
          (∀ r, regionInterior D r.val ∩ t.neighborhood =
            starMetricSector g t o (t.direction (e (E r)))
              (t.direction (e (finRotate t.rayCount (E r))))) ∧
          (∑ r, starMetricAngle g t o (t.direction (e (E r)))
            (t.direction (e (finRotate t.rayCount (E r))))) = 2 * Real.pi := by
  have hpG : D.graph.vertex v ∈ D.graph.carrier := Or.inl ⟨v, rfl⟩
  obtain ⟨t, ht, Er, hEr⟩ := exists_incident_region_sector_equiv D (D.graph.vertex v)
    hpG (intrinsicBoundary S)ᶜ (SmoothManifolds.isClosed_intrinsicBoundary S).isOpen_compl hp
  have hfull := graphStar_full_model_of_interior_neighborhood t ht
  have htpos : 0 < t.rayCount := by
    have hv := two_le_vertexDegree D v
    rw [vertexDegree_eq_valence, valence_eq_graphStar_rayCount D.graph v t] at hv
    omega
  obtain ⟨e, Em, hEm, hsum⟩ := P202.RadialGraphSectors.fullStarMetricSectors g t o hfull htpos
  let E := Er.symm.trans Em
  refine ⟨t, e, E, ?_, ?_⟩
  · intro r
    have hr := hEr (Er.symm r)
    rw [Er.apply_symm_apply] at hr
    exact hr.trans (hEm (Er.symm r))
  · exact (Equiv.sum_comp E (fun i : Fin t.rayCount => starMetricAngle g t o
      (t.direction (e i)) (t.direction (e (finRotate t.rayCount i))))).trans hsum

/-- The full-plane count holds at every genuine interior vertex, including
interior vertices represented by half-space atlas charts. -/
theorem interior_incident_region_card
    (D : RegionDecomposition S) (v : Fin D.graph.vertexCount)
    (hp : D.graph.vertex v ∉ intrinsicBoundary S) :
    Nat.card {r : Fin D.regionCount // D.graph.vertex v ∈ regionClosure D r} =
      vertexDegree D.graph v := by
  have hpG : D.graph.vertex v ∈ D.graph.carrier := Or.inl ⟨v, rfl⟩
  obtain ⟨t, ht, E, _⟩ := exists_incident_region_sector_equiv D (D.graph.vertex v)
    hpG (intrinsicBoundary S)ᶜ (SmoothManifolds.isClosed_intrinsicBoundary S).isOpen_compl hp
  rw [← Nat.card_congr E]
  have hc := P202.RadialGraphSectors.fullStar_component_card t
    (graphStar_full_model_of_interior_neighborhood t ht)
  have hd : t.rayCount = vertexDegree D.graph v :=
    (valence_eq_graphStar_rayCount D.graph v t).symm.trans
      (vertexDegree_eq_valence D.graph v).symm
  have hv : vertexDegree D.graph v ≠ 0 := by have := two_le_vertexDegree D v; omega
  simpa only [hd, if_neg hv] using hc

namespace AngularMeasure
open MeasureTheory
open scoped ENNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

local notation "positiveAngle" => (P202Specs.RegionalCornerTransport.positiveAngle : AddCircle (2 * Real.pi) → ℝ)

lemma coe_positiveAngle (theta : AddCircle (2 * Real.pi)) :
    (positiveAngle theta : AddCircle (2 * Real.pi)) = theta := by
  change (positiveAngle theta : Real.Angle) = theta
  unfold P202Specs.RegionalCornerTransport.positiveAngle
  split
  · exact Real.Angle.coe_toReal _
  · exact (Real.Angle.coe_add _ _).trans
      ((congrArg₂ (· + ·) (Real.Angle.coe_toReal (show Real.Angle from theta)) Real.Angle.coe_two_pi).trans (add_zero _))

lemma positiveAngle_mem (theta : AddCircle (2 * Real.pi)) :
    positiveAngle theta ∈ Ioc 0 (2 * Real.pi) := by
  obtain ⟨hl, hu⟩ := Real.Angle.toReal_mem_Ioc theta
  unfold P202Specs.RegionalCornerTransport.positiveAngle
  split <;> constructor <;> linarith [Real.pi_pos]

lemma positiveAngle_eq_equivIoc (theta : AddCircle (2 * Real.pi)) :
    positiveAngle theta = (AddCircle.equivIoc (2 * Real.pi) 0 theta).val := by
  have h := AddCircle.equivIoc_coe_eq (p := 2 * Real.pi) (a := 0)
    (by simpa only [zero_add] using positiveAngle_mem theta)
  change (AddCircle.equivIoc (2 * Real.pi) 0) ((positiveAngle theta : AddCircle (2 * Real.pi))) = _ at h
  rw [coe_positiveAngle] at h
  exact (congrArg Subtype.val h).symm

lemma measurable_positiveAngle : Measurable (fun theta : AddCircle (2 * Real.pi) => positiveAngle theta) := by
  have h : (fun theta : AddCircle (2 * Real.pi) => positiveAngle theta) = (fun theta : AddCircle (2 * Real.pi) => (AddCircle.equivIoc (2 * Real.pi) 0 theta).val) := funext positiveAngle_eq_equivIoc
  rw [h]
  exact measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (2 * Real.pi) 0).measurable

lemma volume_positiveAngle_lt {alpha : ℝ} (ha : 0 < alpha) (hb : alpha ≤ 2 * Real.pi) :
    volume {theta : AddCircle (2 * Real.pi) | positiveAngle theta < alpha} = ENNReal.ofReal alpha := by
  have hp := AddCircle.add_projection_respects_measure (2 * Real.pi) 0
    (measurable_positiveAngle (measurableSet_Iio : MeasurableSet (Iio alpha)))
  change volume (positiveAngle ⁻¹' Iio alpha : Set (AddCircle (2 * Real.pi))) = _
  apply hp.trans
  have hs : (QuotientAddGroup.mk ⁻¹' {theta : AddCircle (2 * Real.pi) | positiveAngle theta < alpha}) ∩
      Ioc 0 (0 + 2 * Real.pi) = Ioo 0 alpha := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_Ioc, mem_Ioo, zero_add]
    constructor
    · rintro ⟨hx, hxp, hxu⟩
      have he : positiveAngle (x : AddCircle (2 * Real.pi)) = x := by
        have hh := AddCircle.equivIoc_coe_eq (p := 2 * Real.pi) (a := 0)
          (show x ∈ Ioc 0 (0 + 2 * Real.pi) by simpa using And.intro hxp hxu)
        rw [positiveAngle_eq_equivIoc, hh]
      exact ⟨hxp, by simpa only [he] using hx⟩
    · rintro ⟨hxp, hxa⟩
      have hxu : x ≤ 2 * Real.pi := hxa.le.trans hb
      have he : positiveAngle (x : AddCircle (2 * Real.pi)) = x := by
        have hh := AddCircle.equivIoc_coe_eq (p := 2 * Real.pi) (a := 0)
          (show x ∈ Ioc 0 (0 + 2 * Real.pi) by simpa using And.intro hxp hxu)
        rw [positiveAngle_eq_equivIoc, hh]
      exact ⟨by simpa only [he] using hxa, hxp, hxu⟩
  apply (congrArg volume hs).trans
  rw [Real.volume_Ioo, sub_zero]



lemma volume_translated_positiveAngle_lt (a : AddCircle (2 * Real.pi))
    {alpha : ℝ} (ha : 0 < alpha) (hb : alpha ≤ 2 * Real.pi) :
    volume {theta : AddCircle (2 * Real.pi) | positiveAngle (theta - a) < alpha} = ENNReal.ofReal alpha := by
  have h := measure_preimage_add (volume : Measure (AddCircle (2 * Real.pi))) (-a)
    {theta : AddCircle (2 * Real.pi) | positiveAngle theta < alpha}
  have he : {theta : AddCircle (2 * Real.pi) | positiveAngle (theta - a) < alpha} =
      (fun theta => -a + theta) ⁻¹' {theta | positiveAngle theta < alpha} := by
    ext theta
    simp only [mem_preimage, mem_ofPred_eq, sub_eq_add_neg, add_comm]
  rw [he, h]
  exact volume_positiveAngle_lt ha hb


lemma volume_reversed_positiveAngle_lt (a : AddCircle (2 * Real.pi))
    {alpha : ℝ} (ha : 0 < alpha) (hb : alpha ≤ 2 * Real.pi) :
    volume {theta : AddCircle (2 * Real.pi) | positiveAngle (a - theta) < alpha} = ENNReal.ofReal alpha := by
  have h := Measure.measure_preimage_neg (volume : Measure (AddCircle (2 * Real.pi)))
    {theta : AddCircle (2 * Real.pi) | positiveAngle (theta - -a) < alpha}
  have he : {theta : AddCircle (2 * Real.pi) | positiveAngle (a - theta) < alpha} =
      Neg.neg ⁻¹' {theta : AddCircle (2 * Real.pi) | positiveAngle (theta - -a) < alpha} := by
    ext theta
    simp only [mem_preimage, mem_ofPred_eq, sub_neg_eq_add, sub_eq_add_neg, neg_neg, add_comm]
  rw [he, h]
  exact volume_translated_positiveAngle_lt (-a) ha hb

lemma angular_width_eq_of_eq_outside_finite
    (a b : AddCircle (2 * Real.pi)) (rev : Bool)
    {alpha beta : ℝ} (ha : 0 < alpha) (ha' : alpha ≤ 2 * Real.pi)
    (hb : 0 < beta) (hb' : beta ≤ 2 * Real.pi)
    (F : Set (AddCircle (2 * Real.pi))) (hF : F.Finite)
    (he : ∀ theta ∉ F,
      ((if rev then positiveAngle (a - theta) else positiveAngle (theta - a)) < alpha ↔
        positiveAngle (theta - b) < beta)) : alpha = beta := by
  haveI : NullSingletonClass (volume : Measure (AddCircle (2 * Real.pi))) := ⟨fun theta => by
    rw [← Metric.closedBall_zero]
    simpa using (AddCircle.volume_closedBall (T := 2 * Real.pi) (x := theta) 0)⟩
  have hae : ∀ᵐ theta : AddCircle (2 * Real.pi), theta ∉ F := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using hF.measure_zero (volume : Measure (AddCircle (2 * Real.pi)))
  have heq : {theta : AddCircle (2 * Real.pi) | (if rev then positiveAngle (a - theta)
      else positiveAngle (theta - a)) < alpha} =ᵐ[volume]
      {theta : AddCircle (2 * Real.pi) | positiveAngle (theta - b) < beta} := by
    filter_upwards [hae] with theta htheta
    exact propext (he theta htheta)
  have hv := measure_congr heq
  have hva : volume {theta : AddCircle (2 * Real.pi) | (if rev then positiveAngle (a - theta)
      else positiveAngle (theta - a)) < alpha} = ENNReal.ofReal alpha := by
    cases rev
    · exact volume_translated_positiveAngle_lt a ha ha'
    · exact volume_reversed_positiveAngle_lt a ha ha'
  rw [hva, volume_translated_positiveAngle_lt b hb hb'] at hv
  simpa only [ENNReal.toReal_ofReal ha.le, ENNReal.toReal_ofReal hb.le] using congrArg ENNReal.toReal hv


lemma finite_angular_partition_angle_sum
    {I : Type*} [Fintype I] (a : I → AddCircle (2 * Real.pi))
    (rev : I → Bool) (alpha : I → ℝ)
    (ha : ∀ i, 0 < alpha i) (ha' : ∀ i, alpha i ≤ 2 * Real.pi)
    (F C : Set (AddCircle (2 * Real.pi))) (hF : F.Finite)
    (hdis : ∀ theta ∉ F, ∀ i j,
      (if rev i then positiveAngle (a i - theta) else positiveAngle (theta - a i)) < alpha i →
      (if rev j then positiveAngle (a j - theta) else positiveAngle (theta - a j)) < alpha j → i = j)
    (hcover : ∀ theta ∉ F, theta ∈ C ↔ ∃ i,
      (if rev i then positiveAngle (a i - theta) else positiveAngle (theta - a i)) < alpha i) :
    ∑ i, alpha i = (volume C).toReal := by
  classical
  let arc := fun i => {theta : AddCircle (2 * Real.pi) |
    (if rev i then positiveAngle (a i - theta) else positiveAngle (theta - a i)) < alpha i}
  let arc' := fun i => arc i \ F
  haveI : NullSingletonClass (volume : Measure (AddCircle (2 * Real.pi))) := ⟨fun theta => by
    rw [← Metric.closedBall_zero]
    simpa using (AddCircle.volume_closedBall (T := 2 * Real.pi) (x := theta) 0)⟩
  have hF0 : volume F = 0 := hF.measure_zero _
  have hmeas (i : I) : MeasurableSet (arc i) := by
    change MeasurableSet ((fun theta : AddCircle (2 * Real.pi) =>
      if rev i then positiveAngle (a i - theta) else positiveAngle (theta - a i)) ⁻¹' Iio (alpha i))
    apply MeasurableSet.preimage measurableSet_Iio
    cases hr : rev i
    · exact measurable_positiveAngle.comp (measurable_id.sub measurable_const)
    · exact measurable_positiveAngle.comp (measurable_const.sub measurable_id)
  have hvol (i : I) : volume (arc' i) = ENNReal.ofReal (alpha i) := by
    change volume (arc i \ F) = _
    rw [measure_sdiff_null hF0]
    dsimp only [arc]
    cases hr : rev i
    · exact volume_translated_positiveAngle_lt (a i) (ha i) (ha' i)
    · exact volume_reversed_positiveAngle_lt (a i) (ha i) (ha' i)
  have hdis' : Pairwise (Function.onFun Disjoint arc') := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro theta ⟨hi, htheta⟩ ⟨hj, _⟩
    exact hij (hdis theta htheta i j hi hj)
  have hunion : (⋃ i, arc' i) = C \ F := by
    ext theta
    simp only [mem_iUnion, Set.mem_sdiff, arc', arc, mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, htheta⟩
      exact ⟨(hcover theta htheta).mpr ⟨i, hi⟩, htheta⟩
    · rintro ⟨hc, htheta⟩
      obtain ⟨i, hi⟩ := (hcover theta htheta).mp hc
      exact ⟨i, hi, htheta⟩
  have hsum : volume C = ∑ i, ENNReal.ofReal (alpha i) := by
    calc
      volume C = volume (C \ F) := (measure_sdiff_null hF0).symm
      _ = volume (⋃ i, arc' i) := congrArg volume hunion.symm
      _ = ∑' i, volume (arc' i) := measure_iUnion hdis' (fun i => (hmeas i).diff hF.measurableSet)
      _ = ∑ i, ENNReal.ofReal (alpha i) := by simp only [tsum_fintype, hvol]
  rw [hsum, ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (ha _).le]


end AngularMeasure


lemma edge_parameter_interior_of_avoids_vertices (G : EmbeddedGraph S)
    (i : Fin G.edgeCount) (t : unitInterval)
    (hpv : G.edge i t ∉ range G.vertex) :
    0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
  constructor
  · by_contra ht
    have ht0 : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
    exact hpv ⟨G.initial i, (G.at_zero i).symm.trans (congrArg (G.edge i) ht0).symm⟩
  · by_contra ht
    have ht1 : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht))
    exact hpv ⟨G.terminal i, (G.at_one i).symm.trans (congrArg (G.edge i) ht1).symm⟩

lemma exists_open_edge_of_mem_carrier (G : EmbeddedGraph S) {p : M}
    (hp : p ∈ G.carrier) (hpv : p ∉ range G.vertex) :
    ∃ (i : Fin G.edgeCount) (t : unitInterval),
      0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ G.edge i t = p := by
  obtain hp | hp := hp
  · exact False.elim (hpv hp)
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hp
  exact ⟨i,t,(edge_parameter_interior_of_avoids_vertices G i t hpv).1,
    (edge_parameter_interior_of_avoids_vertices G i t hpv).2,rfl⟩

lemma open_edge_parameter_neighborhood (G : EmbeddedGraph S) (i : Fin G.edgeCount)
    (t : unitInterval) (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ O : Set M, IsOpen O ∧ G.edge i t ∈ O ∧
      ∀ x ∈ O, x ∈ G.carrier →
        ∃ q : unitInterval, G.edge i q = x ∧ |(q : ℝ) - t| < δ := by
  classical
  letI := S.topologicalManifold.hausdorff
  let Kpar : Set unitInterval := {q | δ ≤ |(q : ℝ) - t|}
  have hKpar : IsClosed Kpar := isClosed_le continuous_const
    ((continuous_subtype_val.sub continuous_const).abs)
  let K : Set M := (range G.vertex ∪
    ⋃ j : {j : Fin G.edgeCount // j ≠ i}, range (G.edge j.val)) ∪
      (G.edge i) '' Kpar
  have hcompact : IsCompact K := by
    apply IsCompact.union
    · exact (Set.finite_range G.vertex).isCompact.union
        (isCompact_iUnion (fun j : {j : Fin G.edgeCount // j ≠ i} =>
          isCompact_range (G.edge j.val).continuous))
    · exact hKpar.isCompact.image (G.edge i).continuous
  have hpv := G.avoids_vertices i t ht.1 ht.2
  have hpn : G.edge i t ∉ K := by
    rintro ((hp | hp) | hp)
    · exact hpv hp
    · obtain ⟨j,q,hq⟩ := mem_iUnion.mp hp
      have hqv : G.edge j.val q ∉ range G.vertex := by rwa [hq]
      exact Set.disjoint_left.mp (G.disjoint_open_edges j.property.symm)
        ⟨t,ht,rfl⟩ ⟨q,edge_parameter_interior_of_avoids_vertices G j.val q hqv,hq⟩
    · obtain ⟨q,hq,heq⟩ := hp
      have hqv : G.edge i q ∉ range G.vertex := by rwa [heq]
      have hqt : q = t := G.open_injective i
        (edge_parameter_interior_of_avoids_vertices G i q hqv) ht heq
      subst q
      exact hδ.not_ge (by simpa only [Kpar,mem_setOf_eq,sub_self,abs_zero] using hq)
  refine ⟨Kᶜ,hcompact.isClosed.isOpen_compl,hpn,?_⟩
  intro x hx hxG
  obtain hxv | hxe := hxG
  · exact False.elim (hx (Or.inl (Or.inl hxv)))
  obtain ⟨j,q,hq⟩ := mem_iUnion.mp hxe
  have hji : j = i := by
    by_contra hne
    exact hx (Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨j,hne⟩,q,hq⟩)))
  subst j
  refine ⟨q,hq,?_⟩
  by_contra hn
  exact hx (Or.inr ⟨q,le_of_not_gt hn,hq⟩)

/-- At an actual open-edge point every ray in a genuine graph star lies
in the line of the nonzero smooth edge derivative. -/
lemma graphStar_two_antipodal_rays_of_open_edge
    (G : EmbeddedGraph S) (i : Fin G.edgeCount) (t : unitInterval)
    (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1)
    (g : GraphStar G (G.edge i t)) :
    ∃ kplus kminus : Fin g.rayCount,
      g.direction kminus = -g.direction kplus ∧
        ∀ k : Fin g.rayCount, k = kplus ∨ k = kminus := by
  let c : ℝ → M := fun s => IccExtend zero_le_one (G.edge i) ((t : ℝ) + s)
  have hc : Continuous c := (G.edge i).continuous.Icc_extend'.comp
    (continuous_const.add continuous_id)
  have hc0 : c 0 = G.edge i t := by
    dsimp [c]
    rw [add_zero,IccExtend_of_mem zero_le_one (G.edge i) t.property]
  have hcN : c ⁻¹' g.neighborhood ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by
      rw [hc0]
      exact (GraphStar.isOpen_neighborhood g).mem_nhds (GraphStar.mem_neighborhood g))
  obtain ⟨ε,hε,hεN⟩ := Metric.mem_nhds_iff.mp hcN
  let δ : ℝ := min (min ε (t : ℝ)) (1-t) / 2
  have hδ : 0 < δ := div_pos (lt_min (lt_min hε ht.1) (sub_pos.mpr ht.2)) (by norm_num)
  have hδε : δ < ε := by
    have := min_le_left (min ε (t : ℝ)) (1-t)
    have := min_le_left ε (t : ℝ)
    dsimp [δ] at *
    linarith
  have hδt : δ < (t : ℝ) := by
    have := min_le_left (min ε (t : ℝ)) (1-t)
    have := min_le_right ε (t : ℝ)
    dsimp [δ] at *
    linarith
  have hδ1 : δ < 1-(t : ℝ) := by
    have := min_le_right (min ε (t : ℝ)) (1-t)
    dsimp [δ] at *
    linarith
  have hparam (s : ℝ) (hs : |s| ≤ δ) : (t : ℝ)+s ∈ Ioo (0 : ℝ) 1 := by
    have hab := abs_le.mp hs
    constructor <;> linarith [hab.1,hab.2]
  have hmem (s : ℝ) (hs : |s| ≤ δ) : c s ∈ g.neighborhood := by
    apply hεN
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    exact hs.trans_lt hδε
  have hne (s : ℝ) (hs : |s| ≤ δ) (hs0 : s ≠ 0) : c s ≠ G.edge i t := by
    intro heq
    have hp := hparam s hs
    have hq := G.open_injective i hp ht (by
      simpa only [c,IccExtend_of_mem zero_le_one (G.edge i) ⟨hp.1.le,hp.2.le⟩] using heq)
    have := congrArg (fun q : unitInterval => (q : ℝ)) hq
    exact hs0 (by dsimp at this; linarith)
  have hgraph (s : ℝ) : c s ∈ G.carrier := Or.inr (mem_iUnion.mpr ⟨i,_,rfl⟩)
  have hplus (s : ℝ) (hs : s ∈ Icc (0 : ℝ) δ) : |s| ≤ δ := by
    simpa only [abs_of_nonneg hs.1] using hs.2
  have hminus (s : ℝ) (hs : s ∈ Icc (0 : ℝ) δ) : |-s| ≤ δ := by
    simpa only [abs_neg] using hplus s hs
  obtain ⟨kplus,hkplus⟩ := BoundaryCycles.fixed_ray_of_graphStar_arc g c δ hδ
    hc.continuousOn (fun s hs => hmem s (hplus s hs))
    (fun s hs => hne s (hplus s ⟨hs.1.le,hs.2.le⟩) hs.1.ne')
    (fun s _ => hgraph s)
  obtain ⟨kminus,hkminus⟩ := BoundaryCycles.fixed_ray_of_graphStar_arc g (fun s => c (-s)) δ hδ
    (hc.comp continuous_neg).continuousOn (fun s hs => hmem (-s) (hminus s hs))
    (fun s hs => hne (-s) (hminus s ⟨hs.1.le,hs.2.le⟩) (neg_ne_zero.mpr hs.1.ne'))
    (fun s _ => hgraph (-s))
  let F : ℝ → Plane := fun s => coordinates g.chart (IccExtend zero_le_one (G.edge i) s)
  have hF := RegularOpenEdge.in_chart (G.regular i) (t : ℝ) ht
    g.chart g.chart_mem g.mem_source
  let v : Plane := deriv F t
  have hv : v ≠ 0 := hF.2
  have hdplus : HasDerivAt (fun s => coordinates g.chart (c s)) v 0 := by
    have hd : HasDerivAt F v ((t : ℝ)+(0 : ℝ)) := by
      simpa only [F,v,add_zero] using (hF.1.differentiableAt (by simp)).hasDerivAt
    simpa only [c,F,Function.comp_def,one_smul] using hd.scomp 0
      ((hasDerivAt_id (0 : ℝ)).const_add (t : ℝ))
  have hdminus : HasDerivAt (fun s => coordinates g.chart (c (-s))) (-v) 0 := by
    have hd : HasDerivAt (fun s => coordinates g.chart (c s)) v (-(0 : ℝ)) := by
      simpa only [neg_zero] using hdplus
    simpa only [Function.comp_def,neg_one_smul] using hd.scomp 0 (hasDerivAt_neg (0 : ℝ))
  have hcoordne (s : ℝ) (hs : |s| ≤ δ) (hs0 : s ≠ 0) :
      coordinates g.chart (c s) - coordinates g.chart (c 0) ≠ 0 := by
    intro heq
    apply hne s hs hs0
    rw [hc0] at heq
    exact coordinates_injOn g.chart (hmem s hs).1 g.mem_source (sub_eq_zero.mp heq)
  obtain ⟨r,hr,hrv⟩ := BoundaryCycles.derivative_points_along_ray
    (fun s => coordinates g.chart (c s)) v (g.direction kplus) hdplus hv
    (g.direction_unit kplus) δ hδ
    (fun s hs => hcoordne s (hplus s ⟨hs.1.le,hs.2.le⟩) hs.1.ne')
    (by simpa only [hc0] using hkplus)
  obtain ⟨q,hq,hqv⟩ := BoundaryCycles.derivative_points_along_ray
    (fun s => coordinates g.chart (c (-s))) (-v) (g.direction kminus) hdminus
    (neg_ne_zero.mpr hv) (g.direction_unit kminus) δ hδ
    (by
      intro s hs
      simpa only [neg_zero] using hcoordne (-s)
        (hminus s ⟨hs.1.le,hs.2.le⟩) (neg_ne_zero.mpr hs.1.ne'))
    (by simpa only [neg_zero,hc0] using hkminus)
  have hvr : ‖v‖ = r := by
    rw [hrv,norm_smul,g.direction_unit,Real.norm_eq_abs,abs_of_pos hr,mul_one]
  have hvq : ‖v‖ = q := by
    have hh := congrArg norm hqv
    simpa only [norm_neg,norm_smul,g.direction_unit,Real.norm_eq_abs,
      abs_of_pos hq,mul_one] using hh
  have hqr : q = r := hvq.symm.trans hvr
  have hopposite : g.direction kminus = -g.direction kplus := by
    rw [hqr,hrv,← smul_neg] at hqv
    exact (smul_right_injective _ hr.ne' hqv).symm
  refine ⟨kplus,kminus,hopposite,?_⟩
  intro k
  obtain ⟨O,hO,htO,hOparam⟩ := open_edge_parameter_neighborhood G i t ht δ hδ
  obtain ⟨x,hxO,hxN,hxp,a,ha,har,hxa⟩ :=
    BoundaryCycles.graphStar_ray_meets_open g k O hO htO
  have hxG : x ∈ G.carrier := (g.graph_eq x hxN.1 hxN.2).mpr
    (Or.inr ⟨k,a,ha,har,hxa⟩)
  obtain ⟨s,hsx,hsδ⟩ := hOparam x hxO hxG
  have hst : (s : ℝ) ≠ t := by
    intro heq
    exact hxp (hsx.symm.trans (congrArg (G.edge i) (Subtype.ext heq)))
  have hcs : c ((s : ℝ)-t) = x := by
    dsimp [c]
    rw [add_sub_cancel,IccExtend_of_mem zero_le_one (G.edge i) s.property,hsx]
  have hnorm : ‖coordinates g.chart x - coordinates g.chart (G.edge i t)‖ = a := by
    rw [hxa,add_sub_cancel_left,norm_smul,g.direction_unit,Real.norm_eq_abs,
      abs_of_pos ha,mul_one]
  rcases lt_or_gt_of_ne hst with hslt | hsgt
  · have hspos : (t : ℝ)-s ∈ Ioo (0 : ℝ) δ := by
      constructor
      · linarith
      · have hh := abs_lt.mp hsδ; linarith [hh.1]
    have heq := hkminus ((t : ℝ)-s) hspos
    have hneg : -((t : ℝ)-s) = (s : ℝ)-t := by ring
    rw [hneg,hcs,hnorm,hxa,add_sub_cancel_left] at heq
    have hdirs : g.direction k = g.direction kminus :=
      (smul_right_injective _ ha.ne') heq
    exact Or.inr (g.direction_injective hdirs)
  · have hspos : (s : ℝ)-t ∈ Ioo (0 : ℝ) δ :=
      ⟨sub_pos.mpr hsgt,lt_of_le_of_lt (le_abs_self _) hsδ⟩
    have heq := hkplus ((s : ℝ)-t) hspos
    rw [hcs,hnorm,hxa,add_sub_cancel_left] at heq
    have hdirs : g.direction k = g.direction kplus :=
      (smul_right_injective _ ha.ne') heq
    exact Or.inl (g.direction_injective hdirs)


/-- The two rays at a regular open edge span its genuine tangent line. -/
lemma graphStar_directions_in_line_of_open_edge
    (G : EmbeddedGraph S) (i : Fin G.edgeCount) (t : unitInterval)
    (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1)
    (g : GraphStar G (G.edge i t)) :
    ∃ v : Plane, v ≠ 0 ∧ ∀ k : Fin g.rayCount, ∃ a : ℝ, g.direction k = a • v := by
  obtain ⟨kplus,kminus,hopposite,hall⟩ :=
    graphStar_two_antipodal_rays_of_open_edge G i t ht g
  refine ⟨g.direction kplus,?_,?_⟩
  · exact norm_ne_zero_iff.mp (by rw [g.direction_unit]; norm_num)
  · intro k
    obtain rfl | rfl := hall k
    · exact ⟨1,(one_smul ℝ _).symm⟩
    · exact ⟨-1,by simpa only [neg_one_smul] using hopposite⟩


lemma graphStar_rayCount_eq_two_of_antipodal_pair
    {G : EmbeddedGraph S} {p : M} (g : GraphStar G p)
    (kplus kminus : Fin g.rayCount)
    (hopposite : g.direction kminus = -g.direction kplus)
    (hall : ∀ k : Fin g.rayCount, k = kplus ∨ k = kminus) :
    g.rayCount = 2 := by
  have hne : kminus ≠ kplus := by
    intro heq
    have hh : g.direction kplus = -g.direction kplus := by
      simpa only [heq] using hopposite
    have hz : (2 : ℝ) • g.direction kplus = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hh
    have hzero : g.direction kplus = 0 :=
      (smul_eq_zero.mp hz).resolve_left (by norm_num)
    have hunit := g.direction_unit kplus
    rw [hzero,norm_zero] at hunit
    norm_num at hunit
  let f : Bool → Fin g.rayCount := fun b => if b then kminus else kplus
  have hinj : Function.Injective f := by
    intro b c hbc
    cases b <;> cases c <;> simp only [f,Bool.false_eq_true,ite_false,ite_true] at hbc ⊢
    · exact False.elim (hne hbc.symm)
    · exact False.elim (hne hbc)
  have hsurj : Function.Surjective f := by
    intro k
    obtain h | h := hall k
    · exact ⟨false,by simpa only [f,Bool.false_eq_true,ite_false] using h.symm⟩
    · exact ⟨true,by simpa only [f,ite_true] using h.symm⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)
  simpa only [Fintype.card_bool,Fintype.card_fin] using hc.symm



namespace AngularPhase
variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma rotation_normalize_exclusion (o : Orientation ℝ V (Fin 2))
    (L : V ≃ₗ[ℝ] E) {w : V} (hw : w ≠ 0) {b : E} (hb : b ≠ 0)
    (theta : Real.Angle) (htheta : theta ≠ o.oangle w (L.symm b)) :
    NormedSpace.normalize (L (o.rotation theta w)) ≠ NormedSpace.normalize b := by
  intro he
  have hx : L (o.rotation theta w) ≠ 0 := L.map_ne_zero_iff.mpr ((o.rotation theta).map_ne_zero_iff.mpr hw)
  have hsr : SameRay ℝ (L (o.rotation theta w)) b := by
    apply (sameRay_iff_inv_norm_smul_eq_of_ne hx hb).mpr
    exact he
  have hsr' : SameRay ℝ (o.rotation theta w) (L.symm b) := by
    apply (SameRay.sameRay_map_iff L).mp
    simpa only [L.apply_symm_apply] using hsr
  have he0 : o.oangle (o.rotation theta w) (L.symm b) = 0 := o.oangle_eq_zero_iff_sameRay.mpr hsr'
  have hb' : L.symm b ≠ 0 := L.symm.map_ne_zero_iff.mpr hb
  have hangle : o.oangle w (o.rotation theta w) + o.oangle (o.rotation theta w) (L.symm b) = o.oangle w (L.symm b) :=
    o.oangle_add hw ((o.rotation theta).map_ne_zero_iff.mpr hw) hb'
  rw [o.oangle_rotation_self_right hw, he0, add_zero] at hangle
  exact htheta hangle

lemma rotation_phase_angles (o : Orientation ℝ V (Fin 2))
    {w b : V} (hw : w ≠ 0) (hb : b ≠ 0) (theta : Real.Angle) :
    o.oangle b (o.rotation theta w) = theta - o.oangle w b ∧
      o.oangle (o.rotation theta w) b = o.oangle w b - theta := by
  have hx : o.rotation theta w ≠ 0 := (o.rotation theta).map_ne_zero_iff.mpr hw
  constructor
  · rw [← o.oangle_sub_left hw hb hx, o.oangle_rotation_self_right hw]
  · exact o.oangle_rotation_left hw hb theta

lemma occupied_test_angular_arc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (o : Orientation ℝ V (Fin 2)) (Le : V ≃ₗ[ℝ] E) (Ld : V ≃ₗ[ℝ] F)
    {w : V} (hw : w ≠ 0) {b d : F} (hb : b ≠ 0) (hd : d ≠ 0)
    (P : E → Prop) (rev : Bool) (alpha : ℝ)
    (htest : ∀ u : E, u ≠ 0 →
      NormedSpace.normalize (Ld (Le.symm u)) ≠ NormedSpace.normalize b →
      NormedSpace.normalize (Ld (Le.symm u)) ≠ NormedSpace.normalize d →
      (P u ↔ (if rev then P202Specs.RegionalCornerTransport.positiveAngle
        (o.oangle (Le.symm u) (Ld.symm b)) else P202Specs.RegionalCornerTransport.positiveAngle
        (o.oangle (Ld.symm b) (Le.symm u))) < alpha)) :
    ∀ theta : Real.Angle,
      theta ≠ o.oangle w (Ld.symm b) → theta ≠ o.oangle w (Ld.symm d) →
      (P (Le (o.rotation theta w)) ↔
        (if rev then P202Specs.RegionalCornerTransport.positiveAngle (o.oangle w (Ld.symm b) - theta)
        else P202Specs.RegionalCornerTransport.positiveAngle (theta - o.oangle w (Ld.symm b))) < alpha) := by
  intro theta htheta htheta'
  have hu : Le (o.rotation theta w) ≠ 0 :=
    Le.map_ne_zero_iff.mpr ((o.rotation theta).map_ne_zero_iff.mpr hw)
  have hbo := rotation_normalize_exclusion o Ld hw hb theta htheta
  have hdi := rotation_normalize_exclusion o Ld hw hd theta htheta'
  have hbo' : NormedSpace.normalize (Ld (Le.symm (Le (o.rotation theta w)))) ≠ NormedSpace.normalize b := by
    simpa only [Le.symm_apply_apply] using hbo
  have hdi' : NormedSpace.normalize (Ld (Le.symm (Le (o.rotation theta w)))) ≠ NormedSpace.normalize d := by
    simpa only [Le.symm_apply_apply] using hdi
  have ht := htest (Le (o.rotation theta w)) hu hbo' hdi'
  rw [Le.symm_apply_apply] at ht
  have hb' : Ld.symm b ≠ 0 := Ld.symm.map_ne_zero_iff.mpr hb
  have hphase := rotation_phase_angles o hw hb' theta
  simpa only [hphase.1, hphase.2] using ht

end AngularPhase

namespace RadialGerms
lemma radial_homeomorph_component
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set X} {V : Set E} (H : U ≃ₜ V) (z : E)
    (hz : ∀ t ∈ Ioc (0 : ℝ) 1, t • z ∈ V) :
    ∃ a : ConnectedComponents U, ∀ t (ht : t ∈ Ioc (0 : ℝ) 1),
      (H.symm ⟨t • z, hz t ht⟩).val ∈ componentSet U a := by
  let f : Ioc (0 : ℝ) 1 → U := fun t => H.symm ⟨t.val • z, hz t.val t.property⟩
  have hf : Continuous f := H.symm.continuous.comp (by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.smul continuous_const)
  haveI : PreconnectedSpace (Ioc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ioc
  let one : Ioc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  refine ⟨ConnectedComponents.mk (f one), ?_⟩
  intro t ht
  refine ⟨f ⟨t, ht⟩, ?_, rfl⟩
  apply ConnectedComponents.coe_eq_coe'.mpr
  exact (isPreconnected_range hf).subset_connectedComponent ⟨one, rfl⟩ ⟨⟨t, ht⟩, rfl⟩

lemma radial_region_image_partition
    {X E I : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U B : Set X} {V : Set E} (H : U ≃ₜ V) (c : X → E) (base z : E)
    (hU : U ⊆ B) (hc : Set.InjOn c B)
    (hH : ∀ x : U, c x.val = base + (H x).val)
    (hz : ∀ t ∈ Ioc (0 : ℝ) 1, t • z ∈ V)
    (R : I → Set X) (hR : ∀ i, R i ⊆ B)
    (Q : ConnectedComponents U ≃ I)
    (hQ : ∀ i, R i ∩ U = componentSet U (Q.symm i)) :
    ∃ i : I, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ j : I,
      (base + t • z ∈ c '' R j ↔ j = i) := by
  obtain ⟨a, ha⟩ := radial_homeomorph_component H z hz
  refine ⟨Q a, ?_⟩
  intro t ht j
  let x : U := H.symm ⟨t • z, hz t ht⟩
  have hcx : c x.val = base + t • z := by
    rw [hH, H.apply_symm_apply]
  have hxa : x.val ∈ componentSet U a := ha t ht
  constructor
  · rintro ⟨y, hy, hcy⟩
    have hxy : y = x.val := hc (hR j hy) (hU x.property) (hcy.trans hcx.symm)
    have hxj : x.val ∈ componentSet U (Q.symm j) := by
      rw [← hQ]
      exact ⟨hxy ▸ hy, x.property⟩
    obtain ⟨xa, hxa, hxae⟩ := hxa
    obtain ⟨xj, hxj, hxje⟩ := hxj
    have hxaj : xa = xj := Subtype.ext (hxae.trans hxje.symm)
    have he : a = Q.symm j := hxa.symm.trans ((congrArg ConnectedComponents.mk hxaj).trans hxj)
    have heQ := congrArg Q he
    simpa only [Q.apply_symm_apply] using heQ.symm
  · intro hji
    subst j
    have hxR : x.val ∈ R (Q a) := by
      have hmem : x.val ∈ componentSet U (Q.symm (Q a)) := by
        simpa only [Q.symm_apply_apply] using hxa
      rw [← hQ] at hmem
      exact hmem.1
    exact ⟨x.val, hxR, hcx⟩

open Filter
open scoped _root_.Topology
lemma eventually_radial_region_image_partition
    {X E I : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U B : Set X} {V : Set E} (H : U ≃ₜ V) (c : X → E) (base u : E)
    (hU : U ⊆ B) (hc : Set.InjOn c B)
    (hH : ∀ x : U, c x.val = base + (H x).val)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hu : ∀ t ∈ Ioc (0 : ℝ) epsilon, t • u ∈ V)
    (R : I → Set X) (hR : ∀ i, R i ⊆ B)
    (Q : ConnectedComponents U ≃ I)
    (hQ : ∀ i, R i ∩ U = componentSet U (Q.symm i)) :
    ∃ i : I, ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ j : I,
      (base + t • u ∈ c '' R j ↔ j = i) := by
  have hz : ∀ t ∈ Ioc (0 : ℝ) 1, t • (epsilon • u) ∈ V := by
    intro t ht
    rw [smul_smul]
    exact hu (t * epsilon) ⟨mul_pos ht.1 hepsilon, mul_le_of_le_one_left hepsilon.le ht.2⟩
  obtain ⟨i, hi⟩ := radial_region_image_partition H c base (epsilon • u) hU hc hH hz R hR Q hQ
  refine ⟨i, ?_⟩
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < epsilon :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hepsilon)
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hte j
  have ht' : t / epsilon ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos ht hepsilon, (div_le_one hepsilon).mpr hte.le⟩
  have hs : (t / epsilon) • (epsilon • u) = t • u := by
    rw [smul_smul, div_mul_cancel₀ _ hepsilon.ne']
  simpa only [hs] using hi (t / epsilon) ht' j

end RadialGerms

open P202.SurfaceBoundaryData P202Specs.MetricBoundaryTurning
theorem listedCorner_angular_germ
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2))
    (w : TangentSpace S p.val) (hw : w ≠ 0)
    (A : ∀ i, ArcPresentation ((D.region r).curve i))
    (s : Fin (D.region r).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region r) s)
    (i : Fin (D.region r).boundaryCount) (j : Fin (A i).count)
    (hj : (A i).arc j 1 = coordinates (D.chart r) p.val)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hp : p.val ∈ e.source) :
    letI := (metricCore g p.val).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (metricCore g p.val).toCore
    letI : Fact (Module.finrank ℝ (TangentSpace S p.val) = 2) :=
      ⟨(SmoothManifolds.tangent_dimension S p.val).2⟩
    let Ke := (tangentStructure S).fiberCoordinates.equiv e he p.val hp
    let Kd := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    let Ld := Kd.trans toPlane.toLinearEquiv
    let alpha := P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
      G.ambientChart G.ambientChart_mem (A i) (s i) j
    let a := o.oangle w (Ld.symm (outgoingRay (A i) (s i) j))
    let b := o.oangle w (Ld.symm (incomingRay (A i) (s i) j))
    ∃ reversed : Bool, 0 < alpha ∧ alpha < 2 * Real.pi ∧
      ∀ theta : Real.Angle, theta ≠ a → theta ≠ b →
        ((∀ᶠ t : ℝ in 𝓝[>] 0, (e p.val).val + t • Ke (o.rotation theta w) ∈
            (fun q => (e q).val) '' (regionInterior D r ∩ e.source)) ↔
          (if reversed then positiveAngle (a - theta) else positiveAngle (theta - a)) < alpha) := by
  letI := (metricCore g p.val).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p.val).toCore
  letI : Fact (Module.finrank ℝ (TangentSpace S p.val) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p.val).2⟩
  dsimp only
  let Ke := (tangentStructure S).fiberCoordinates.equiv e he p.val hp
  let Kd := (tangentStructure S).fiberCoordinates.equiv
    (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
  let Ld := Kd.trans toPlane.toLinearEquiv
  obtain ⟨reversed, halpha, halpha', ht⟩ :=
    P202.GlobalGaussBonnet.CornerTransport.regionalChartGeometry_changed_chart_occupiedSectorAngle_transport
      g D r G p o A s hs i j hj e he hp
  refine ⟨reversed, halpha, halpha', ?_⟩
  have hout : outgoingRay (A i) (s i) j ≠ 0 := by
    unfold outgoingRay
    split
    · exact (A i).regular _ _ (by simp)
    · exact neg_ne_zero.mpr ((A i).regular _ _ (by simp))
  have hin : incomingRay (A i) (s i) j ≠ 0 := by
    unfold incomingRay
    split
    · exact neg_ne_zero.mpr ((A i).regular _ _ (by simp))
    · exact (A i).regular _ _ (by simp)
  apply AngularPhase.occupied_test_angular_arc o Ke Ld hw hout hin
    (fun u => ∀ᶠ t : ℝ in 𝓝[>] 0, (e p.val).val + t • u ∈
      (fun q => (e q).val) '' (regionInterior D r ∩ e.source)) reversed
    (P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
      G.ambientChart G.ambientChart_mem (A i) (s i) j)
  intro u hu huo hui
  have huo' : NormedSpace.normalize (toPlane
      (((Ke.symm.trans Kd).toContinuousLinearEquiv) u)) ≠
      NormedSpace.normalize (outgoingRay (A i) (s i) j) := huo
  have hui' : NormedSpace.normalize (toPlane
      (((Ke.symm.trans Kd).toContinuousLinearEquiv) u)) ≠
      NormedSpace.normalize (incomingRay (A i) (s i) j) := hui
  exact ht u hu huo' hui'


theorem graphStar_eventually_unique_incident_region
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (D : RegionDecomposition S) (p : M)
    (t : GraphStar D.graph p)
    (Q : ConnectedComponents (t.neighborhood \ D.graph.carrier : Set M) ≃
      {r : Fin D.regionCount // p ∈ regionClosure D r})
    (hQ : ∀ a, regionInterior D (Q a).val ∩ t.neighborhood =
      componentSet (t.neighborhood \ D.graph.carrier) a)
    (v : Euclidean 2) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hv : ∀ s ∈ Ioc (0 : ℝ) epsilon, s • toPlane v ∈
      (closedRays t.direction)ᶜ ∩ (centeredModel t ∩ Metric.ball 0 t.radius)) :
    ∃ r : {r : Fin D.regionCount // p ∈ regionClosure D r},
      ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ r' : {r : Fin D.regionCount // p ∈ regionClosure D r},
        ((t.chart p).val + s • v ∈ (fun q => (t.chart q).val) ''
          (regionInterior D r'.val ∩ t.chart.source) ↔ r' = r) := by
  let U := t.neighborhood \ D.graph.carrier
  let V := (closedRays t.direction)ᶜ ∩ (centeredModel t ∩ Metric.ball 0 t.radius)
  let H : U ≃ₜ V :=
    (P202.RadialGraphSectors.StarHomeomorph.centeredCoordinatesHomeomorph t U
      (fun _ hx => hx.1.1)).trans
        (Homeomorph.setCongr
          (P202.GlobalGaussBonnet.CornerTransport.graphStar_centered_coordinates_image t))
  let R := fun r : {r : Fin D.regionCount // p ∈ regionClosure D r} =>
    regionInterior D r.val ∩ t.chart.source
  have hH : ∀ x : U, coordinates t.chart x.val = coordinates t.chart p + (H x).val := by
    intro x
    change coordinates t.chart x.val = coordinates t.chart p +
      (coordinates t.chart x.val - coordinates t.chart p)
    abel
  have hRQ : ∀ r, R r ∩ U = componentSet U (Q.symm r) := by
    intro r
    have he := hQ (Q.symm r)
    rw [Q.apply_symm_apply] at he
    apply Set.Subset.antisymm
    · rintro q ⟨⟨hqR, _⟩, hqU⟩
      exact he ▸ ⟨hqR, hqU.1⟩
    · intro q hq
      have hqU : q ∈ U := Components.subset U (Q.symm r) hq
      have hqR : q ∈ regionInterior D r.val ∩ t.neighborhood := he.symm ▸ hq
      exact ⟨⟨hqR.1, hqU.1.1⟩, hqU⟩
  obtain ⟨r, hr⟩ := RadialGerms.eventually_radial_region_image_partition
    H (coordinates t.chart) (coordinates t.chart p) (toPlane v)
    (fun _ hx => hx.1.1) (P202.SurfaceRegionConstruction.coordinates_injOn t.chart)
    hH epsilon hepsilon hv R (fun _ => inter_subset_right) Q hRQ
  refine ⟨r, ?_⟩
  filter_upwards [hr] with s hs r'
  have he : (coordinates t.chart p + s • toPlane v ∈ coordinates t.chart '' R r') ↔
      (t.chart p).val + s • v ∈ (fun q => (t.chart q).val) '' R r' := by
    constructor
    · rintro ⟨q, hq, hcoord⟩
      refine ⟨q, hq, ?_⟩
      apply toPlane.injective
      simpa only [coordinates, map_add, map_smul] using hcoord
    · rintro ⟨q, hq, hcoord⟩
      exact ⟨q, hq, by simpa only [coordinates, map_add, map_smul] using congrArg toPlane hcoord⟩
  exact he.symm.trans (hs r')

/-- Every nonray model direction supplies a genuine short radial segment in
the exact star complement used by the regional component correspondence. -/
lemma exists_graphStar_short_ray {G : EmbeddedGraph S} {p : M}
    (t : GraphStar G p) (v : Plane) (hv : v ∉ closedRays t.direction)
    (hmodel : ∀ a : ℝ, 0 < a → ‖a • v‖ < t.radius → a • v ∈ centeredModel t) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ a ∈ Ioc (0 : ℝ) epsilon,
      a • v ∈ (closedRays t.direction)ᶜ ∩ (centeredModel t ∩ Metric.ball 0 t.radius) := by
  let epsilon := t.radius / (‖v‖ + 1)
  have hep : 0 < epsilon := div_pos t.radius_pos (by positivity)
  have heq : epsilon * (‖v‖ + 1) = t.radius :=
    div_mul_cancel₀ _ (by positivity)
  refine ⟨epsilon, hep, ?_⟩
  intro a ha
  have hn : ‖a • v‖ < t.radius := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha.1]
    have := mul_le_mul_of_nonneg_right ha.2 (norm_nonneg v)
    nlinarith
  refine ⟨CornerTransport.closedRays_compl_smul t.direction a ha.1 v hv,
    hmodel a ha.1 hn, ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right] using hn


/-- Two actual regions cannot both occupy the same chart ray germ. This is
uniqueness from chart injectivity and actual complementary components. -/
lemma region_chart_ray_germs_unique (D : RegionDecomposition S)
    (e : ModelChart 2 kind M) (base v : Euclidean 2)
    (r r' : Fin D.regionCount)
    (hr : ∀ᶠ t : ℝ in 𝓝[>] 0, base + t • v ∈
      (fun q => (e q).val) '' (regionInterior D r ∩ e.source))
    (hr' : ∀ᶠ t : ℝ in 𝓝[>] 0, base + t • v ∈
      (fun q => (e q).val) '' (regionInterior D r' ∩ e.source)) : r = r' := by
  obtain ⟨t, ht, ht'⟩ := (hr.and hr').exists
  obtain ⟨q, hq, heq⟩ := ht
  obtain ⟨q', hq', heq'⟩ := ht'
  have hqq' : q = q' := e.injOn hq.2 hq'.2 (Subtype.ext (heq.trans heq'.symm))
  subst q'
  by_contra hne
  exact Set.disjoint_left.mp (P202.SurfaceRegionsEuler.regionInteriors_disjoint D hne) hq.1 hq'.1


namespace AngularVolume
open MeasureTheory
open scoped ENNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
abbrev Circle := AddCircle (2 * Real.pi)
local instance : NullSingletonClass (volume : Measure Circle) where
  measure_singleton theta := by
    rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
    simp [Real.pi_pos.le]
lemma half_volume_of_antipodal (f : Circle → ℝ) (hf : Continuous f)
    (hanti : ∀ theta, f ((Real.pi : Circle) + theta) = -f theta)
    (hz : volume {theta | f theta = 0} = 0) :
    volume {theta | 0 < f theta} = ENNReal.ofReal Real.pi := by
  let P : Set Circle := {theta | 0 < f theta}
  let N : Set Circle := {theta | f theta < 0}
  have hPN : volume N = volume P := by
    have he : (fun theta : Circle => (Real.pi : Circle) + theta) ⁻¹' P = N := by
      ext theta
      change 0 < f ((Real.pi : Circle) + theta) ↔ f theta < 0
      rw [hanti]
      exact neg_pos
    simpa only [he] using (measure_preimage_add volume (Real.pi : Circle) P)
  have hzero : ∀ᵐ theta : Circle ∂volume, f theta ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_ne_iff] using hz
  have hae : N =ᵐ[volume] Pᶜ := by
    filter_upwards [hzero] with theta ht
    apply propext
    change f theta < 0 ↔ ¬0 < f theta
    exact ⟨fun h => not_lt_of_ge h.le, fun h => lt_of_le_of_ne (le_of_not_gt h) ht⟩
  have hmP : MeasurableSet P := measurableSet_lt measurable_const hf.measurable
  have hsum : volume P + volume P = ENNReal.ofReal (2 * Real.pi) := by
    calc
      volume P + volume P = volume P + volume Pᶜ := by rw [← measure_congr hae, hPN]
      _ = volume (Set.univ : Set Circle) := measure_add_measure_compl hmP
      _ = ENNReal.ofReal (2 * Real.pi) := AddCircle.measure_univ _
  have hpfin : volume P ≠ ⊤ := measure_ne_top _ _
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hpfin hpfin, ENNReal.toReal_ofReal (by positivity)] at hreal
  have hpR : (volume P).toReal = Real.pi := by linarith
  change volume P = _
  rw [← ENNReal.ofReal_toReal hpfin, hpR]

open P202Specs.PlanarRegionTopology P202Specs.PlaneTurning
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]

lemma rotation_linear_coordinate_zero_finite (o : Orientation ℝ V (Fin 2))
    (L : V ≃ₗ[ℝ] Plane) {w : V} (hw : w ≠ 0) :
    Set.Finite {theta : Circle | (L (o.rotation (show Real.Angle from theta) w)) 1 = 0} := by
  let b : V := L.symm reference
  have href : (reference : Plane) ≠ 0 := by
    intro h
    have hh := congrArg (fun z : Plane => z 0) h
    norm_num [reference] at hh
  have hb : b ≠ 0 := L.symm.map_ne_zero_iff.mpr href
  let beta : Circle := o.oangle w b
  apply (Set.toFinite ({beta, (Real.pi : Circle) + beta} : Set Circle)).subset
  intro theta ht
  let x : V := o.rotation (show Real.Angle from theta) w
  have hx : x ≠ 0 := (o.rotation (show Real.Angle from theta)).map_ne_zero_iff.mpr hw
  have hy : L x = (L x 0) • reference := by
    ext i
    fin_cases i
    · simp [reference]
    · simpa [reference] using ht
  have hmul : x = (L x 0) • b := by
    apply L.injective
    simpa only [map_smul, b, L.apply_symm_apply] using hy
  have hz := o.oangle_eq_zero_or_eq_pi_iff_right_eq_smul.mpr (Or.inr ⟨L x 0, hmul⟩)
  have hangle : o.oangle b x = (show Real.Angle from theta) - o.oangle w b := by
    rw [← o.oangle_sub_left hw hb hx, o.oangle_rotation_self_right hw]
  rcases hz with hz | hz
  · rw [hangle, sub_eq_zero] at hz
    exact Set.mem_insert_iff.mpr (Or.inl hz)
  · rw [hangle, sub_eq_iff_eq_add] at hz
    exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hz))

open P202Specs.PlanarRegionTopology P202Specs.PlaneTurning
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]
lemma rotation_linear_coordinate_pos_volume (o : Orientation ℝ V (Fin 2))
    (L : V ≃ₗ[ℝ] Plane) {w : V} (hw : w ≠ 0) :
    volume {theta : Circle | 0 < (L (o.rotation (show Real.Angle from theta) w)) 1} =
      ENNReal.ofReal Real.pi := by
  letI : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  let f : Circle → ℝ := fun theta => (L (o.rotation (show Real.Angle from theta) w)) 1
  apply half_volume_of_antipodal f
  · have hr : Continuous (fun theta : Circle => o.rotation (show Real.Angle from theta) w) := by
      simp only [o.rotation_apply]
      exact (Real.Angle.continuous_cos.smul continuous_const).add
        (Real.Angle.continuous_sin.smul continuous_const)
    exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
      (L.toLinearMap.continuous_of_finiteDimensional.comp hr)
  · intro theta
    change (L (o.rotation ((Real.pi : Real.Angle) + (show Real.Angle from theta)) w)) 1 =
      -(L (o.rotation (show Real.Angle from theta) w)) 1
    rw [← o.neg_rotation, map_neg]
    rfl
  · exact (rotation_linear_coordinate_zero_finite o L hw).measure_zero volume

lemma circle_volume_univ : volume (Set.univ : Set Circle) =
    ENNReal.ofReal (2 * Real.pi) := AddCircle.measure_univ _

lemma rotation_coordinate_pos_volume (o : Orientation ℝ V (Fin 2))
    (L : V ≃ₗ[ℝ] SmoothManifolds.ModelData.Euclidean 2) {w : V} (hw : w ≠ 0) :
    volume {theta : Circle | 0 <
      (P202Specs.SurfaceRegionConstruction.toPlane
        (L (o.rotation (show Real.Angle from theta) w))) 1} =
      ENNReal.ofReal Real.pi :=
  rotation_linear_coordinate_pos_volume o
    (L.trans P202Specs.SurfaceRegionConstruction.toPlane.toLinearEquiv) hw

end AngularVolume


lemma not_eventually_region_coordinate_image
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
    (D : RegionDecomposition S) (e : ModelChart 2 .halfSpace M)
    (he : e ∈ S.smoothStructure.val) {p : M} (hp : p ∈ e.source)
    (hpB : p ∈ intrinsicBoundary S) (v : Euclidean 2) (hv : v 1 ≤ 0)
    (r : Fin D.regionCount) :
    ¬∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      (e p).val + s • v ∈ (fun q => (e q).val) '' (regionInterior D r ∩ e.source) := by
  intro h
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨s, hs, q, hq, heq⟩ := (hpos.and h).exists
  have hpb : (e p).val 1 = 0 := by
    exact (SmoothManifolds.intrinsicBoundary_iff_chart S e he p hp).mp hpB
  have hqn : 0 ≤ (e q).val 1 := (e q).property
  have he1 := congrArg (fun z : Euclidean 2 => z 1) heq
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpb, zero_add] at he1
  have hqz : (e q).val 1 = 0 := by
    apply le_antisymm _ hqn
    rw [he1]
    exact mul_nonpos_of_nonneg_of_nonpos hs.le hv
  have hqB : q ∈ intrinsicBoundary S :=
    (SmoothManifolds.intrinsicBoundary_iff_chart S e he q hq.2).mpr hqz
  exact (P202.SurfaceRegionsEuler.componentSet_subset _ hq.1) (D.contains_boundary hqB)


open MeasureTheory
set_option maxHeartbeats 2000000 in
theorem incident_interior_angles_sum_fullStar
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (G : ∀ r, RegionalChartGeometry g D r)
    (A : ∀ r i, ArcPresentation ((D.region r).curve i))
    (s : ∀ r, Fin (D.region r).boundaryCount → ℝ)
    (hs : ∀ r, IsInducedBoundaryOrientation (D.region r) (s r))
    (p : M) (o : Orientation ℝ (TangentSpace S p) (Fin 2))
    (w : TangentSpace S p) (hw : w ≠ 0) (t : GraphStar D.graph p)
    (Q : ConnectedComponents (t.neighborhood \ D.graph.carrier : Set M) ≃
      {r : Fin D.regionCount // p ∈ regionClosure D r})
    (hQ : ∀ a, regionInterior D (Q a).val ∩ t.neighborhood =
      componentSet (t.neighborhood \ D.graph.carrier) a)
    (hfull : ∀ z : Plane, ‖z‖ < t.radius →
      toPlane.symm (coordinates t.chart p + z) ∈ modelSet 2 kind)
    (i : ∀ r : {r : Fin D.regionCount // p ∈ regionClosure D r},
      Fin (D.region r.val).boundaryCount)
    (k : ∀ r : {r : Fin D.regionCount // p ∈ regionClosure D r}, Fin (A r.val (i r)).count)
    (hp : ∀ r, CornerAt D r.val (i r) (A r.val (i r)) (k r) p) :
    (∑ r : {r : Fin D.regionCount // p ∈ regionClosure D r},
      P202Specs.LocalGaussBonnet.interiorAngle
        (G r.val).metric (G r.val).orientation (G r.val).ambientChart
        (G r.val).ambientChart_mem (A r.val (i r)) (s r.val (i r)) (k r)) = 2 * Real.pi := by
  classical
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let I := {r : Fin D.regionCount // p ∈ regionClosure D r}
  let q : ∀ r : I, (G r.val).neighborhood := fun r => ⟨p, (G r.val).closure_subset r.property⟩
  let Ke := (tangentStructure S).fiberCoordinates.equiv t.chart t.chart_mem p t.mem_source
  let L := Ke.trans toPlane.toLinearEquiv
  let Kd := fun r : I => (tangentStructure S).fiberCoordinates.equiv
    (D.chart r.val) (D.chart_mem r.val) p ((G r.val).source_subset (q r).property)
  let Ld := fun r : I => (Kd r).trans toPlane.toLinearEquiv
  let alpha := fun r : I => P202Specs.LocalGaussBonnet.interiorAngle
    (G r.val).metric (G r.val).orientation (G r.val).ambientChart
    (G r.val).ambientChart_mem (A r.val (i r)) (s r.val (i r)) (k r)
  let a : I → AddCircle (2 * Real.pi) := fun r => o.oangle w
    ((Ld r).symm (outgoingRay (A r.val (i r)) (s r.val (i r)) (k r)))
  let b : I → AddCircle (2 * Real.pi) := fun r => o.oangle w
    ((Ld r).symm (incomingRay (A r.val (i r)) (s r.val (i r)) (k r)))
  let P := fun (r : I) (theta : AddCircle (2 * Real.pi)) =>
    ∀ᶠ x : ℝ in 𝓝[>] 0, (t.chart p).val + x • Ke (o.rotation theta w) ∈
      (fun q => (t.chart q).val) '' (regionInterior D r.val ∩ t.chart.source)
  have hgeom (r : I) : ∃ reversed : Bool, 0 < alpha r ∧ alpha r < 2 * Real.pi ∧
      ∀ theta : AddCircle (2 * Real.pi), theta ≠ a r → theta ≠ b r →
        (P r theta ↔ (if reversed then positiveAngle (a r - theta) else positiveAngle (theta - a r)) < alpha r) := by
    have h := listedCorner_angular_germ g D r.val (G r.val) (q r) o w hw
      (A r.val) (s r.val) (hs r.val) (i r) (k r) (hp r).2.symm
      t.chart t.chart_mem t.mem_source
    exact h
  choose reversed halpha halpha' htest using hgeom
  let phase : Fin t.rayCount → AddCircle (2 * Real.pi) := fun j => o.oangle w (L.symm (t.direction j))
  let F : Set (AddCircle (2 * Real.pi)) := range phase ∪ (range a ∪ range b)
  have hF : F.Finite := (finite_range _).union ((finite_range _).union (finite_range _))
  have hna {theta : AddCircle (2 * Real.pi)} (htheta : theta ∉ F) (r : I) : theta ≠ a r := by
    intro he
    exact htheta (Or.inr (Or.inl ⟨r, he.symm⟩))
  have hnb {theta : AddCircle (2 * Real.pi)} (htheta : theta ∉ F) (r : I) : theta ≠ b r := by
    intro he
    exact htheta (Or.inr (Or.inr ⟨r, he.symm⟩))
  have hdis : ∀ theta ∉ F, ∀ r r',
      (if reversed r then positiveAngle (a r - theta) else positiveAngle (theta - a r)) < alpha r →
      (if reversed r' then positiveAngle (a r' - theta) else positiveAngle (theta - a r')) < alpha r' → r = r' := by
    intro theta htheta r r' hr hr'
    apply Subtype.ext
    exact region_chart_ray_germs_unique D t.chart (t.chart p).val (Ke (o.rotation theta w)) r.val r'.val
      ((htest r theta (hna htheta r) (hnb htheta r)).mpr hr)
      ((htest r' theta (hna htheta r') (hnb htheta r')).mpr hr')
  have hcover : ∀ theta ∉ F, theta ∈ (univ : Set (AddCircle (2 * Real.pi))) ↔ ∃ r : I,
      (if reversed r then positiveAngle (a r - theta) else positiveAngle (theta - a r)) < alpha r := by
    intro theta htheta
    constructor
    · intro _
      have hv0 : L (o.rotation theta w) ≠ 0 :=
        L.map_ne_zero_iff.mpr ((o.rotation theta).map_ne_zero_iff.mpr hw)
      have hdir : ∀ j, NormedSpace.normalize (L (o.rotation theta w)) ≠ NormedSpace.normalize (t.direction j) := by
        intro j
        apply AngularPhase.rotation_normalize_exclusion o L hw
          (norm_ne_zero_iff.mp ((t.direction_unit j).trans_ne one_ne_zero)) theta
        intro he
        exact htheta (Or.inl ⟨j, he.symm⟩)
      have hv : L (o.rotation theta w) ∉ closedRays t.direction :=
        CornerTransport.not_mem_closedRays_of_normalize t.direction hv0 hdir
      obtain ⟨epsilon, hepsilon, hvε⟩ := exists_graphStar_short_ray t (L (o.rotation theta w)) hv
        (fun x hx hn => hfull _ hn)
      obtain ⟨r, hr⟩ := graphStar_eventually_unique_incident_region D p t Q hQ
        (Ke (o.rotation theta w)) epsilon hepsilon hvε
      have hPr : P r theta := by
        filter_upwards [hr] with x hx
        exact (hx r).mpr rfl
      exact ⟨r, (htest r theta (hna htheta r) (hnb htheta r)).mp hPr⟩
    · exact fun _ => mem_univ _
  have hsum := AngularMeasure.finite_angular_partition_angle_sum a reversed alpha halpha
    (fun r => (halpha' r).le) F univ hF hdis hcover
  have hvuniv : (volume (univ : Set (AddCircle (2 * Real.pi)))).toReal = 2 * Real.pi := by
    rw [AddCircle.measure_univ, ENNReal.toReal_ofReal (by positivity)]
  exact hsum.trans hvuniv


set_option maxHeartbeats 2000000 in
theorem incident_interior_angles_sum_boundaryStar
    {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (G : ∀ r, RegionalChartGeometry g D r)
    (A : ∀ r i, ArcPresentation ((D.region r).curve i))
    (s : ∀ r, Fin (D.region r).boundaryCount → ℝ)
    (hs : ∀ r, IsInducedBoundaryOrientation (D.region r) (s r))
    (p : M) (o : Orientation ℝ (TangentSpace S p) (Fin 2))
    (w : TangentSpace S p) (hw : w ≠ 0) (t : GraphStar D.graph p)
    (Q : ConnectedComponents (t.neighborhood \ D.graph.carrier : Set M) ≃
      {r : Fin D.regionCount // p ∈ regionClosure D r})
    (hQ : ∀ a, regionInterior D (Q a).val ∩ t.neighborhood =
      componentSet (t.neighborhood \ D.graph.carrier) a)
    (hpB : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (i : ∀ r : {r : Fin D.regionCount // p ∈ regionClosure D r},
      Fin (D.region r.val).boundaryCount)
    (k : ∀ r : {r : Fin D.regionCount // p ∈ regionClosure D r}, Fin (A r.val (i r)).count)
    (hp : ∀ r, CornerAt D r.val (i r) (A r.val (i r)) (k r) p) :
    (∑ r : {r : Fin D.regionCount // p ∈ regionClosure D r},
      P202Specs.LocalGaussBonnet.interiorAngle
        (G r.val).metric (G r.val).orientation (G r.val).ambientChart
        (G r.val).ambientChart_mem (A r.val (i r)) (s r.val (i r)) (k r)) = Real.pi := by
  classical
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let I := {r : Fin D.regionCount // p ∈ regionClosure D r}
  let q : ∀ r : I, (G r.val).neighborhood := fun r => ⟨p, (G r.val).closure_subset r.property⟩
  let Ke := (tangentStructure S).fiberCoordinates.equiv t.chart t.chart_mem p t.mem_source
  let L := Ke.trans toPlane.toLinearEquiv
  let Kd := fun r : I => (tangentStructure S).fiberCoordinates.equiv
    (D.chart r.val) (D.chart_mem r.val) p ((G r.val).source_subset (q r).property)
  let Ld := fun r : I => (Kd r).trans toPlane.toLinearEquiv
  let alpha := fun r : I => P202Specs.LocalGaussBonnet.interiorAngle
    (G r.val).metric (G r.val).orientation (G r.val).ambientChart
    (G r.val).ambientChart_mem (A r.val (i r)) (s r.val (i r)) (k r)
  let a : I → AddCircle (2 * Real.pi) := fun r => o.oangle w
    ((Ld r).symm (outgoingRay (A r.val (i r)) (s r.val (i r)) (k r)))
  let b : I → AddCircle (2 * Real.pi) := fun r => o.oangle w
    ((Ld r).symm (incomingRay (A r.val (i r)) (s r.val (i r)) (k r)))
  let P := fun (r : I) (theta : AddCircle (2 * Real.pi)) =>
    ∀ᶠ x : ℝ in 𝓝[>] 0, (t.chart p).val + x • Ke (o.rotation theta w) ∈
      (fun q => (t.chart q).val) '' (regionInterior D r.val ∩ t.chart.source)
  have hgeom (r : I) : ∃ reversed : Bool, 0 < alpha r ∧ alpha r < 2 * Real.pi ∧
      ∀ theta : AddCircle (2 * Real.pi), theta ≠ a r → theta ≠ b r →
        (P r theta ↔ (if reversed then positiveAngle (a r - theta) else positiveAngle (theta - a r)) < alpha r) := by
    have h := listedCorner_angular_germ g D r.val (G r.val) (q r) o w hw
      (A r.val) (s r.val) (hs r.val) (i r) (k r) (hp r).2.symm
      t.chart t.chart_mem t.mem_source
    exact h
  choose reversed halpha halpha' htest using hgeom
  let phase : Fin t.rayCount → AddCircle (2 * Real.pi) := fun j => o.oangle w (L.symm (t.direction j))
  let F : Set (AddCircle (2 * Real.pi)) := range phase ∪ (range a ∪ range b)
  have hF : F.Finite := (finite_range _).union ((finite_range _).union (finite_range _))
  have hna {theta : AddCircle (2 * Real.pi)} (htheta : theta ∉ F) (r : I) : theta ≠ a r := by
    intro he
    exact htheta (Or.inr (Or.inl ⟨r, he.symm⟩))
  have hnb {theta : AddCircle (2 * Real.pi)} (htheta : theta ∉ F) (r : I) : theta ≠ b r := by
    intro he
    exact htheta (Or.inr (Or.inr ⟨r, he.symm⟩))
  have hdis : ∀ theta ∉ F, ∀ r r',
      (if reversed r then positiveAngle (a r - theta) else positiveAngle (theta - a r)) < alpha r →
      (if reversed r' then positiveAngle (a r' - theta) else positiveAngle (theta - a r')) < alpha r' → r = r' := by
    intro theta htheta r r' hr hr'
    apply Subtype.ext
    exact region_chart_ray_germs_unique D t.chart (t.chart p).val (Ke (o.rotation theta w)) r.val r'.val
      ((htest r theta (hna htheta r) (hnb htheta r)).mpr hr)
      ((htest r' theta (hna htheta r') (hnb htheta r')).mpr hr')
  let C : Set (AddCircle (2 * Real.pi)) := {theta | 0 < (L (o.rotation theta w)) 1}
  have hcover : ∀ theta ∉ F, theta ∈ C ↔ ∃ r : I,
      (if reversed r then positiveAngle (a r - theta) else positiveAngle (theta - a r)) < alpha r := by
    intro theta htheta
    constructor
    · intro hpos
      have hv0 : L (o.rotation theta w) ≠ 0 :=
        L.map_ne_zero_iff.mpr ((o.rotation theta).map_ne_zero_iff.mpr hw)
      have hdir : ∀ j, NormedSpace.normalize (L (o.rotation theta w)) ≠ NormedSpace.normalize (t.direction j) := by
        intro j
        apply AngularPhase.rotation_normalize_exclusion o L hw
          (norm_ne_zero_iff.mp ((t.direction_unit j).trans_ne one_ne_zero)) theta
        intro he
        exact htheta (Or.inl ⟨j, he.symm⟩)
      have hv : L (o.rotation theta w) ∉ closedRays t.direction :=
        CornerTransport.not_mem_closedRays_of_normalize t.direction hv0 hdir
      obtain ⟨epsilon, hepsilon, hvε⟩ := exists_graphStar_short_ray t (L (o.rotation theta w)) hv
        (by
          intro x hx hn
          have hp0 : coordinates t.chart p 1 = 0 :=
            (SmoothManifolds.intrinsicBoundary_iff_chart S t.chart t.chart_mem p t.mem_source).mp hpB
          change 0 ≤ (toPlane.symm (coordinates t.chart p + x • L (o.rotation theta w))) 1
          simpa [toPlane, hp0] using mul_nonneg hx.le hpos.le)
      obtain ⟨r, hr⟩ := graphStar_eventually_unique_incident_region D p t Q hQ
        (Ke (o.rotation theta w)) epsilon hepsilon hvε
      have hPr : P r theta := by
        filter_upwards [hr] with x hx
        exact (hx r).mpr rfl
      exact ⟨r, (htest r theta (hna htheta r) (hnb htheta r)).mp hPr⟩
    · rintro ⟨r, hr⟩
      by_contra hpos
      have hPr : P r theta := (htest r theta (hna htheta r) (hnb htheta r)).mpr hr
      have hvnon : (Ke (o.rotation theta w)) 1 ≤ 0 := by
        simpa [C, L, toPlane] using (not_lt.mp hpos)
      exact not_eventually_region_coordinate_image D t.chart t.chart_mem
        t.mem_source hpB (Ke (o.rotation theta w)) hvnon r.val hPr
  have hsum := AngularMeasure.finite_angular_partition_angle_sum a reversed alpha halpha
    (fun r => (halpha' r).le) F C hF hdis hcover
  have hvol : (volume C).toReal = Real.pi := by
    rw [AngularVolume.rotation_linear_coordinate_pos_volume o L hw, ENNReal.toReal_ofReal Real.pi_pos.le]
  exact hsum.trans hvol



open SmoothManifolds.TangentBundleData
lemma sameRay_of_common_line_of_noncuspidal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v d : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (huL : ∃ a : ℝ, u = a • d) (hvL : ∃ b : ℝ, v = b • d)
    (hn : NormedSpace.normalize u ≠ -NormedSpace.normalize v) :
    SameRay ℝ u v := by
  obtain ⟨a,rfl⟩ := huL
  obtain ⟨b,rfl⟩ := hvL
  have ha : a ≠ 0 := by rintro rfl; simp at hu
  have hb : b ≠ 0 := by rintro rfl; simp at hv
  by_cases hab : 0 ≤ a*b
  · exact sameRay_smul_smul_of_mul_nonneg hab
  · exfalso
    have hr : SameRay ℝ (a • d) (-(b • d)) := by
      rw [← neg_smul]
      exact sameRay_smul_smul_of_mul_nonneg (by nlinarith)
    have hh := (sameRay_iff_inv_norm_smul_eq_of_ne hu (neg_ne_zero.mpr hv)).mp hr
    apply hn
    change NormedSpace.normalize (a • d) = NormedSpace.normalize (-(b • d)) at hh
    simpa only [NormedSpace.normalize_neg] using hh

lemma deriv_mem_of_eventually_sub_mem_closed_submodule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {v : E} (hF : HasDerivAt F v 0)
    (L : Submodule ℝ E) (hclosed : IsClosed (L : Set E))
    (he : ∀ᶠ t : ℝ in 𝓝[>] 0, F t - F 0 ∈ L) : v ∈ L := by
  apply hclosed.mem_of_tendsto hF.tendsto_slope_zero_right
  filter_upwards [he] with t ht
  change t⁻¹ • (F (0+t) - F 0) ∈ L
  simpa only [zero_add] using L.smul_mem t⁻¹ ht

/-- Derivatives of actual regional boundary tails, transferred through the
actual atlas germ, lie in every closed subspace containing the star rays.
No explicit inverse-chart lift of the tail is assumed. -/
lemma regional_boundary_derivatives_mem_star_line
    (D : RegionDecomposition S) (r : Fin D.regionCount) (p : M)
    (hp : p ∈ regionClosure D r) (g : GraphStar D.graph p)
    (P : Submodule ℝ Plane) (hP : IsClosed (P : Set Plane))
    (hdir : ∀ k : Fin g.rayCount, g.direction k ∈ P) :
    ∃ T : Plane ≃L[ℝ] Plane,
      ∀ {f : ℝ → Plane} {v : Plane}, HasDerivAt f v 0 →
        f 0 = coordinates (D.chart r) p →
        (∀ᶠ t : ℝ in 𝓝[>] 0, f t ∈ (D.region r).boundary) → T v ∈ P := by
  let e := D.chart r
  have hpe : p ∈ e.source := D.closure_in_chart r hp
  let K := (P202.MetricData.tangentStructure S).fiberCoordinates
  let L := ((K.equiv e (D.chart_mem r) p hpe).symm.trans
    (K.equiv g.chart g.chart_mem p g.mem_source)).toContinuousLinearEquiv
  obtain ⟨H,hHs,hHbase,hHsm,hHinv,hHd,hHid,hrep,hrepi⟩ :=
    CornerTransport.exists_atlas_transition_localDiffeomorph S K e g.chart
      (D.chart_mem r) g.chart_mem p hpe g.mem_source
  let T : Plane ≃L[ℝ] Plane := (toPlane.symm.trans L).trans toPlane
  let Q : Plane → Plane := fun z => toPlane (H (toPlane.symm z))
  have hQbase : Q (coordinates e p) = coordinates g.chart p := by
    simpa only [Q,coordinates,toPlane.symm_apply_apply] using congrArg toPlane hHbase
  have hW : ∀ᶠ q in 𝓝 p, q ∈ g.neighborhood ∧ q ∈ e.source ∧
      H (e q).val = (g.chart q).val := by
    filter_upwards [(GraphStar.isOpen_neighborhood g).mem_nhds
      (GraphStar.mem_neighborhood g), e.open_source.mem_nhds hpe, hrep] with q hqN hqe hqrep
    exact ⟨hqN,hqe,hqrep⟩
  obtain ⟨W,hWsub,hWopen,hpW⟩ := mem_nhds_iff.mp hW
  let B : Set M := regionClosure D r ∩ D.graph.carrier
  have hBsource : B ⊆ e.source := fun q hq => D.closure_in_chart r hq.1
  have hcut := CornerTransport.coordinateImage_inter_nhds e p hpe W hWopen hpW B hBsource
  refine ⟨T,?_⟩
  intro f v hf hf0 hfb
  have hraw0 : toPlane.symm (f 0) = (e p).val := by
    rw [hf0]
    simp only [e,coordinates,toPlane.symm_apply_apply]
  have hraw : HasDerivAt (fun t => toPlane.symm (f t)) (toPlane.symm v) 0 :=
    toPlane.symm.hasFDerivAt.comp_hasDerivAt 0 hf
  have hrawTend : Tendsto (fun t => toPlane.symm (f t)) (𝓝[>] 0) (𝓝 (e p).val) := by
    simpa only [hraw0] using hraw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcutf := hrawTend.eventually hcut
  have hQd : HasDerivAt (fun t => Q (f t)) (T v) 0 := by
    have hHd' : HasFDerivAt H (L : Euclidean 2 →L[ℝ] Euclidean 2)
        (toPlane.symm (f 0)) := by simpa only [hraw0] using hHd
    have hh := toPlane.hasFDerivAt.comp_hasDerivAt 0
      (hHd'.comp_hasDerivAt 0 hraw)
    simpa only [Q,T,ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.coe_coe,Function.comp_def] using hh
  apply deriv_mem_of_eventually_sub_mem_closed_submodule hQd P hP
  filter_upwards [hcutf,hfb] with t htcut htb
  have htB : toPlane.symm (f t) ∈ (fun q => (e q).val) '' B := by
    rw [region_boundary_eq_coordinates_graph D r] at htb
    obtain ⟨q,hq,hqf⟩ := htb
    refine ⟨q,hq,?_⟩
    apply toPlane.injective
    simpa only [e,coordinates,toPlane.apply_symm_apply] using hqf
  obtain ⟨q,⟨hqB,hqW⟩,hqf⟩ := htcut.mp htB
  have hqN : q ∈ g.neighborhood := (hWsub hqW).1
  have hQf : Q (f t) = coordinates g.chart q := by
    dsimp [Q]
    rw [← hqf,(hWsub hqW).2.2]
    rfl
  rw [hQf,hf0,hQbase]
  obtain rfl | ⟨k,a,ha,har,hqa⟩ := (g.graph_eq q hqN.1 hqN.2).mp hqB.2
  · simpa only [sub_self] using P.zero_mem
  · rw [hqa,add_sub_cancel_left]
    exact P.smul_mem a (hdir k)

lemma arcPresentation_mem_region_boundary (R : PlanarRegion)
    (i : Fin R.boundaryCount) (A : ArcPresentation (R.curve i))
    (k : Fin A.count) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    A.arc k t ∈ R.boundary := by
  rw [A.agrees k t ht]
  change realLift (R.curve i).parametrization _ ∈ frontier R.domain
  rw [R.boundary_eq]
  exact mem_iUnion.mpr ⟨i,_,rfl⟩

/-- The actual directed presentation velocities at every nonvertex join
are on the same ray; speed jumps are allowed. -/
lemma presentation_velocities_sameRay_off_vertices
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (k : Fin A.count) (p : M)
    (hp : CornerAt D r i A k p) (hpv : p ∉ range D.graph.vertex) :
    SameRay ℝ (velocity A k 1) (velocity A (finRotate A.count k) 0) := by
  obtain ⟨p',hp',hps,hpc⟩ := region_corner_on_graph D r i A k
  have hpp : p' = p := coordinates_injOn (D.chart r) hps hp.1
    (hpc.trans hp.2.symm)
  subst p'
  obtain ⟨e,t,ht0,ht1,het⟩ := exists_open_edge_of_mem_carrier D.graph hp'.2 hpv
  obtain ⟨g,_,_⟩ := D.sectors p hp'.2 univ isOpen_univ (mem_univ p)
  let gt : GraphStar D.graph (D.graph.edge e t) := het.symm ▸ g
  obtain ⟨d,hd,hdirs⟩ := graphStar_directions_in_line_of_open_edge D.graph e t ⟨ht0,ht1⟩ gt
  have hdirs' : ∀ j : Fin g.rayCount, ∃ a : ℝ, g.direction j = a • d := by
    cases het
    simpa only [gt] using hdirs
  let P : Submodule ℝ Plane := Submodule.span ℝ {d}
  have hP : IsClosed (P : Set Plane) := P.closed_of_finiteDimensional
  have hdirP : ∀ j : Fin g.rayCount, g.direction j ∈ P := by
    intro j
    obtain ⟨a,ha⟩ := hdirs' j
    rw [ha]
    exact P.smul_mem a (Submodule.subset_span (by simp))
  obtain ⟨T,hT⟩ := regional_boundary_derivatives_mem_star_line D r p hp'.1 g P hP hdirP
  have hin : HasDerivAt (fun t => A.arc k (1-t)) (-velocity A k 1) 0 := by
    have hd : HasDerivAt (A.arc k) (velocity A k 1) ((1 : ℝ)-0) := by
      simpa only [velocity,sub_zero] using
        (differentiableAt_of_deriv_ne_zero (A.regular k 1 (by simp))).hasDerivAt
    simpa only [Function.comp_def,zero_sub,one_smul,neg_one_smul] using
      hd.scomp 0 ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ)))
  have hinB : ∀ᶠ t : ℝ in 𝓝[>] 0, A.arc k (1-t) ∈ (D.region r).boundary := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))] with t ht0 ht1
    exact arcPresentation_mem_region_boundary (D.region r) i A k (1-t)
      ⟨by have := (show t < 1 from ht1); linarith,
        by have := (show 0 < t from ht0); linarith⟩
  have hTin : T (-velocity A k 1) ∈ P := hT hin (by simpa only [sub_zero] using hp.2.symm) hinB
  have hout : HasDerivAt (A.arc (finRotate A.count k))
      (velocity A (finRotate A.count k) 0) 0 :=
    (differentiableAt_of_deriv_ne_zero (A.regular (finRotate A.count k) 0 (by simp))).hasDerivAt
  have hout0 : A.arc (finRotate A.count k) 0 = coordinates (D.chart r) p :=
    (P202.MetricBoundaryTurning.FrameAngleCoordinates.arc_join A k).symm.trans hp.2.symm
  have houtB : ∀ᶠ t : ℝ in 𝓝[>] 0,
      A.arc (finRotate A.count k) t ∈ (D.region r).boundary := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))] with t ht0 ht1
    exact arcPresentation_mem_region_boundary (D.region r) i A (finRotate A.count k) t
      ⟨le_of_lt ht0,le_of_lt ht1⟩
  have hTout : T (velocity A (finRotate A.count k) 0) ∈ P := hT hout hout0 houtB
  have hTu : T (velocity A k 1) ∈ P := by
    simpa only [map_neg,neg_neg] using P.neg_mem hTin
  have hU : ∃ a : ℝ, velocity A k 1 = a • T.symm d := by
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hTu
    refine ⟨a,?_⟩
    simpa only [map_smul,ContinuousLinearEquiv.symm_apply_apply] using
      (congrArg (fun z : Plane => T.symm z) ha).symm
  have hV : ∃ a : ℝ, velocity A (finRotate A.count k) 0 = a • T.symm d := by
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hTout
    refine ⟨a,?_⟩
    simpa only [map_smul,ContinuousLinearEquiv.symm_apply_apply] using
      (congrArg (fun z : Plane => T.symm z) ha).symm
  exact sameRay_of_common_line_of_noncuspidal
    (A.regular k 1 (by simp)) (A.regular (finRotate A.count k) 0 (by simp))
    hU hV (A.noncuspidal k)

theorem offVertexContribution_zero :
    P202Specs.RegionalVertexCorners.Expected.offVertexContribution_zero.{u} := by
  intro kind M _ _ S g D G A s hs r i k p hp hpv
  have hray := presentation_velocities_sameRay_off_vertices D r i (A r i) k p hp hpv
  have hzero := P202.GlobalGaussBonnet.metricCornerAngle_eq_zero_of_sameRay
    (G r).metric (G r).orientation (G r).ambientChart (G r).ambientChart_mem (A r i) k hray
  simp only [cornerTerm,P202Specs.LocalGaussBonnet.interiorAngle,hzero,mul_zero,
    sub_zero,sub_self]




/-- The complete local exterior-angle identity, for every actual regional
presentation. Comparison presentations supply any omitted smooth vertex joins. -/
theorem vertexCornerIdentity :
    P202Specs.RegionalVertexCorners.Expected.vertexCornerIdentity.{u} := by
  intro kind M _ _ S g D G A s hs v
  classical
  let p : M := D.graph.vertex v
  have hpG : p ∈ D.graph.carrier := Or.inl ⟨v, rfl⟩
  obtain ⟨B, hB⟩ := exists_presentations_listing_incident_point D A p hpG
  choose i k hk using
    (fun r : {r : Fin D.regionCount // p ∈ regionClosure D r} => hB r.val r.property)
  let o : Orientation ℝ (TangentSpace S p) (Fin 2) :=
    (P202.SurfaceBoundaryData.referenceBasis g p).orientation (R := ℝ) (M := TangentSpace S p)
  let w : TangentSpace S p := P202.SurfaceBoundaryData.referenceBasis g p 0
  have hw : w ≠ 0 := (P202.SurfaceBoundaryData.referenceBasis g p).ne_zero 0
  change cornerSumAt g D G A s p = Real.pi * ((vertexDegree D.graph v : ℝ) - 2)
  rw [cornerSumAt_eq_of_presentations g D G A B s p,
    cornerSumAt_eq_incident_angle_sum g D G B s p i k hk]
  by_cases hpB : p ∈ intrinsicBoundary S
  · cases kind with
    | euclidean =>
      exact False.elim (by
        simpa only [SmoothManifolds.intrinsicBoundary_euclidean, mem_empty_iff_false] using hpB)
    | halfSpace =>
      obtain ⟨t, _, Q, hQ⟩ := exists_incident_region_sector_equiv D p hpG
        univ isOpen_univ (mem_univ p)
      have hangle := incident_interior_angles_sum_boundaryStar
        g D G B s hs p o w hw t Q hQ hpB i k hk
      have hcard : Nat.card {r : Fin D.regionCount // p ∈ regionClosure D r} =
          vertexDegree D.graph v - 1 := boundary_incident_region_card D v hpB
      rw [hangle, hcard]
      have hv1 : 1 ≤ vertexDegree D.graph v := le_trans (by norm_num) (two_le_vertexDegree D v)
      rw [Nat.cast_sub hv1]
      push_cast
      ring
  · obtain ⟨t, ht, Q, hQ⟩ := exists_incident_region_sector_equiv D p hpG
      (intrinsicBoundary S)ᶜ (SmoothManifolds.isClosed_intrinsicBoundary S).isOpen_compl hpB
    have hfull := graphStar_full_model_of_interior_neighborhood t ht
    have hangle := incident_interior_angles_sum_fullStar
      g D G B s hs p o w hw t Q hQ hfull i k hk
    have hcard : Nat.card {r : Fin D.regionCount // p ∈ regionClosure D r} =
        vertexDegree D.graph v := interior_incident_region_card D v hpB
    rw [hangle, hcard]
    ring

end P202.GlobalGaussBonnet.VertexCorners
