import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RegionalBoundaryRefinement
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GlobalGaussBonnetLocalization
import Mathlib.Tactic.Module
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Algebra.GroupWithZero

/-! Genuine original regional arcs and their finite geometric common refinement.
All incidence, multiplicity, occupied germs and closed transitions are derived
from the given decomposition and literal presentations. The parent handoff
is proof data only, never an import. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology
open scoped Classical BigOperators ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
open P202Specs.SurfaceRegionConstruction P202.SurfaceRegionConstruction
open P202Specs.PlanarRegionTopology
open P202.GlobalGaussBonnet
open P202.MetricData P202.SurfaceBoundaryData P202Specs.RegionalBoundaryRefinement
namespace P202.GlobalGaussBonnet.BoundaryGluing
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

lemma arcPresentation_affine_mem_Ioo {q : RegularJordanCurve}
    (A : P202Specs.PlaneTurning.ArcPresentation q) (k : Fin A.count)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * t ∈ Ioo (0 : ℝ) 1 := by
  have ha : 0 ≤ A.time k.castSucc := by
    rw [← A.first]
    exact A.strictMono.monotone (Fin.zero_le _)
  have hb : A.time k.succ ≤ 1 := by
    rw [← A.last]
    exact A.strictMono.monotone (Fin.le_last _)
  have hd : 0 < A.time k.succ - A.time k.castSucc :=
    sub_pos.mpr (A.strictMono k.castSucc_lt_succ)
  constructor <;> nlinarith [mul_pos hd ht.1, mul_pos hd (sub_pos.mpr ht.2)]

/-- Open arcs in every genuine regional presentation are embedded, including
when the two endpoints are the same point of the parameter circle. -/
lemma arcPresentation_open_injective {q : RegularJordanCurve}
    (A : P202Specs.PlaneTurning.ArcPresentation q) (k : Fin A.count) :
    InjOn (A.arc k) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hparam : ((A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * x : ℝ) :
      ParameterCircle) =
      ((A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * y : ℝ) : ParameterCircle) := by
    apply q.injective
    change realLift q.parametrization _ = realLift q.parametrization _
    rw [← A.agrees k x ⟨hx.1.le, hx.2.le⟩, ← A.agrees k y ⟨hy.1.le, hy.2.le⟩]
    exact hxy
  have hx' := arcPresentation_affine_mem_Ioo A k hx
  have hy' := arcPresentation_affine_mem_Ioo A k hy
  have he : A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * x =
      A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * y :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      ⟨hx'.1.le, by simpa only [zero_add] using hx'.2⟩
      ⟨hy'.1.le, by simpa only [zero_add] using hy'.2⟩).mp hparam
  have hd : 0 < A.time k.succ - A.time k.castSucc :=
    sub_pos.mpr (A.strictMono k.castSucc_lt_succ)
  nlinarith

lemma arcPresentation_cutParameters_finite {q : RegularJordanCurve}
    (A : P202Specs.PlaneTurning.ArcPresentation q) (k : Fin A.count)
    {F : Set Plane} (hF : F.Finite) :
    (Ioo (0 : ℝ) 1 ∩ A.arc k ⁻¹' F).Finite := by
  exact Set.Finite.of_injOn (t := F) (fun t ht => ht.2)
    ((arcPresentation_open_injective A k).mono inter_subset_left) hF
/-- Every point of every actual regional boundary arc is on the original
graph, in the original assigned coordinates. This includes inserted smooth
subdivision endpoints and both original model kinds. -/
theorem region_arc_on_graph (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ p ∈ P202Specs.SurfaceRegionsEuler.regionClosure D j ∩ D.graph.carrier,
      p ∈ (D.chart j).source ∧ coordinates (D.chart j) p = A.arc k t := by
  have hx : A.arc k t ∈ (D.region j).boundary := by
    change A.arc k t ∈ frontier (D.region j).domain
    rw [(D.region j).boundary_eq]
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    refine ⟨((A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * t : ℝ) :
      ParameterCircle), ?_⟩
    exact (A.agrees k t ht).symm
  rw [region_boundary_eq_coordinates_graph D j] at hx
  obtain ⟨p, hp, he⟩ := hx
  exact ⟨p, hp, D.closure_in_chart j hp.1, he⟩

/-- Cutting a genuine presentation arc at all original graph vertices adds
only finitely many parameter values. No endpoint regularity of the supplied
graph parametrizations is needed. -/
theorem region_arc_vertex_cutParameters_finite (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) :
    (Ioo (0 : ℝ) 1 ∩ A.arc k ⁻¹' (coordinates (D.chart j) '' range D.graph.vertex)).Finite := by
  exact arcPresentation_cutParameters_finite A k ((Set.finite_range _).image _)

/-- Removing the actual vertices turns a full edge into its embedded open
edge. Loops are allowed, so the two endpoint vertices need not be distinct. -/
lemma mem_openEdge_of_mem_edge_not_vertex (G : EmbeddedGraph S) (i : Fin G.edgeCount)
    {p : M} (hp : p ∈ range (G.edge i)) (hne : p ∉ range G.vertex) :
    p ∈ G.edge i '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
  obtain ⟨t, rfl⟩ := hp
  have hzero : t ≠ 0 := by
    intro he
    apply hne
    exact ⟨G.initial i, (G.at_zero i).symm.trans (congrArg (G.edge i) he.symm)⟩
  have hone : t ≠ 1 := by
    intro he
    apply hne
    exact ⟨G.terminal i, (G.at_one i).symm.trans (congrArg (G.edge i) he.symm)⟩
  refine ⟨t, ⟨?_, ?_⟩, rfl⟩
  · exact lt_of_le_of_ne t.property.1 (fun h => hzero (Subtype.ext h.symm))
  · exact lt_of_le_of_ne t.property.2 (fun h => hone (Subtype.ext h))

lemma fullEdge_index_unique_off_vertices (G : EmbeddedGraph S) {p : M}
    (hne : p ∉ range G.vertex) (i j : Fin G.edgeCount)
    (hi : p ∈ range (G.edge i)) (hj : p ∈ range (G.edge j)) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (G.disjoint_open_edges hij)
    (mem_openEdge_of_mem_edge_not_vertex G i hi hne)
    (mem_openEdge_of_mem_edge_not_vertex G j hj hne)

/-- Every connected piece of the actual graph avoiding its vertices lies in
one actual open edge. This localizes a refined regional arc without making
any regularity assumption on the graph's endpoint parameters. -/
theorem connected_graph_subset_one_openEdge (G : EmbeddedGraph S) {A : Set M}
    (hA : IsConnected A) (hgraph : A ⊆ G.carrier)
    (hne : Disjoint A (range G.vertex)) :
    ∃ i : Fin G.edgeCount,
      A ⊆ G.edge i '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
  letI : T2Space M := S.topologicalManifold.hausdorff
  have hfull : ∃ i : Fin G.edgeCount, A ⊆ range (G.edge i) := by
    apply connected_subset_one_finite_closed_cover hA (fun i => range (G.edge i))
    · intro i
      exact (isCompact_range (G.edge i).continuous).isClosed
    · intro p hp
      rcases hgraph hp with hv | he
      · exact (Set.disjoint_left.mp hne hp hv).elim
      · exact he
    · intro p hp i j hi hj
      exact fullEdge_index_unique_off_vertices G
        (fun hv => Set.disjoint_left.mp hne hp hv) i j hi hj
  obtain ⟨i, hi⟩ := hfull
  exact ⟨i, fun p hp => mem_openEdge_of_mem_edge_not_vertex G i (hi hp)
    (fun hv => Set.disjoint_left.mp hne hp hv)⟩

/-- The open pieces of one original finite regional presentation are
pairwise disjoint; arbitrary inserted smooth subdivision endpoints are allowed. -/
lemma arcPresentation_open_images_disjoint {q : RegularJordanCurve}
    (A : P202Specs.PlaneTurning.ArcPresentation q) : Pairwise (fun k z : Fin A.count =>
      Disjoint (A.arc k '' Ioo (0 : ℝ) 1) (A.arc z '' Ioo (0 : ℝ) 1)) := by
  intro k z hkz
  apply Set.disjoint_left.mpr
  rintro p ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
  have hparam : ((A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * x : ℝ) :
      ParameterCircle) =
      ((A.time z.castSucc + (A.time z.succ - A.time z.castSucc) * y : ℝ) : ParameterCircle) := by
    apply q.injective
    change realLift q.parametrization _ = realLift q.parametrization _
    rw [← A.agrees k x (Ioo_subset_Icc_self hx),
      ← A.agrees z y (Ioo_subset_Icc_self hy)]
    exact he.symm
  have hx' := arcPresentation_affine_mem_Ioo A k hx
  have hy' := arcPresentation_affine_mem_Ioo A z hy
  have heq : A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * x =
      A.time z.castSucc + (A.time z.succ - A.time z.castSucc) * y :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      ⟨hx'.1.le, by simpa only [zero_add] using hx'.2⟩
      ⟨hy'.1.le, by simpa only [zero_add] using hy'.2⟩).mp hparam
  have horder : ∀ (k z : Fin A.count) (x y : ℝ),
      k < z → x ∈ Ioo (0 : ℝ) 1 → y ∈ Ioo (0 : ℝ) 1 →
      A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * x <
        A.time z.castSucc + (A.time z.succ - A.time z.castSucc) * y := by
    intro k z x y hkz hx hy
    have hk : 0 < A.time k.succ - A.time k.castSucc :=
      sub_pos.mpr (A.strictMono k.castSucc_lt_succ)
    have hz : 0 < A.time z.succ - A.time z.castSucc :=
      sub_pos.mpr (A.strictMono z.castSucc_lt_succ)
    have hle : A.time k.succ ≤ A.time z.castSucc :=
      A.strictMono.monotone (by
        change k.val + 1 ≤ z.val
        exact Nat.succ_le_of_lt hkz)
    nlinarith [mul_pos hk (sub_pos.mpr hx.2), mul_pos hz hy.1]
  rcases lt_or_gt_of_ne hkz with hkz | hzk
  · exact heq.not_lt (horder k z x y hkz hx hy)
  · exact heq.symm.not_lt (horder z k y x hzk hy hx)

/-- The actual surface point of a genuine regional presentation arc. The
original chart determines it uniquely, even in the half-space model. -/
def regionalArcLift (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (t : unitInterval) : M :=
  (region_arc_on_graph D j i A k t t.property).choose

lemma regionalArcLift_spec (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (t : unitInterval) :
    regionalArcLift D j i A k t ∈ P202Specs.SurfaceRegionsEuler.regionClosure D j ∩
      D.graph.carrier ∧
    regionalArcLift D j i A k t ∈ (D.chart j).source ∧
    coordinates (D.chart j) (regionalArcLift D j i A k t) = A.arc k t :=
  (region_arc_on_graph D j i A k t t.property).choose_spec

lemma regionalArcLift_continuous (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) : Continuous (regionalArcLift D j i A k) := by
  obtain ⟨δ, hδ, hs⟩ := A.smooth k
  have hA : Continuous (fun t : unitInterval => A.arc k t) :=
    hs.continuousOn.comp_continuous continuous_subtype_val (by
      intro t
      constructor <;> linarith [t.property.1, t.property.2])
  have hm : Continuous (fun t : unitInterval => (D.chart j) (regionalArcLift D j i A k t)) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun t : unitInterval => ((D.chart j) (regionalArcLift D j i A k t)).val)
    convert toPlane.symm.continuous.comp hA using 1
    funext t
    simpa only [coordinates, ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply] using
      congrArg toPlane.symm (regionalArcLift_spec D j i A k t).2.2
  have h := (D.chart j).continuousOn_symm.comp_continuous hm
    (fun t => (D.chart j).map_source (regionalArcLift_spec D j i A k t).2.1)
  convert h using 1
  funext t
  exact ((D.chart j).left_inv (regionalArcLift_spec D j i A k t).2.1).symm

/-- A harmless constant extension gives a real parameter curve, with the
original point and coordinates throughout the full unit interval. -/
def regionalArcCurve (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) : ℝ → M :=
  IccExtend zero_le_one (regionalArcLift D j i A k)

lemma regionalArcCurve_continuous (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) : Continuous (regionalArcCurve D j i A k) :=
  continuous_IccExtend_iff.mpr (regionalArcLift_continuous D j i A k)

lemma regionalArcCurve_spec (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    regionalArcCurve D j i A k t ∈ P202Specs.SurfaceRegionsEuler.regionClosure D j ∩
      D.graph.carrier ∧
    regionalArcCurve D j i A k t ∈ (D.chart j).source ∧
    coordinates (D.chart j) (regionalArcCurve D j i A k t) = A.arc k t := by
  rw [regionalArcCurve, IccExtend_of_mem zero_le_one _ ht]
  exact regionalArcLift_spec D j i A k ⟨t, ht⟩

lemma regionalArcCurve_open_injective (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) : InjOn (regionalArcCurve D j i A k) (Ioo (0 : ℝ) 1) := by
  intro s hs t ht he
  apply arcPresentation_open_injective A k hs ht
  rw [← (regionalArcCurve_spec D j i A k (Ioo_subset_Icc_self hs)).2.2,
    ← (regionalArcCurve_spec D j i A k (Ioo_subset_Icc_self ht)).2.2, he]

/-- The full family of original open regional presentation arcs is a
multiplicity-one family in the actual surface, including all boundary curves. -/
lemma regionalArcCurve_images_disjoint (D : RegionDecomposition S)
    (j : Fin D.regionCount)
    (A : ∀ i : Fin (D.region j).boundaryCount,
      P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i)) :
    Pairwise (fun k z : Σ i : Fin (D.region j).boundaryCount, Fin (A i).count =>
      Disjoint (regionalArcCurve D j k.1 (A k.1) k.2 '' Ioo (0 : ℝ) 1)
        (regionalArcCurve D j z.1 (A z.1) z.2 '' Ioo (0 : ℝ) 1)) := by
  intro ⟨i, k⟩ ⟨h, z⟩ hne
  apply Set.disjoint_left.mpr
  rintro p ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
  have hcoord : (A i).arc k s = (A h).arc z t := by
    rw [← (regionalArcCurve_spec D j i (A i) k (Ioo_subset_Icc_self hs)).2.2,
      ← (regionalArcCurve_spec D j h (A h) z (Ioo_subset_Icc_self ht)).2.2, he]
  by_cases hih : i = h
  · subst h
    have hkz : k ≠ z := fun hkz => hne (by cases hkz; rfl)
    exact Set.disjoint_left.mp (arcPresentation_open_images_disjoint (A i) hkz)
      ⟨s, hs, rfl⟩ ⟨t, ht, hcoord.symm⟩
  · have htrace : ∀ (i : Fin (D.region j).boundaryCount) (k : Fin (A i).count)
        (s : ℝ), s ∈ Ioo (0 : ℝ) 1 → (A i).arc k s ∈ ((D.region j).curve i).trace := by
      intro i k s hs
      rw [(A i).agrees k s (Ioo_subset_Icc_self hs)]
      exact ⟨_, rfl⟩
    exact Set.disjoint_left.mp ((D.region j).disjoint_curves hih)
      (htrace i k s hs) (hcoord.symm ▸ htrace h z t ht)

/-- Every finite set of actual surface points gives only finitely many
interior cut parameters on a genuine regional arc. In particular, all
presentation endpoint sets can be added to the graph-vertex refinement. -/
lemma regionalArcCurve_cutParameters_finite (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) {F : Set M} (hF : F.Finite) :
    (Ioo (0 : ℝ) 1 ∩ regionalArcCurve D j i A k ⁻¹' F).Finite := by
  exact Set.Finite.of_injOn (t := F) (fun t ht => ht.2)
    ((regionalArcCurve_open_injective D j i A k).mono inter_subset_left) hF

/-- Every nontrivial cut-free regional subarc belongs to a single actual open
graph edge. This uses only the genuine arc, graph and assigned chart. -/
theorem regional_subarc_subset_one_openEdge (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (l r : ℝ) (hlr : l < r)
    (hsub : Ioo l r ⊆ Ioo (0 : ℝ) 1)
    (hcuts : Disjoint (Ioo l r)
      (A.arc k ⁻¹' (coordinates (D.chart j) '' range D.graph.vertex))) :
    ∃ e : Fin D.graph.edgeCount, regionalArcCurve D j i A k '' Ioo l r ⊆
      D.graph.edge e '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
  apply connected_graph_subset_one_openEdge D.graph
  · exact (isConnected_Ioo hlr).image _ (regionalArcCurve_continuous D j i A k).continuousOn
  · rintro p ⟨t, ht, rfl⟩
    exact (regionalArcCurve_spec D j i A k (Ioo_subset_Icc_self (hsub ht))).1.2
  · apply Set.disjoint_left.mpr
    rintro p ⟨t, ht, rfl⟩ hp
    apply Set.disjoint_left.mp hcuts ht
    change A.arc k t ∈ coordinates (D.chart j) '' range D.graph.vertex
    rw [← (regionalArcCurve_spec D j i A k (Ioo_subset_Icc_self (hsub ht))).2.2]
    exact ⟨_, hp, rfl⟩

def regionalArcMap (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) : C(unitInterval, M) :=
  ⟨regionalArcLift D j i A k, regionalArcLift_continuous D j i A k⟩

/-- Every genuine regional presentation gives regular smooth coordinate
germs in every original chart, including arbitrary subdivision endpoints.
No regularity of the graph's own endpoint parameterization is used. -/
theorem regionalArcMap_regularCoordinateGerms (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) : RegularCoordinateGerms S (regionalArcMap D j i A k) := by
  intro t e he hte
  let c := regionalArcMap D j i A k
  let γ : ℝ → M := IccExtend zero_le_one c
  let f : ℝ → Plane := A.arc k
  let d := D.chart j
  have hγ : Continuous γ := c.continuous.Icc_extend'
  have hγt : γ t = c t := IccExtend_of_mem zero_le_one c t.property
  have htd : γ t ∈ d.source := by
    rw [hγt]
    exact (regionalArcLift_spec D j i A k t).2.1
  have hte' : γ t ∈ e.source := hγt.symm ▸ hte
  obtain ⟨U, hU, hpU, K, hK, hKrep⟩ := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 d (D.chart_mem j) e he) htd hte'
  obtain ⟨V, hV, hpV, L, hL, hLrep⟩ := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he d (D.chart_mem j)) hte' htd
  let Kp : Plane → Plane := fun z => toPlane (K (toPlane.symm z))
  let Lp : Plane → Plane := fun z => toPlane (L (toPlane.symm z))
  let F : ℝ → Plane := Kp ∘ f
  have hcoord : ∀ s ∈ Icc (0 : ℝ) 1, coordinates d (γ s) = f s := by
    intro s hs
    exact (regionalArcCurve_spec D j i A k hs).2.2
  obtain ⟨a, ha, hf⟩ := A.smooth k
  let W : Set ℝ := Ioo (-a) (1 + a) ∩ (toPlane.symm ∘ f) ⁻¹' U
  have hfE : ContDiffOn ℝ ∞ (toPlane.symm ∘ f) (Ioo (-a) (1 + a)) :=
    toPlane.symm.contDiff.comp_contDiffOn hf
  have hW : IsOpen W := hfE.continuousOn.isOpen_inter_preimage isOpen_Ioo hU
  have htW : (t : ℝ) ∈ W := by
    refine ⟨?_, ?_⟩
    · constructor <;> linarith [t.property.1, t.property.2]
    · change toPlane.symm (f t) ∈ U
      rw [← hcoord t t.property]
      simpa only [coordinates, ContinuousLinearEquiv.symm_apply_apply] using hpU
  have hFOn : ContDiffOn ℝ ∞ F W := by
    simpa only [F, Kp, W, Function.comp_def] using
      toPlane.contDiff.comp_contDiffOn (hK.comp_inter hfE)
  have hfAt : ContDiffAt ℝ ∞ f t := hf.contDiffAt (isOpen_Ioo.mem_nhds (by
    constructor <;> linarith [t.property.1, t.property.2]))
  have hFAt : ContDiffAt ℝ ∞ F t := hFOn.contDiffAt (hW.mem_nhds htW)
  have hforward : ∀ᶠ s in 𝓝 (t : ℝ),
      Kp (coordinates d (γ s)) = coordinates e (γ s) := by
    filter_upwards [hKrep.comp_tendsto hγ.continuousAt] with s hs
    simpa only [Kp, coordinates, ContinuousLinearEquiv.symm_apply_apply, id_eq,
      Function.comp_def] using congrArg toPlane hs
  have hbackward : ∀ᶠ s in 𝓝 (t : ℝ),
      Lp (coordinates e (γ s)) = coordinates d (γ s) := by
    filter_upwards [hLrep.comp_tendsto hγ.continuousAt] with s hs
    simpa only [Lp, coordinates, ContinuousLinearEquiv.symm_apply_apply, id_eq,
      Function.comp_def] using congrArg toPlane hs
  have hFrep : F =ᶠ[𝓝[Icc (0 : ℝ) 1] (t : ℝ)] (fun s => coordinates e (γ s)) := by
    filter_upwards [hforward.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with s hs hsJ
    change Kp (f s) = coordinates e (γ s)
    rw [← hcoord s hsJ]
    exact hs
  have hFvalue : F t = coordinates e (γ t) := hFrep.eq_of_nhdsWithin t.property
  have hLp : ContDiffAt ℝ ∞ Lp (F t) := by
    have hl : ContDiffAt ℝ ∞ L (toPlane.symm (coordinates e (γ t))) := by
      simpa only [coordinates, ContinuousLinearEquiv.symm_apply_apply] using
        hL.contDiffAt (hV.mem_nhds hpV)
    rw [hFvalue]
    exact toPlane.contDiff.contDiffAt.comp _
      (hl.comp _ toPlane.symm.contDiff.contDiffAt)
  have hinverse : (Lp ∘ F) =ᶠ[𝓝[Icc (0 : ℝ) 1] (t : ℝ)] f := by
    filter_upwards [hFrep, hbackward.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with s hsF hsL hsJ
    rw [Function.comp_apply, hsF, hsL, hcoord s hsJ]
  have hFn : deriv F (t : ℝ) ≠ 0 := by
    intro hzero
    have hd := (hLp.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      (t : ℝ) (hFAt.differentiableAt (by simp)).hasDerivAt
    have hd' := hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hinverse.symm t.property
    have hUD := uniqueDiffOn_Icc zero_lt_one (t : ℝ) t.property
    have heq := hd'.derivWithin hUD
    rw [(hfAt.differentiableAt (by simp)).derivWithin hUD, hzero, map_zero] at heq
    exact A.regular k t t.property heq
  have hnear : ∀ᶠ s in 𝓝 (t : ℝ),
      s ∈ W ∧ γ s ∈ e.source ∧ Kp (coordinates d (γ s)) = coordinates e (γ s) := by
    filter_upwards [hW.mem_nhds htW, hγ.continuousAt.eventually (e.open_source.mem_nhds hte'),
      hforward] with s hsW hse hsK
    exact ⟨hsW, hse, hsK⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, F, hδ, hFOn.mono ?_, hFn, ?_⟩
  · intro s hs
    exact (hball (show s ∈ Metric.ball (t : ℝ) δ by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2])).1
  · intro q hq
    have hqnear := hball (show (q : ℝ) ∈ Metric.ball (t : ℝ) δ by
      simpa only [Metric.mem_ball, Real.dist_eq] using hq)
    have hγq : γ q = c q := IccExtend_of_mem zero_le_one c q.property
    refine ⟨hγq ▸ hqnear.2.1, ?_⟩
    change Kp (f q) = coordinates e (c q)
    rw [← hcoord q q.property, hqnear.2.2, hγq]

/-- The original regional arc, as an actual intrinsic regular metric arc.
Its endpoint jets come from A, not from the arbitrary graph parameterization. -/
def regionalRegularArc (g : P202.MetricData.RiemannianMetric S)
    (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) : P202.SurfaceBoundaryData.RegularArc g :=
  regularArcOfGerms g (regionalArcMap D j i A k)
    (regionalArcMap_regularCoordinateGerms D j i A k)

lemma regionalRegularArc_curve (g : P202.MetricData.RiemannianMetric S)
    (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) :
    (regionalRegularArc g D j i A k).curve = regionalArcCurve D j i A k := rfl

lemma regionalRegularArc_open_injective (g : P202.MetricData.RiemannianMetric S)
    (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) :
    InjOn (regionalRegularArc g D j i A k).curve (Ioo (0 : ℝ) 1) :=
  regionalArcCurve_open_injective D j i A k


/-- The standard real one-period parameter is embedded on its open interval. -/
lemma parameterCircle_open_interval_embedding :
    Topology.IsEmbedding (fun t : Ioo (0 : ℝ) 1 => ((t.val : ℝ) : ParameterCircle)) := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let e := AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0
  have he := Topology.IsEmbedding.subtypeVal.comp e.toHomeomorphSourceTarget.isEmbedding
  let h : Ioo (0 : ℝ) 1 ≃ₜ e.source := Homeomorph.setCongr (by simp [e])
  exact he.comp h.isEmbedding

/-- Each literal open arc of the original Jordan-curve presentation is embedded. -/
lemma arcPresentation_open_embedding {q : RegularJordanCurve}
    (A : P202Specs.PlaneTurning.ArcPresentation q) (k : Fin A.count) :
    Topology.IsEmbedding (fun t : Ioo (0 : ℝ) 1 => A.arc k t.val) := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let a := A.time k.castSucc
  let b := A.time k.succ - A.time k.castSucc
  have hb : b ≠ 0 := (sub_pos.mpr (A.strictMono k.castSucc_lt_succ)).ne'
  let f : Ioo (0 : ℝ) 1 → Ioo (0 : ℝ) 1 := fun t =>
    ⟨a + b * t.val,arcPresentation_affine_mem_Ioo A k t.property⟩
  have hfR : Topology.IsEmbedding (fun t : Ioo (0 : ℝ) 1 => a + b * t.val) :=
    (Homeomorph.addLeft a).isEmbedding.comp
      ((Homeomorph.mulLeft₀ b hb).isEmbedding.comp Topology.IsEmbedding.subtypeVal)
  have hf : Topology.IsEmbedding f :=
    (Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).mp hfR
  have hq : Topology.IsEmbedding q.parametrization :=
    (q.parametrization.continuous.isClosedEmbedding q.injective).isEmbedding
  have he := hq.comp (parameterCircle_open_interval_embedding.comp hf)
  have heq : (q.parametrization ∘ (fun t : Ioo (0 : ℝ) 1 => ((t.val : ℝ) : ParameterCircle)) ∘ f) =
      (fun t : Ioo (0 : ℝ) 1 => A.arc k t.val) := by
    funext t
    exact (A.agrees k t.val (Ioo_subset_Icc_self t.property)).symm
  rwa [heq] at he

/-- Chart coordinates transfer the embedded topology of an original Jordan
presentation to any literal original-surface curve. -/
lemma curve_open_embedding_of_arcPresentation_coordinates {q : RegularJordanCurve}
    (A : P202Specs.PlaneTurning.ArcPresentation q) (k : Fin A.count)
    (e : ModelChart 2 kind M) (c : ℝ → M)
    (hsource : ∀ t ∈ Ioo (0 : ℝ) 1, c t ∈ e.source)
    (hcoord : ∀ t ∈ Ioo (0 : ℝ) 1, coordinates e (c t) = A.arc k t) :
    Topology.IsEmbedding (fun t : Ioo (0 : ℝ) 1 => c t.val) := by
  let f : Ioo (0 : ℝ) 1 → e.source := fun t => ⟨c t.val,hsource t.val t.property⟩
  have he : Topology.IsEmbedding (fun x : e.source => coordinates e x.val) :=
    toPlane.toHomeomorph.isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal.comp
        (Topology.IsEmbedding.subtypeVal.comp e.toHomeomorphSourceTarget.isEmbedding))
  have hcoord' : (fun x : e.source => coordinates e x.val) ∘ f =
      (fun t : Ioo (0 : ℝ) 1 => A.arc k t.val) := by
    funext t
    exact hcoord t.val t.property
  have hf : Topology.IsEmbedding f := by
    apply (Topology.IsEmbedding.of_comp_iff he).mp
    rw [hcoord']
    exact arcPresentation_open_embedding A k
  exact Topology.IsEmbedding.subtypeVal.comp hf

/-- The constructed literal regional regular arc has the embedded open topology. -/
lemma regionalRegularArc_open_embedding (g : RiemannianMetric S)
    (D : RegionDecomposition S) (j : Fin D.regionCount)
    (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) :
    Topology.IsEmbedding (fun t : Ioo (0 : ℝ) 1 =>
      (regionalRegularArc g D j i A k).curve t.val) :=
  curve_open_embedding_of_arcPresentation_coordinates A k (D.chart j)
    (regionalRegularArc g D j i A k).curve
    (fun _t ht => (regionalArcCurve_spec D j i A k (Ioo_subset_Icc_self ht)).2.1)
    (fun _t ht => (regionalArcCurve_spec D j i A k (Ioo_subset_Icc_self ht)).2.2)

/-- Literal regional representatives inherit the subspace topology from their
actual original Jordan arcs and assigned original charts. -/
theorem regionalRepresentatives_open_embedding {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (j : Fin D.regionCount)
    (i : Fin (D.region j).boundaryCount) (k : Fin (A j i).count) :
    Topology.IsEmbedding (fun t : Ioo (0 : ℝ) 1 => (R.arc j i k).curve t.val) :=
  curve_open_embedding_of_arcPresentation_coordinates (A j i) k (D.chart j)
    (R.arc j i k).curve
    (fun t ht => (R.literal j i k t (Ioo_subset_Icc_self ht)).2.1)
    (fun t ht => (R.literal j i k t (Ioo_subset_Icc_self ht)).2.2)


/-- Genuine representatives for every arc of the original arbitrary family. -/
def regionalRepresentatives (g : P202.MetricData.RiemannianMetric S)
    (D : RegionDecomposition S) (A : P202Specs.RegionalBoundaryRefinement.Presentations D) :
    P202Specs.RegionalBoundaryRefinement.RegionalRepresentatives g D A where
  arc := fun j i k => regionalRegularArc g D j i (A j i) k
  left := fun _ _ _ => rfl
  right := fun _ _ _ => rfl
  literal := fun j i k t ht => regionalArcCurve_spec D j i (A j i) k ht
  injective := fun j i k => regionalRegularArc_open_injective g D j i (A j i) k
  embedding := fun j i k => regionalRegularArc_open_embedding g D j i (A j i) k
  disjoint := fun j => regionalArcCurve_images_disjoint D j (A j)

/-- The complete representative part of the assigned refinement obligation. -/
theorem regional_regular_representatives :
    P202Specs.RegionalBoundaryRefinement.Expected.regionalRepresentatives.{u} := by
  intro kind M _ _ S g D A
  exact ⟨regionalRepresentatives g D A⟩


open P202Specs.RegionalBoundaryRefinement P202Specs.GlobalGaussBonnet
open P202.MetricData

/-- Open injectivity on either kind of occurrence's actual parameter interval. -/
lemma occurrenceArc_injective {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) (o : Occurrence A B) :
    InjOn (occurrenceArc R B o).curve
      (Ioo (occurrenceArc R B o).left (occurrenceArc R B o).right) := by
  rcases o with ⟨j, i, k⟩ | b
  · simpa only [occurrenceArc, R.left, R.right] using R.injective j i k
  · exact B.injective b

/-- All required geometric cuts are a finite set of actual original points. -/
def refinementForbiddenPoints {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) : Set M :=
  range D.graph.vertex ∪
    (range (fun o : Occurrence A B =>
      (occurrenceArc R B o).curve (occurrenceArc R B o).left) ∪
    range (fun o : Occurrence A B =>
      (occurrenceArc R B o).curve (occurrenceArc R B o).right)) ∪
    ⋃ j, ⋃ i, (D.chart j).source ∩ coordinates (D.chart j) ⁻¹'
      (((D.region j).curve i).parametrization ''
        (((D.region j).curve i).joins : Set ParameterCircle))

lemma refinementForbiddenPoints_finite {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) : (refinementForbiddenPoints R B).Finite := by
  classical
  apply ((finite_range _).union ((finite_range _).union (finite_range _))).union
  apply Set.finite_iUnion
  intro j
  apply Set.finite_iUnion
  intro i
  apply Set.Finite.of_injOn (t := ((D.region j).curve i).parametrization ''
    (((D.region j).curve i).joins : Set ParameterCircle)) (fun _ ht => ht.2)
    ((coordinates_injOn (D.chart j)).mono inter_subset_left)
  exact ((D.region j).curve i).joins.finite_toSet.image _

/-- Every finite actual point set has finite open preimage on every occurrence. -/
lemma occurrenceArc_cutParameters_finite {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) (o : Occurrence A B) {F : Set M} (hF : F.Finite) :
    (Ioo (occurrenceArc R B o).left (occurrenceArc R B o).right ∩
      (occurrenceArc R B o).curve ⁻¹' F).Finite := by
  exact Set.Finite.of_injOn (t := F) (fun _ ht => ht.2)
    ((occurrenceArc_injective R B o).mono inter_subset_left) hF

/-- Simultaneous vertex/endpoint/Jordan-join cuts, in the original parameters. -/
def refinementCuts {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) (o : Occurrence A B) : Finset ℝ :=
  insert (occurrenceArc R B o).left (insert (occurrenceArc R B o).right
    (occurrenceArc_cutParameters_finite R B o (refinementForbiddenPoints_finite R B)).toFinset)

lemma refinementCuts_left {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) (o : Occurrence A B) :
    (occurrenceArc R B o).left ∈ refinementCuts R B o := by
  simp only [refinementCuts, Finset.mem_insert, true_or]

lemma refinementCuts_right {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) (o : Occurrence A B) :
    (occurrenceArc R B o).right ∈ refinementCuts R B o := by
  simp only [refinementCuts, Finset.mem_insert, true_or, or_true]

lemma refinementCuts_bounds {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) (o : Occurrence A B) :
    (refinementCuts R B o : Set ℝ) ⊆
      Icc (occurrenceArc R B o).left (occurrenceArc R B o).right := by
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact ⟨le_rfl, (occurrenceArc R B o).ordered.le⟩
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact ⟨(occurrenceArc R B o).ordered.le, le_rfl⟩
  exact Ioo_subset_Icc_self ((occurrenceArc_cutParameters_finite R B o (refinementForbiddenPoints_finite R B)).mem_toFinset.mp ht).1

lemma mem_refinementCuts_of_point {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) (o : Occurrence A B) {t : ℝ}
    (ht : t ∈ Icc (occurrenceArc R B o).left (occurrenceArc R B o).right)
    (hp : (occurrenceArc R B o).curve t ∈ refinementForbiddenPoints R B) :
    t ∈ refinementCuts R B o := by
  rcases eq_or_lt_of_le ht.1 with h | hl
  · exact h ▸ refinementCuts_left R B o
  rcases eq_or_lt_of_le ht.2 with h | hr
  · exact h.symm ▸ refinementCuts_right R B o
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  exact (occurrenceArc_cutParameters_finite R B o (refinementForbiddenPoints_finite R B)).mem_toFinset.mpr ⟨⟨hl, hr⟩, hp⟩

/-- The accepted adjacent-gap representation is bridged to the independent
finite-subdivision interface. This proves every cut and exact partition clause,
without presupposing geometric mates or sector incidence. -/
def finiteSubdivision (g : RiemannianMetric S) (D : RegionDecomposition S)
    (A : Presentations D) (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) : FiniteSubdivision R B := by
  classical
  let P := Σ o : Occurrence A B, FiniteGap (refinementCuts R B o)
  let e : Fin (Fintype.card P) ≃ P := (Fintype.equivFin P).symm
  refine {
    cuts := refinementCuts R B
    cuts_left := refinementCuts_left R B
    cuts_right := refinementCuts_right R B
    cuts_bounds := refinementCuts_bounds R B
    cuts_vertices := ?_
    cuts_endpoints := ?_
    cuts_joins := ?_
    count := Fintype.card P
    occurrence := fun h => (e h).1
    left := fun h => (e h).2.left
    right := fun h => (e h).2.right
    ordered := fun h => (e h).2.ordered
    left_cut := fun h => (e h).2.left_mem
    right_cut := fun h => (e h).2.right_mem
    cut_free := ?_
    disjoint := ?_
    covers := ?_ }
  · intro o t ht hp
    apply mem_refinementCuts_of_point R B o ht
    exact Or.inl (Or.inl hp)
  · intro o t ht z hz
    apply mem_refinementCuts_of_point R B o ht
    apply Or.inl
    apply Or.inr
    rcases hz with hz | hz
    · exact Or.inl ⟨z, hz.symm⟩
    · exact Or.inr ⟨z, hz.symm⟩
  · intro o t ht j i q hq hs hc
    apply mem_refinementCuts_of_point R B o ht
    apply Or.inr
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨i, hs, q, hq, hc.symm⟩⟩
  · intro h t ht hf
    exact Set.disjoint_left.mp (e h).2.avoids ht hf
  · intro h k hne he
    have hp : e h ≠ e k := fun h => hne (e.injective h)
    rcases eh : e h with ⟨oh, gh⟩
    rcases ek : e k with ⟨ok, gk⟩
    simp only [eh, ek] at he ⊢
    subst ok
    exact FiniteGap.disjoint _ (fun hgg => hp (by simp only [eh, ek, hgg]))
  · intro o t ht hn
    obtain ⟨q, hq⟩ := FiniteGap.containing (refinementCuts R B o)
      (refinementCuts_left R B o) (refinementCuts_right R B o) ht hn
    refine ⟨e.symm ⟨o, q⟩, ?_, ?_⟩
    · simp only [e.apply_symm_apply]
    · change t ∈ Ioo (e (e.symm (⟨o, q⟩ : P))).2.left
        (e (e.symm (⟨o, q⟩ : P))).2.right
      rw [Equiv.apply_symm_apply]
      exact hq

/-- Finite common cuts and exact interval coverage, prior to geometric pairing. -/
theorem regional_boundary_finite_subdivision :
    P202Specs.RegionalBoundaryRefinement.Expected.finiteSubdivision.{u} := by
  intro kind M _ _ S g D A B
  let R := regionalRepresentatives g D A
  exact ⟨R, ⟨finiteSubdivision g D A R B⟩⟩


/-- Every literal occurrence, including B arcs, lies on the original graph. -/
lemma occurrenceArc_on_graph {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) (o : Occurrence A B) {t : ℝ}
    (ht : t ∈ Icc (occurrenceArc R B o).left (occurrenceArc R B o).right) :
    (occurrenceArc R B o).curve t ∈ D.graph.carrier := by
  rcases o with ⟨j, i, k⟩ | b
  · have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [occurrenceArc, R.left, R.right] using ht
    exact (R.literal j i k t ht').1.2
  · apply D.contains_boundary
    rw [B.covers]
    exact mem_iUnion.mpr ⟨b, t, ht, rfl⟩

lemma subdivision_piece_bounds {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} {R : RegionalRepresentatives g D A}
    {B : BoundaryPresentation g} (F : FiniteSubdivision R B) (h : Fin F.count) :
    Icc (F.left h) (F.right h) ⊆
      Icc (occurrenceArc R B (F.occurrence h)).left
        (occurrenceArc R B (F.occurrence h)).right := by
  intro t ht
  exact ⟨(F.cuts_bounds _ (F.left_cut h)).1.trans ht.1,
    ht.2.trans (F.cuts_bounds _ (F.right_cut h)).2⟩

/-- All pieces of the simultaneous partition, including original B pieces,
localize to one actual open graph edge. -/
theorem subdivision_piece_one_openEdge {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (F : FiniteSubdivision R B) (h : Fin F.count) :
    ∃ e : Fin D.graph.edgeCount,
      (occurrenceArc R B (F.occurrence h)).curve '' Ioo (F.left h) (F.right h) ⊆
        D.graph.edge e '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
  apply connected_graph_subset_one_openEdge D.graph
  · apply (isConnected_Ioo (F.ordered h)).image
    exact (occurrenceArc R B (F.occurrence h)).continuous.mono
      (Ioo_subset_Icc_self.trans (subdivision_piece_bounds F h))
  · rintro p ⟨t, ht, rfl⟩
    exact occurrenceArc_on_graph R B (F.occurrence h)
      (subdivision_piece_bounds F h (Ioo_subset_Icc_self ht))
  · apply Set.disjoint_left.mpr
    rintro p ⟨t, ht, rfl⟩ hp
    exact F.cut_free h t ht (F.cuts_vertices _ t
      (subdivision_piece_bounds F h (Ioo_subset_Icc_self ht)) hp)

/-- Every open regional piece avoids the literal original Jordan joins
needed when applying the independent density theorem. -/
theorem subdivision_piece_nonjoin {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (F : FiniteSubdivision R B) (h : Fin F.count)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount) (k : Fin (A j i).count)
    (ho : F.occurrence h = .inl ⟨j, i, k⟩)
    {t : ℝ} (ht : t ∈ Ioo (F.left h) (F.right h)) :
    (((A j i).time k.castSucc + ((A j i).time k.succ -
      (A j i).time k.castSucc) * t : ℝ) : ParameterCircle) ∉ ((D.region j).curve i).joins := by
  intro hj
  have htbase := subdivision_piece_bounds F h (Ioo_subset_Icc_self ht)
  have htunit : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [ho, occurrenceArc, R.left, R.right] using htbase
  have hlit := R.literal j i k t htunit
  apply F.cut_free h t ht
  apply F.cuts_joins _ t htbase j i _ hj
  · simpa only [ho, occurrenceArc] using hlit.2.1
  · simpa only [ho, occurrenceArc, realLift] using
      hlit.2.2.trans ((A j i).agrees k t htunit)

/-- The full common refinement in the empty original-surface case. Both
occurrence kinds are empty because each would give an actual original point. -/
theorem regional_boundary_refinement_of_isEmpty [IsEmpty M]
    (g : RiemannianMetric S) (D : RegionDecomposition S) (A : Presentations D)
    (B : BoundaryPresentation g) :
    ∃ R : RegionalRepresentatives g D A, Nonempty (CommonRefinement R B) := by
  let R := regionalRepresentatives g D A
  let F := finiteSubdivision g D A R B
  haveI : IsEmpty (Occurrence A B) :=
    ⟨fun o => isEmptyElim ((occurrenceArc R B o).curve 0)⟩
  haveI : IsEmpty (Fin F.count) := ⟨fun h => isEmptyElim (F.occurrence h)⟩
  refine ⟨R, ⟨{
    toFiniteSubdivision := F
    mate := fun h => isEmptyElim h
    involutive := fun h => isEmptyElim h
    fixed_point_free := fun h => isEmptyElim h
    no_boundary_boundary := fun h => isEmptyElim h
    edge := fun h => isEmptyElim h
    edge_mate := fun h => isEmptyElim h
    in_edge := fun h => isEmptyElim h
    trace_eq := fun h => isEmptyElim h
    transition := fun h => isEmptyElim h
    continuous := fun h => isEmptyElim h
    monotone := fun h => isEmptyElim h
    image_open := fun h => isEmptyElim h
    image_closed := fun h => isEmptyElim h
    point_eq := fun h => isEmptyElim h
    hasDerivAt := fun h => isEmptyElim h
    derivative_sign := fun h => isEmptyElim h
    interior_incidence := fun h => isEmptyElim h
    boundary_incidence := fun h => isEmptyElim h }⟩⟩

section StarGeometry
variable {G : EmbeddedGraph S} {p : M}

def starRadialModel (s : GraphStar G p) (x : M) (t : unitInterval) :
    ModelSpace 2 kind :=
  ⟨(1 - (t : ℝ)) • (s.chart p).val + (t : ℝ) • (s.chart x).val,
    (SmoothManifolds.convex_modelSet 2 kind) (s.chart p).property (s.chart x).property
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩

lemma starRadialModel_continuous (s : GraphStar G p) (x : M) :
    Continuous (starRadialModel s x) := by
  apply Continuous.subtype_mk
  fun_prop

lemma starRadialModel_coordinates (s : GraphStar G p) (x : M) (t : unitInterval) :
    toPlane (starRadialModel s x t).val =
      coordinates s.chart p + (t : ℝ) • (coordinates s.chart x - coordinates s.chart p) := by
  simp only [starRadialModel, map_add, map_smul, coordinates]
  module

lemma starRadialModel_ball (s : GraphStar G p) {x : M} (hx : x ∈ s.neighborhood)
    (t : unitInterval) :
    toPlane (starRadialModel s x t).val ∈ Metric.ball (coordinates s.chart p) s.radius := by
  rw [starRadialModel_coordinates, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  have hx' : ‖coordinates s.chart x - coordinates s.chart p‖ < s.radius := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      (show coordinates s.chart x ∈ Metric.ball (coordinates s.chart p) s.radius from hx.2)
  exact (mul_le_of_le_one_left (norm_nonneg _) t.property.2).trans_lt hx'

def starRadialCurve (s : GraphStar G p) (x : M) : unitInterval → M :=
  fun t => s.chart.symm (starRadialModel s x t)

lemma starRadialCurve_mem (s : GraphStar G p) {x : M} (hx : x ∈ s.neighborhood)
    (t : unitInterval) : starRadialCurve s x t ∈ s.neighborhood := by
  have htar := s.ball_in_target _ (starRadialModel_ball s hx t)
  refine ⟨s.chart.map_target htar, ?_⟩
  change toPlane (s.chart (s.chart.symm (starRadialModel s x t))).val ∈
    Metric.ball (coordinates s.chart p) s.radius
  rw [s.chart.right_inv htar]
  exact starRadialModel_ball s hx t

lemma starRadialCurve_coordinates (s : GraphStar G p) {x : M}
    (hx : x ∈ s.neighborhood) (t : unitInterval) :
    coordinates s.chart (starRadialCurve s x t) =
      coordinates s.chart p + (t : ℝ) • (coordinates s.chart x - coordinates s.chart p) := by
  have htar := s.ball_in_target _ (starRadialModel_ball s hx t)
  change toPlane (s.chart (s.chart.symm (starRadialModel s x t))).val = _
  rw [s.chart.right_inv htar, starRadialModel_coordinates]

lemma starRadialCurve_continuous (s : GraphStar G p) {x : M}
    (hx : x ∈ s.neighborhood) : Continuous (starRadialCurve s x) :=
  s.chart.continuousOn_symm.comp_continuous (starRadialModel_continuous s x)
    (fun t => s.ball_in_target _ (starRadialModel_ball s hx t))

lemma starRadialCurve_zero (s : GraphStar G p) (x : M) :
    starRadialCurve s x 0 = p := by
  change s.chart.symm (starRadialModel s x 0) = p
  have h : starRadialModel s x 0 = s.chart p := by
    apply Subtype.ext
    simp [starRadialModel]
  rw [h, s.chart.left_inv s.mem_source]

lemma starRadialCurve_one (s : GraphStar G p) {x : M} (hx : x ∈ s.neighborhood) :
    starRadialCurve s x 1 = x := by
  change s.chart.symm (starRadialModel s x 1) = x
  have h : starRadialModel s x 1 = s.chart x := by
    apply Subtype.ext
    simp [starRadialModel]
  rw [h, s.chart.left_inv hx.1]

lemma starRadialCurve_avoids (s : GraphStar G p) {x : M}
    (hx : x ∈ s.neighborhood) (hxG : x ∉ G.carrier)
    {t : unitInterval} (ht : 0 < (t : ℝ)) : starRadialCurve s x t ∉ G.carrier := by
  intro hG
  have hmem := starRadialCurve_mem s hx t
  have hpG : p ∈ G.carrier :=
    (s.graph_eq p s.mem_source (by simpa only [Metric.mem_ball, dist_self] using s.radius_pos)).mpr (Or.inl rfl)
  have hxp : x ≠ p := fun h => hxG (h ▸ hpG)
  have hdisp : coordinates s.chart x - coordinates s.chart p ≠ 0 := by
    intro h
    apply hxp
    apply s.chart.injOn hx.1 s.mem_source
    apply Subtype.ext
    exact toPlane.injective (sub_eq_zero.mp h)
  rcases (s.graph_eq _ hmem.1 hmem.2).mp hG with heq | ⟨i, r, hr, hrr, heq⟩
  · have hz : (t : ℝ) • (coordinates s.chart x - coordinates s.chart p) = 0 := by
      have hcoord := starRadialCurve_coordinates s hx t
      rw [heq] at hcoord
      exact (add_eq_left.mp hcoord.symm)
    exact (smul_ne_zero ht.ne' hdisp) hz
  · rw [starRadialCurve_coordinates s hx t] at heq
    have hv : (t : ℝ) • (coordinates s.chart x - coordinates s.chart p) = r • s.direction i :=
      add_left_cancel heq
    have he : coordinates s.chart x - coordinates s.chart p = (r / (t : ℝ)) • s.direction i := by
      calc
        _ = (t : ℝ)⁻¹ • ((t : ℝ) • (coordinates s.chart x - coordinates s.chart p)) :=
          (inv_smul_smul₀ ht.ne' _).symm
        _ = (t : ℝ)⁻¹ • (r • s.direction i) := by rw [hv]
        _ = (r / (t : ℝ)) • s.direction i := by rw [smul_smul]; congr 1; ring
    have hpos : 0 < r / (t : ℝ) := div_pos hr ht
    have hn : ‖coordinates s.chart x - coordinates s.chart p‖ = r / (t : ℝ) := by
      rw [he, norm_smul, s.direction_unit, Real.norm_eq_abs, abs_of_pos hpos, mul_one]
    have hlt : r / (t : ℝ) < s.radius := by
      rw [← hn]
      simpa only [Metric.mem_ball, dist_eq_norm] using
      (show coordinates s.chart x ∈ Metric.ball (coordinates s.chart p) s.radius from hx.2)
    apply hxG
    apply (s.graph_eq x hx.1 hx.2).mpr
    exact Or.inr ⟨i, r / (t : ℝ), hpos, hlt, by rw [← he]; abel⟩

/-- Every actual local sector accumulates at the star center, with no
endpoint-germ, arrangement, incidence or cardinality assumption. -/
theorem graphStar_center_mem_closure_component (s : GraphStar G p)
    (a : ConnectedComponents (s.neighborhood \ G.carrier : Set M)) :
    p ∈ closure (componentSet (s.neighborhood \ G.carrier) a) := by
  obtain ⟨x, hx⟩ := Components.nonempty (s.neighborhood \ G.carrier) a
  have hxN := (Components.subset (s.neighborhood \ G.carrier) a hx).1
  have hxG := (Components.subset (s.neighborhood \ G.carrier) a hx).2
  let c := starRadialCurve s x
  have hcont : Continuous c := starRadialCurve_continuous s hxN
  have himage : c '' Ioc (0 : unitInterval) 1 ⊆ componentSet (s.neighborhood \ G.carrier) a := by
    apply Components.contains_preconnected (s.neighborhood \ G.carrier)
      (isPreconnected_Ioc.image c hcont.continuousOn)
    · rintro y ⟨t, ht, rfl⟩
      exact ⟨starRadialCurve_mem s hxN t, starRadialCurve_avoids s hxN hxG ht.1⟩
    · refine ⟨x, ?_, hx⟩
      exact ⟨1, ⟨zero_lt_one, le_rfl⟩, starRadialCurve_one s hxN⟩
  have hzero : (0 : unitInterval) ∈ closure (Ioc (0 : unitInterval) 1) := by
    rw [closure_Ioc (zero_ne_one : (0 : unitInterval) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  have h := mem_closure_image (f := c) hcont.continuousAt hzero
  have hp : c 0 = p := starRadialCurve_zero s x
  rw [hp] at h
  exact closure_mono himage h
lemma componentSet_injective {M : Type u} [TopologicalSpace M] (U : Set M) : Function.Injective (componentSet U) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
  have hx : x.val ∈ componentSet U (ConnectedComponents.mk x) := ⟨x, rfl, rfl⟩
  have hxb : x.val ∈ componentSet U b := hab ▸ hx
  obtain ⟨y, hy, hyx⟩ := hxb
  have hyx' : y = x := Subtype.ext hyx
  change ConnectedComponents.mk y = b at hy
  simpa only [hyx'] using hy


/-- If every local sector has the star center in its closure, the exact
occupancy fields give a genuine equivalence between incident regional closures
and local sectors. The center-closure condition is elementary radial star
geometry, independent of global incidence and of edge endpoint regularity. -/
theorem regional_incidence_equiv_local_components
    (D : RegionDecomposition S) (p : M) (N : Set M)
    (hforward : ∀ j : Fin D.regionCount,
      p ∈ closure (componentSet D.graph.carrierᶜ (D.component j)) →
      ∃ a : ConnectedComponents (N \ D.graph.carrier : Set M),
        componentSet D.graph.carrierᶜ (D.component j) ∩ N =
          componentSet (N \ D.graph.carrier) a)
    (hback : ∀ a : ConnectedComponents (N \ D.graph.carrier : Set M),
      ∃! j : Fin D.regionCount,
        componentSet D.graph.carrierᶜ (D.component j) ∩ N =
          componentSet (N \ D.graph.carrier) a)
    (hcenter : ∀ a : ConnectedComponents (N \ D.graph.carrier : Set M),
      p ∈ closure (componentSet (N \ D.graph.carrier) a)) :
    Nonempty ({j : Fin D.regionCount //
      p ∈ closure (componentSet D.graph.carrierᶜ (D.component j))} ≃
      ConnectedComponents (N \ D.graph.carrier : Set M)) := by
  classical
  let J := {j : Fin D.regionCount //
    p ∈ closure (componentSet D.graph.carrierᶜ (D.component j))}
  let f : J → ConnectedComponents (N \ D.graph.carrier : Set M) :=
    fun j => (hforward j.val j.property).choose
  have hf (j : J) : componentSet D.graph.carrierᶜ (D.component j.val) ∩ N =
      componentSet (N \ D.graph.carrier) (f j) :=
    (hforward j.val j.property).choose_spec
  have hinj : Function.Injective f := by
    intro j k hjk
    obtain ⟨i, hi, huniq⟩ := hback (f j)
    have hj : j.val = i := huniq j.val (hf j)
    have hk : k.val = i := huniq k.val (by rw [hjk]; exact hf k)
    exact Subtype.ext (hj.trans hk.symm)
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨i, hi, _⟩ := hback a
    have hp : p ∈ closure (componentSet D.graph.carrierᶜ (D.component i)) := by
      apply closure_mono (inter_subset_left :
        componentSet D.graph.carrierᶜ (D.component i) ∩ N ⊆ _) 
      rw [hi]
      exact hcenter a
    let j : J := ⟨i, hp⟩
    refine ⟨j, ?_⟩
    apply componentSet_injective (N \ D.graph.carrier)
    exact (hf j).symm.trans hi
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩⟩


/-- Original occupancy gives the exact incidence/local-sector equivalence;
radial center-closure is derived internally, not supplied as a premise. -/
theorem regional_incidence_equiv_star_components (D : RegionDecomposition S)
    (p : M) (hp : p ∈ D.graph.carrier) (O : Set M) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ s : GraphStar D.graph p, s.neighborhood ⊆ O ∧
      Nonempty ({j : Fin D.regionCount //
        p ∈ closure (componentSet D.graph.carrierᶜ (D.component j))} ≃
        ConnectedComponents (s.neighborhood \ D.graph.carrier : Set M)) := by
  obtain ⟨s, hsO, hforward, hback⟩ := D.sectors p hp O hO hpO
  exact ⟨s, hsO, regional_incidence_equiv_local_components D p s.neighborhood
    hforward hback (graphStar_center_mem_closure_component s)⟩

/-- Finitely many closed regions not incident at p disappear on a neighborhood
of p. This identifies the actual occupied-set germ, without assuming a pair of
incident labels or any incidence cardinality. -/
theorem regional_closures_incident_germ (D : RegionDecomposition S) (p : M) :
    (⋃ j ∈ P202Specs.RegionalBoundaryRefinement.incidentRegions D p,
      P202Specs.SurfaceRegionsEuler.regionClosure D j) =ᶠ[nhds p]
      (⋃ j, P202Specs.SurfaceRegionsEuler.regionClosure D j) := by
  classical
  have he : ∀ j : Fin D.regionCount, ∀ᶠ x in nhds p,
      x ∈ P202Specs.SurfaceRegionsEuler.regionClosure D j →
        p ∈ P202Specs.SurfaceRegionsEuler.regionClosure D j := by
    intro j
    by_cases hp : p ∈ P202Specs.SurfaceRegionsEuler.regionClosure D j
    · exact Filter.Eventually.of_forall (fun _ _ => hp)
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hp] with x hx hmem
      exact (hx hmem).elim
  filter_upwards [Filter.eventually_all.mpr he] with x hx
  apply propext
  constructor
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    obtain ⟨_, hj⟩ := mem_iUnion.mp hj
    exact mem_iUnion.mpr ⟨j, hj⟩
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hx j hj, hj⟩⟩

end StarGeometry

/-! Generic open-edge stars and their exact local sectors. -/
namespace OpenEdgeStars
open P202.SurfaceRegionConstruction.BoundaryCycles
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

lemma edge_interval_neighborhood (G : EmbeddedGraph S) (i : Fin G.edgeCount)
    (q : unitInterval) (hq : 0 < (q : ℝ) ∧ (q : ℝ) < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ O : Set M, IsOpen O ∧ G.edge i q ∈ O ∧
      ∀ x ∈ O, x ∈ G.carrier →
        ∃ t : unitInterval, |(t : ℝ) - (q : ℝ)| < δ ∧ G.edge i t = x := by
  let := S.topologicalManifold.hausdorff
  obtain ⟨O,hO,hqO,hOg⟩ := open_edge_neighborhood G i q hq
  let K : Set unitInterval := {t | δ ≤ |(t : ℝ) - (q : ℝ)|}
  have hK : IsCompact K := (isClosed_le continuous_const
    ((continuous_subtype_val.sub continuous_const).abs)).isCompact
  have hpK : G.edge i q ∉ G.edge i '' K := by
    rintro ⟨t,ht,hqt⟩
    have htV : G.edge i t ∉ range G.vertex := by
      rw [hqt]
      exact G.avoids_vertices i q hq.1 hq.2
    have hti : 0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
      have := EmbeddedGraph.edge_preimage_compl_vertices G i
      exact (Set.ext_iff.mp this t).mp htV
    have htq := G.open_injective i hti hq hqt
    subst t
    exact (not_le_of_gt hδ) (by simpa [K] using ht)
  refine ⟨O ∩ (G.edge i '' K)ᶜ,hO.inter (hK.image (G.edge i).continuous).isClosed.isOpen_compl,
    ⟨hqO,hpK⟩,?_⟩
  intro x hx hxg
  obtain ⟨t,ht⟩ := (Set.ext_iff.mp hOg x).mp ⟨hx.1,hxg⟩ |>.2
  let t' : unitInterval := ⟨t.val,t.property.1.le,t.property.2.le⟩
  refine ⟨t',?_,ht⟩
  by_contra hn
  exact hx.2 ⟨t',le_of_not_gt hn,ht⟩

/-- Every star at an actual regular open edge point has two opposite rays.
The ray bijection uses embedded-interval topology, while its opposite-direction
property uses only regularity at the actual interior parameter. -/
theorem graphStar_open_edge_two_rays (G : EmbeddedGraph S) (i : Fin G.edgeCount)
    (q : unitInterval) (hq : 0 < (q : ℝ) ∧ (q : ℝ) < 1)
    (g : GraphStar G (G.edge i q)) :
    ∃ r : Bool ≃ Fin g.rayCount, g.direction (r true) = -g.direction (r false) := by
  let c : ℝ → M := fun t => IccExtend zero_le_one (G.edge i) ((q : ℝ) + t)
  have hc : Continuous c := (G.edge i).continuous.Icc_extend'.comp
    (continuous_const.add continuous_id)
  have hc0 : c 0 = G.edge i q := by
    simp only [c,add_zero,IccExtend_of_mem zero_le_one (G.edge i) q.property]
  have hnear : c ⁻¹' g.neighborhood ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by
      rw [hc0]
      exact (P202.SurfaceRegionConstruction.GraphStar.isOpen_neighborhood g).mem_nhds
        (P202.SurfaceRegionConstruction.GraphStar.mem_neighborhood g))
  obtain ⟨ε,hε,hεball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ := min ε (min (q : ℝ) (1 - (q : ℝ))) / 2
  have hδ : 0 < δ := half_pos (lt_min hε (lt_min hq.1 (sub_pos.mpr hq.2)))
  have hδε : δ < ε := by
    have := min_le_left ε (min (q : ℝ) (1 - (q : ℝ)))
    dsimp [δ]; linarith
  have hδq : δ < (q : ℝ) := by
    have := min_le_right ε (min (q : ℝ) (1 - (q : ℝ)))
    have := min_le_left (q : ℝ) (1 - (q : ℝ))
    dsimp [δ]; linarith
  have hδ1 : δ < 1 - (q : ℝ) := by
    have := min_le_right ε (min (q : ℝ) (1 - (q : ℝ)))
    have := min_le_right (q : ℝ) (1 - (q : ℝ))
    dsimp [δ]; linarith
  let a : Bool → ℝ → ℝ := fun b t => if b then -t else t
  have habs (b : Bool) (t : ℝ) : |a b t| = |t| := by
    cases b <;> simp [a]
  have hparam (b : Bool) {t : ℝ} (ht : t ∈ Icc 0 δ) :
      (q : ℝ) + a b t ∈ Ioo (0 : ℝ) 1 := by
    cases b <;> simp only [a,Bool.false_eq_true,ite_false,ite_true] <;>
      constructor <;> linarith [ht.1,ht.2]
  have hmem (b : Bool) {t : ℝ} (ht : t ∈ Icc 0 δ) : c (a b t) ∈ g.neighborhood := by
    apply hεball
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,habs,abs_of_nonneg ht.1]
    exact ht.2.trans_lt hδε
  have hceq (b : Bool) {t : ℝ} (ht : t ∈ Icc 0 δ) :
      c (a b t) = G.edge i ⟨(q : ℝ) + a b t,(hparam b ht).1.le,(hparam b ht).2.le⟩ := by
    exact IccExtend_of_mem zero_le_one (G.edge i) ⟨(hparam b ht).1.le,(hparam b ht).2.le⟩
  have hne (b : Bool) {t : ℝ} (ht : t ∈ Ioo 0 δ) : c (a b t) ≠ G.edge i q := by
    intro heq
    rw [hceq b ⟨ht.1.le,ht.2.le⟩] at heq
    have h := congrArg (fun r : unitInterval => (r : ℝ))
      (G.open_injective i (hparam b ⟨ht.1.le,ht.2.le⟩) hq heq)
    cases b <;> simp only [a,Bool.false_eq_true,ite_false,ite_true] at h <;> linarith [ht.1]
  have hfixed (b : Bool) : ∃ k : Fin g.rayCount, ∀ t ∈ Ioo 0 δ,
      coordinates g.chart (c (a b t)) - coordinates g.chart (G.edge i q) =
        ‖coordinates g.chart (c (a b t)) - coordinates g.chart (G.edge i q)‖ • g.direction k := by
    apply fixed_ray_of_graphStar_arc g (fun t => c (a b t)) δ hδ
    · exact (hc.comp (by cases b <;> dsimp [a] <;> fun_prop)).continuousOn
    · exact fun t ht => hmem b ht
    · exact fun t ht => hne b ht
    · intro t ht
      rw [hceq b ⟨ht.1.le,ht.2.le⟩]
      exact Or.inr (mem_iUnion.mpr ⟨i,_,rfl⟩)
  let r : Bool → Fin g.rayCount := fun b => Classical.choose (hfixed b)
  have hray (b : Bool) : ∀ t ∈ Ioo 0 δ,
      coordinates g.chart (c (a b t)) - coordinates g.chart (G.edge i q) =
        ‖coordinates g.chart (c (a b t)) - coordinates g.chart (G.edge i q)‖ • g.direction (r b) :=
    Classical.choose_spec (hfixed b)
  have hrinj : Function.Injective r := by
    intro b d hbd
    let f : Bool → ℝ → Plane := fun b t =>
      coordinates g.chart (c (a b t)) - coordinates g.chart (G.edge i q)
    have hfcont (b : Bool) : ContinuousOn (f b) (Icc 0 δ) := by
      apply ContinuousOn.sub _ continuousOn_const
      exact (continuousOn_coordinates g.chart).comp
        ((hc.comp (by cases b <;> dsimp [a] <;> fun_prop)).continuousOn)
        (fun t ht => (hmem b ht).1)
    have hfzero (b : Bool) : f b 0 = 0 := by
      simp only [f,a,neg_zero,ite_self,hc0,sub_self]
    have hfne (b : Bool) : f b (δ/2) ≠ 0 := by
      intro heq
      exact hne b (by constructor <;> linarith)
        (coordinates_injOn g.chart (hmem b (by constructor <;> linarith)).1
          g.mem_source (sub_eq_zero.mp heq))
    obtain ⟨s,hs,t,ht,hst⟩ := same_ray_arcs_intersect (f b) (f d) (g.direction (r b)) δ hδ
      (hfcont b) (hfcont d) (hfzero b) (hfzero d) (hfne b) (hfne d)
      (hray b) (by simpa only [← hbd] using hray d)
    have hpoint := coordinates_injOn g.chart (hmem b ⟨hs.1.le,hs.2.le⟩).1
      (hmem d ⟨ht.1.le,ht.2.le⟩).1 (sub_left_inj.mp hst)
    rw [hceq b ⟨hs.1.le,hs.2.le⟩,hceq d ⟨ht.1.le,ht.2.le⟩] at hpoint
    have heq := congrArg (fun r : unitInterval => (r : ℝ))
      (G.open_injective i (hparam b ⟨hs.1.le,hs.2.le⟩)
        (hparam d ⟨ht.1.le,ht.2.le⟩) hpoint)
    cases b <;> cases d <;> simp_all only [a,Bool.false_eq_true,ite_false,ite_true] <;>
      linarith [hs.1,ht.1]
  have hrsurj : Function.Surjective r := by
    intro k
    obtain ⟨O,hO,hpO,hOedge⟩ := edge_interval_neighborhood G i q hq δ hδ
    obtain ⟨x,hxO,hxg,hxne,ρ,hρ,hρR,hxcoord⟩ := graphStar_ray_meets_open g k O hO hpO
    have hxgraph : x ∈ G.carrier := (g.graph_eq x hxg.1 hxg.2).mpr
      (Or.inr ⟨k,ρ,hρ,hρR,hxcoord⟩)
    obtain ⟨t,htδ,hxt⟩ := hOedge x hxO hxgraph
    have htne : (t : ℝ) ≠ (q : ℝ) := by
      intro heq
      exact hxne (hxt.symm.trans (congrArg (G.edge i) (Subtype.ext heq)))
    have hex : ∃ (b : Bool) (s : ℝ), s ∈ Ioo 0 δ ∧ c (a b s) = x := by
      rcases lt_or_gt_of_ne htne with hlt | hgt
      · refine ⟨true,(q : ℝ) - (t : ℝ),⟨sub_pos.mpr hlt,?_⟩,?_⟩
        · rwa [abs_of_neg (sub_neg.mpr hlt),neg_sub] at htδ
        · simp only [a,ite_true,neg_sub,c,add_sub_cancel]
          rw [IccExtend_of_mem zero_le_one (G.edge i) t.property]
          exact hxt
      · refine ⟨false,(t : ℝ) - (q : ℝ),⟨sub_pos.mpr hgt,?_⟩,?_⟩
        · rwa [abs_of_pos (sub_pos.mpr hgt)] at htδ
        · simp only [a,Bool.false_eq_true,ite_false,c,add_sub_cancel]
          rw [IccExtend_of_mem zero_le_one (G.edge i) t.property]
          exact hxt
    obtain ⟨b,s,hs,hcs⟩ := hex
    have heq := hray b s hs
    rw [hcs,hxcoord,add_sub_cancel_left,norm_smul,g.direction_unit,
      Real.norm_eq_abs,abs_of_pos hρ,mul_one] at heq
    refine ⟨b,?_⟩
    apply g.direction_injective
    exact (smul_right_injective _ hρ.ne' heq).symm
  let F : ℝ → Plane := fun t => coordinates g.chart (IccExtend zero_le_one (G.edge i) t)
  let v : Plane := deriv F (q : ℝ)
  obtain ⟨hsm,hnv⟩ := RegularOpenEdge.in_chart (G.regular i) (q : ℝ) hq
    g.chart g.chart_mem g.mem_source
  have hDF : HasDerivAt F v (q : ℝ) :=
    (hsm.differentiableAt (by simp)).hasDerivAt
  have hDplus : HasDerivAt (fun t => F ((q : ℝ) + t)) v 0 := by
    have hDF' : HasDerivAt F v ((q : ℝ) + id (0 : ℝ)) := by simpa using hDF
    simpa only [id_eq,add_zero,one_smul,Function.comp_def] using
      (hDF'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_add (q : ℝ)))
  have hDminus : HasDerivAt (fun t => F ((q : ℝ) - t)) (-v) 0 := by
    have hDF' : HasDerivAt F v ((q : ℝ) - id (0 : ℝ)) := by simpa using hDF
    simpa only [id_eq,sub_zero,neg_smul,one_smul,Function.comp_def] using
      (hDF'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_sub (q : ℝ)))
  have hFnonzero (b : Bool) {t : ℝ} (ht : t ∈ Ioo 0 δ) :
      coordinates g.chart (c (a b t)) - coordinates g.chart (G.edge i q) ≠ 0 := by
    intro heq
    exact hne b ht (coordinates_injOn g.chart (hmem b ⟨ht.1.le,ht.2.le⟩).1
      g.mem_source (sub_eq_zero.mp heq))
  have hFq : F (q : ℝ) = coordinates g.chart (G.edge i q) := by
    simp only [F,IccExtend_of_mem zero_le_one (G.edge i) q.property]
  obtain ⟨α,hα,hαeq⟩ := derivative_points_along_ray
    (fun t => F ((q : ℝ) + t)) v (g.direction (r false)) hDplus hnv
    (g.direction_unit _) δ hδ
    (by intro t ht; simpa only [add_zero,hFq,F,c,a,Bool.false_eq_true,ite_false,ite_true,sub_eq_add_neg] using hFnonzero false ht)
    (by intro t ht; simpa only [add_zero,hFq,F,c,a,Bool.false_eq_true,ite_false,ite_true,sub_eq_add_neg] using hray false t ht)
  obtain ⟨β,hβ,hβeq⟩ := derivative_points_along_ray
    (fun t => F ((q : ℝ) - t)) (-v) (g.direction (r true)) hDminus (neg_ne_zero.mpr hnv)
    (g.direction_unit _) δ hδ
    (by intro t ht; simpa only [sub_zero,hFq,F,c,a,Bool.false_eq_true,ite_false,ite_true,sub_eq_add_neg,neg_zero,add_zero,
      IccExtend_of_mem zero_le_one (G.edge i) q.property] using hFnonzero true ht)
    (by intro t ht; simpa only [sub_zero,hFq,F,c,a,Bool.false_eq_true,ite_false,ite_true,sub_eq_add_neg,neg_zero,add_zero,
      IccExtend_of_mem zero_le_one (G.edge i) q.property] using hray true t ht)
  have hαβ : α = β := by
    have hA := congrArg norm hαeq
    have hB := congrArg norm hβeq
    rw [norm_smul,g.direction_unit,Real.norm_eq_abs,abs_of_pos hα,mul_one] at hA
    rw [norm_neg,norm_smul,g.direction_unit,Real.norm_eq_abs,abs_of_pos hβ,mul_one] at hB
    exact hA.symm.trans hB
  refine ⟨Equiv.ofBijective r ⟨hrinj,hrsurj⟩,?_⟩
  change g.direction (r true) = -g.direction (r false)
  apply smul_right_injective _ hα.ne'
  change α • g.direction (r true) = α • (-g.direction (r false))
  rw [smul_neg,← hαeq,hαβ,← hβeq]

lemma graphStar_open_edge_rayCount (G : EmbeddedGraph S) (i : Fin G.edgeCount)
    (q : unitInterval) (hq : 0 < (q : ℝ) ∧ (q : ℝ) < 1)
    (g : GraphStar G (G.edge i q)) : g.rayCount = 2 := by
  obtain ⟨r,_⟩ := graphStar_open_edge_two_rays G i q hq g
  simpa only [Fintype.card_bool,Fintype.card_fin] using (Fintype.card_congr r).symm

theorem graphStar_nonvertex_two_rays (G : EmbeddedGraph S) (p : M)
    (hp : p ∈ G.carrier) (hpV : p ∉ range G.vertex) (g : GraphStar G p) :
    ∃ r : Bool ≃ Fin g.rayCount, g.direction (r true) = -g.direction (r false) := by
  rcases hp with hp | hp
  · exact False.elim (hpV hp)
  · obtain ⟨i,q,rfl⟩ := mem_iUnion.mp hp
    have hq : 0 < (q : ℝ) ∧ (q : ℝ) < 1 := by
      have hq' : q ∈ G.edge i ⁻¹' (range G.vertex)ᶜ := hpV
      rwa [EmbeddedGraph.edge_preimage_compl_vertices G i] at hq'
    exact graphStar_open_edge_two_rays G i q hq g
end OpenEdgeStars

namespace StarSectors
open SmoothManifolds.BoundaryData
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
lemma preconnected_of_coordinates (e : ModelChart 2 kind M)
    (U : Set M) (hU : U ⊆ e.source) (hconn : IsPreconnected (coordinates e '' U)) :
    IsPreconnected U := by
  let V : Set e.source := Subtype.val ⁻¹' U
  have he : Topology.IsEmbedding (fun x : e.source => coordinates e x.val) :=
    toPlane.toHomeomorph.isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal.comp
        (Topology.IsEmbedding.subtypeVal.comp e.toHomeomorphSourceTarget.isEmbedding))
  have him : (fun x : e.source => coordinates e x.val) '' V = coordinates e '' U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hU hx⟩, hx, rfl⟩
  have hV : IsPreconnected V := he.isInducing.isPreconnected_image.mp (him ▸ hconn)
  have hval : (Subtype.val : e.source → M) '' V = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hU hx⟩, hx, rfl⟩
  exact hval ▸ hV.image Subtype.val continuous_subtype_val.continuousOn

variable {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
lemma star_direction_of_graph_ray (s : GraphStar G p) (v : Plane) (hv : ‖v‖ = 1)
    (t : ℝ) (ht : 0 < t) (htr : t < s.radius)
    (hz : toPlane.symm (coordinates s.chart p + t • v) ∈ modelSet 2 kind)
    (hG : s.chart.symm ⟨toPlane.symm (coordinates s.chart p + t • v), hz⟩ ∈ G.carrier) :
    ∃ i, s.direction i = v := by
  let z : ModelSpace 2 kind := ⟨toPlane.symm (coordinates s.chart p + t • v), hz⟩
  have hball : toPlane z.val ∈ Metric.ball (coordinates s.chart p) s.radius := by
    simpa only [z, toPlane.apply_symm_apply, Metric.mem_ball, dist_eq_norm,
      add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv, mul_one] using htr
  have hzt : z ∈ s.chart.target := s.ball_in_target z hball
  have hxc : coordinates s.chart (s.chart.symm z) = coordinates s.chart p + t • v := by
    change toPlane (s.chart (s.chart.symm z)).val = _
    rw [s.chart.right_inv hzt]
    exact toPlane.apply_symm_apply _
  have hxball : coordinates s.chart (s.chart.symm z) ∈
      Metric.ball (coordinates s.chart p) s.radius := by
    simpa only [coordinates, s.chart.right_inv hzt] using hball
  rcases (s.graph_eq _ (s.chart.map_target hzt) hxball).mp hG with hp | ⟨i, r, hr, hrr, heq⟩
  · have htv : t • v = 0 := by
      rw [hp] at hxc
      exact add_eq_left.mp hxc.symm
    have hv0 : v ≠ 0 := by intro h; simp [h] at hv
    exact False.elim ((smul_ne_zero ht.ne' hv0) htv)
  · have he : t • v = r • s.direction i := by
      rw [hxc] at heq
      exact add_left_cancel heq
    have hrt : t = r := by
      have hn := congrArg norm he
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hr,
        hv, s.direction_unit, mul_one] using hn
    refine ⟨i, ?_⟩
    rw [← hrt] at he
    exact (smul_right_injective _ ht.ne' he).symm

lemma star_boundary_axis_direction {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hboundary : intrinsicBoundary S ⊆ G.carrier)
    (hp : p ∈ intrinsicBoundary S) (v : Plane) (hv : ‖v‖ = 1) (hv1 : v 1 = 0) :
    ∃ i, s.direction i = v := by
  have hp1 : coordinates s.chart p 1 = 0 := by
    have h := (SmoothManifolds.intrinsicBoundary_iff_chart S s.chart s.chart_mem p s.mem_source).mp hp
    change (s.chart p).val 1 = 0 at h
    exact h
  let t := s.radius / 2
  have ht : 0 < t := half_pos s.radius_pos
  have htr : t < s.radius := half_lt_self s.radius_pos
  have hz1 : (toPlane.symm (coordinates s.chart p + t • v)) 1 = 0 := by
    change coordinates s.chart p 1 + t * v 1 = 0
    rw [hp1, hv1]
    ring
  have hz : toPlane.symm (coordinates s.chart p + t • v) ∈ modelSet 2 .halfSpace := hz1.ge
  apply star_direction_of_graph_ray s v hv t ht htr hz
  let z : ModelSpace 2 .halfSpace := ⟨toPlane.symm (coordinates s.chart p + t • v), hz⟩
  have hball : toPlane z.val ∈ Metric.ball (coordinates s.chart p) s.radius := by
    simpa only [z, toPlane.apply_symm_apply, Metric.mem_ball, dist_eq_norm,
      add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv, mul_one] using htr
  have hzt : z ∈ s.chart.target := s.ball_in_target z hball
  apply hboundary
  apply (SmoothManifolds.intrinsicBoundary_iff_chart S s.chart s.chart_mem _ (s.chart.map_target hzt)).mpr
  rw [s.chart.right_inv hzt]
  exact hz1

lemma two_boundary_star_directions {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hboundary : intrinsicBoundary S ⊆ G.carrier)
    (hp : p ∈ intrinsicBoundary S) (hc : s.rayCount = 2) :
    ∀ i, s.direction i 1 = 0 := by
  let v : Plane := toPlane ![1,0]
  have hv : ‖v‖ = 1 := by
    norm_num [v, toPlane, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hv1 : v 1 = 0 := rfl
  obtain ⟨a, ha⟩ := star_boundary_axis_direction s hboundary hp v hv hv1
  obtain ⟨b, hb⟩ := star_boundary_axis_direction s hboundary hp (-v) (by simpa only [norm_neg] using hv)
    (by simp only [PiLp.neg_apply, hv1, neg_zero])
  have hab : a ≠ b := by
    intro hab
    have heq : v = -v := ha.symm.trans ((congrArg s.direction hab).trans hb)
    have hzero : (1 : ℝ) = -1 := congrArg (fun z : Plane => z 0) heq
    norm_num at hzero
  intro i
  have hi : i = a ∨ i = b := by
    have ha' := a.isLt
    have hb' := b.isLt
    have hi' := i.isLt
    have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rcases (show i.val = a.val ∨ i.val = b.val by omega) with hi | hi
    · exact Or.inl (Fin.ext hi)
    · exact Or.inr (Fin.ext hi)
  rcases hi with rfl | rfl
  · rw [ha]; exact hv1
  · rw [hb]; simp only [PiLp.neg_apply, hv1, neg_zero]

lemma boundary_star_coordinates_complement {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hboundary : intrinsicBoundary S ⊆ G.carrier)
    (hp : p ∈ intrinsicBoundary S) (hc : s.rayCount = 2) :
    coordinates s.chart '' (s.neighborhood \ G.carrier) =
      Metric.ball (coordinates s.chart p) s.radius ∩ {z : Plane | 0 < z 1} := by
  have hp1 : coordinates s.chart p 1 = 0 := by
    exact (SmoothManifolds.intrinsicBoundary_iff_chart S s.chart s.chart_mem p s.mem_source).mp hp
  have hd := two_boundary_star_directions s hboundary hp hc
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨hx.1.2, ?_⟩
    have hxnonneg : 0 ≤ coordinates s.chart x 1 := (s.chart x).property
    apply lt_of_le_of_ne hxnonneg
    intro heq
    apply hx.2
    apply hboundary
    apply (SmoothManifolds.intrinsicBoundary_iff_chart S s.chart s.chart_mem _ hx.1.1).mpr
    exact heq.symm
  · rintro ⟨hzball, hz1⟩
    change 0 < z 1 at hz1
    have hzmodel : toPlane.symm z ∈ modelSet 2 .halfSpace := by
      change 0 ≤ z 1
      exact hz1.le
    let zm : ModelSpace 2 .halfSpace := ⟨toPlane.symm z, hzmodel⟩
    have hzt : zm ∈ s.chart.target := by
      apply s.ball_in_target
      simpa only [zm, toPlane.apply_symm_apply] using hzball
    let x := s.chart.symm zm
    have hxsource : x ∈ s.chart.source := s.chart.map_target hzt
    have hxcoord : coordinates s.chart x = z := by
      change toPlane (s.chart (s.chart.symm zm)).val = z
      rw [s.chart.right_inv hzt]
      exact toPlane.apply_symm_apply z
    have hxball : coordinates s.chart x ∈ Metric.ball (coordinates s.chart p) s.radius :=
      hxcoord.symm ▸ hzball
    refine ⟨x, ⟨⟨hxsource, hxball⟩, ?_⟩, hxcoord⟩
    intro hxG
    rcases (s.graph_eq x hxsource hxball).mp hxG with hxp | ⟨i, t, ht, htr, hcoord⟩
    · have : z 1 = 0 := by rw [← hxcoord, hxp]; exact hp1
      linarith
    · have h1 := congrArg (fun z : Plane => z 1) hcoord
      change coordinates s.chart x 1 = coordinates s.chart p 1 + t * s.direction i 1 at h1
      rw [hxcoord, hp1, hd i] at h1
      linarith

lemma boundary_star_preconnected {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hboundary : intrinsicBoundary S ⊆ G.carrier)
    (hp : p ∈ intrinsicBoundary S) (hc : s.rayCount = 2) :
    IsPreconnected (s.neighborhood \ G.carrier) := by
  apply preconnected_of_coordinates s.chart _ (fun _ hx => hx.1.1)
  rw [boundary_star_coordinates_complement s hboundary hp hc]
  apply Convex.isPreconnected
  exact (convex_ball _ _).inter (convex_halfSpace_gt (EuclideanSpace.proj (1 : Fin 2)).isLinear 0)

lemma boundary_star_component_card {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hboundary : intrinsicBoundary S ⊆ G.carrier)
    (hp : p ∈ intrinsicBoundary S) (hc : s.rayCount = 2) :
    Nat.card (ConnectedComponents (s.neighborhood \ G.carrier : Set M)) = 1 := by
  let := isPreconnected_iff_preconnectedSpace.mp (boundary_star_preconnected s hboundary hp hc)
  have hp1 : coordinates s.chart p 1 = 0 := by
    exact (SmoothManifolds.intrinsicBoundary_iff_chart S s.chart s.chart_mem p s.mem_source).mp hp
  let v : Plane := toPlane ![0,1]
  have hv : ‖v‖ = 1 := by
    norm_num [v, toPlane, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hmem : coordinates s.chart p + (s.radius / 2) • v ∈
      coordinates s.chart '' (s.neighborhood \ G.carrier) := by
    rw [boundary_star_coordinates_complement s hboundary hp hc]
    constructor
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos (half_pos s.radius_pos), hv, mul_one] using
        half_lt_self s.radius_pos
    · change 0 < coordinates s.chart p 1 + (s.radius / 2) * 1
      rw [hp1, zero_add, mul_one]
      exact half_pos s.radius_pos
  obtain ⟨x, hx, _⟩ := hmem
  let : Nonempty (s.neighborhood \ G.carrier : Set M) := ⟨⟨x, hx⟩⟩
  exact Nat.card_unique

lemma component_card_two_of_signs {X : Type u} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (hzero : ∀ x, f x ≠ 0)
    (hpos : IsConnected {x | 0 < f x}) (hneg : IsConnected {x | f x < 0}) :
    Nat.card (ConnectedComponents X) = 2 := by
  let C : Bool → Set X := fun b => if b then {x | 0 < f x} else {x | f x < 0}
  have hclopen : ∀ b, IsClopen (C b) := by
    intro b
    cases b
    · change IsClopen {x | f x < 0}
      refine ⟨?_, isOpen_lt hf continuous_const⟩
      have heq : {x | f x < 0} = {x | f x ≤ 0} := by
        ext x
        exact lt_iff_le_and_ne.trans (and_iff_left (hzero x))
      rw [heq]
      exact isClosed_le hf continuous_const
    · change IsClopen {x | 0 < f x}
      refine ⟨?_, isOpen_lt continuous_const hf⟩
      have heq : {x | 0 < f x} = {x | 0 ≤ f x} := by
        ext x
        exact lt_iff_le_and_ne.trans (and_iff_left (hzero x).symm)
      rw [heq]
      exact isClosed_le continuous_const hf
  have hdis : Pairwise (Function.onFun Disjoint C) := by
    intro a b hab
    cases a <;> cases b <;> simp only [ne_eq, not_true_eq_false] at hab
    · apply disjoint_left.mpr
      intro x hx hy
      change f x < 0 at hx
      change 0 < f x at hy
      exact (lt_asymm hx hy)
    · apply disjoint_left.mpr
      intro x hx hy
      change 0 < f x at hx
      change f x < 0 at hy
      exact (lt_asymm hx hy)
  have hunion : ⋃ b, C b = univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases (hzero x).lt_or_gt with hn | hp
    · exact mem_iUnion.mpr ⟨false, hn⟩
    · exact mem_iUnion.mpr ⟨true, hp⟩
  have hconn : ∀ b, IsConnected (C b) := by
    intro b; cases b; exact hneg; exact hpos
  have he := ConnectedComponents.equivOfIsClopenOfIsConnected hclopen hdis hunion hconn
  rw [Nat.card_congr he]
  simp only [Nat.card_eq_fintype_card, Fintype.card_bool]

def componentsEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := e.continuous.connectedComponentsMap
  invFun := e.symm.continuous.connectedComponentsMap
  left_inv := by
    intro a
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    simp only [Continuous.connectedComponentsMap_mk, e.symm_apply_apply]
  right_inv := by
    intro a
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    simp only [Continuous.connectedComponentsMap_mk, e.apply_symm_apply]

lemma component_card_coordinates (e : ModelChart 2 kind M)
    (U : Set M) (hU : U ⊆ e.source) :
    Nat.card (ConnectedComponents U) = Nat.card (ConnectedComponents (coordinates e '' U)) := by
  have he : Topology.IsEmbedding (fun x : U => coordinates e x.val) :=
    (toPlane.toHomeomorph.isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal.comp
        (Topology.IsEmbedding.subtypeVal.comp e.toHomeomorphSourceTarget.isEmbedding))).comp
      (Topology.IsEmbedding.inclusion hU)
  have him : range (fun x : U => coordinates e x.val) = coordinates e '' U := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  exact Nat.card_congr (componentsEquiv (he.toHomeomorph.trans (Homeomorph.setCongr him)))

def planeNormal (d : Plane) : Plane →L[ℝ] ℝ :=
  d 0 • EuclideanSpace.proj 1 - d 1 • EuclideanSpace.proj 0
lemma planeNormal_apply (d z : Plane) : planeNormal d z = d 0 * z 1 - d 1 * z 0 := rfl
lemma planeNormal_zero_iff (d z : Plane) (hd : d ≠ 0) :
    planeNormal d z = 0 ↔ ∃ t : ℝ, z = t • d := by
  constructor
  · intro h
    change d 0 * z 1 - d 1 * z 0 = 0 at h
    by_cases hd0 : d 0 = 0
    · have hd1 : d 1 ≠ 0 := by
        intro h1
        apply hd
        ext i; fin_cases i <;> assumption
      refine ⟨z 1 / d 1, ?_⟩
      ext i
      fin_cases i
      · change z 0 = (z 1 / d 1) * d 0
        rw [hd0, mul_zero]
        rw [hd0, zero_mul, zero_sub, neg_eq_zero] at h
        exact (mul_eq_zero.mp h).resolve_left hd1
      · change z 1 = (z 1 / d 1) * d 1
        rw [div_mul_cancel₀ _ hd1]
    · refine ⟨z 0 / d 0, ?_⟩
      ext i
      fin_cases i
      · change z 0 = (z 0 / d 0) * d 0
        rw [div_mul_cancel₀ _ hd0]
      · change z 1 = (z 0 / d 0) * d 1
        apply (mul_right_injective₀ hd0)
        field_simp
        nlinarith
  · rintro ⟨t, rfl⟩
    change d 0 * (t * d 1) - d 1 * (t * d 0) = 0
    ring

def planePerp (d : Plane) : Plane := toPlane ![-d 1, d 0]
lemma planePerp_norm (d : Plane) : ‖planePerp d‖ = ‖d‖ := by
  simp only [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  congr 1
  change ‖-d 1‖ ^ 2 + ‖d 0‖ ^ 2 = ‖d 0‖ ^ 2 + ‖d 1‖ ^ 2
  simp only [norm_neg, add_comm]
lemma planeNormal_perp_pos (d : Plane) (hd : ‖d‖ = 1) : 0 < planeNormal d (planePerp d) := by
  have hdz : d ≠ 0 := by intro h; simp [h] at hd
  have hsome : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hdz (by ext i; fin_cases i <;> simp_all)
  change 0 < d 0 * d 0 - d 1 * (-d 1)
  rcases hsome with h0 | h1
  · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (d 1)]
  · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (d 0)]

lemma linear_positive_half_ball_connected (c : Plane) (r : ℝ) (hr : 0 < r)
    (L : Plane →L[ℝ] ℝ) (v : Plane) (hv : ‖v‖ = 1) (hLv : 0 < L v) :
    IsConnected (Metric.ball c r ∩ {z | 0 < L (z - c)}) := by
  have hconv : Convex ℝ (Metric.ball c r ∩ {z | 0 < L (z - c)}) := by
    have heq : {z | 0 < L (z - c)} = {z | L c < L z} := by
      ext z
      simp only [mem_ofPred_eq, map_sub]
      exact sub_pos
    rw [heq]
    exact (convex_ball _ _).inter (convex_halfSpace_gt L.isLinear (L c))
  apply hconv.isConnected
  refine ⟨c + (r / 2) • v, ?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos (half_pos hr), hv, mul_one] using half_lt_self hr
  · change 0 < L (c + (r / 2) • v - c)
    rw [add_sub_cancel_left, map_smul]
    exact mul_pos (half_pos hr) hLv

lemma plane_line_complement_component_card (c : Plane) (r : ℝ) (hr : 0 < r)
    (d : Plane) (hd : ‖d‖ = 1) :
    Nat.card (ConnectedComponents (Metric.ball c r ∩ {z | planeNormal d (z - c) ≠ 0} : Set Plane)) = 2 := by
  let U := Metric.ball c r ∩ {z | planeNormal d (z - c) ≠ 0}
  let f : U → ℝ := fun z => planeNormal d (z.val - c)
  apply component_card_two_of_signs f
  · exact (planeNormal d).continuous.comp (continuous_subtype_val.sub continuous_const)
  · exact fun z => z.property.2
  · have hconn := linear_positive_half_ball_connected c r hr (planeNormal d)
        (planePerp d) ((planePerp_norm d).trans hd) (planeNormal_perp_pos d hd)
    have him : (Subtype.val : U → Plane) '' {z | 0 < f z} =
        Metric.ball c r ∩ {z | 0 < planeNormal d (z - c)} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.property.1, hx⟩
      · rintro ⟨hzball, hzpos⟩
        exact ⟨⟨z, hzball, ne_of_gt hzpos⟩, hzpos, rfl⟩
    refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp (him ▸ hconn.isPreconnected)⟩
    obtain ⟨z, hz⟩ := hconn.nonempty
    rw [← him] at hz
    exact (Set.nonempty_of_mem hz).of_image
  · have hconn := linear_positive_half_ball_connected c r hr (-planeNormal d)
        (-planePerp d) (by simpa only [norm_neg, planePerp_norm] using hd)
        (by simpa only [neg_apply, map_neg, neg_neg] using planeNormal_perp_pos d hd)
    have him : (Subtype.val : U → Plane) '' {z | f z < 0} =
        Metric.ball c r ∩ {z | 0 < (-planeNormal d) (z - c)} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x.property.1, ?_⟩
        change 0 < -(planeNormal d (x.val - c))
        exact neg_pos.mpr hx
      · rintro ⟨hzball, hzpos⟩
        have hzneg : planeNormal d (z - c) < 0 := neg_pos.mp hzpos
        exact ⟨⟨z, hzball, ne_of_lt hzneg⟩, hzneg, rfl⟩
    refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp (him ▸ hconn.isPreconnected)⟩
    obtain ⟨z, hz⟩ := hconn.nonempty
    rw [← him] at hz
    exact (Set.nonempty_of_mem hz).of_image

lemma star_graph_iff_normal_zero (s : GraphStar G p)
    (e : Bool ≃ Fin s.rayCount)
    (hop : s.direction (e true) = -s.direction (e false))
    (x : M) (hx : x ∈ s.neighborhood) :
    x ∈ G.carrier ↔ planeNormal (s.direction (e false))
      (coordinates s.chart x - coordinates s.chart p) = 0 := by
  let d := s.direction (e false)
  have hd : ‖d‖ = 1 := s.direction_unit _
  have hd0 : d ≠ 0 := by intro h; simp [h] at hd
  rw [planeNormal_zero_iff _ _ hd0]
  constructor
  · intro hxG
    rcases (s.graph_eq x hx.1 hx.2).mp hxG with hxp | ⟨i,t,ht,htr,hcoord⟩
    · exact ⟨0, by rw [hxp, sub_self, zero_smul]⟩
    · obtain ⟨b, rfl⟩ := e.surjective i
      cases b
      · exact ⟨t, by rw [hcoord, add_sub_cancel_left]⟩
      · exact ⟨-t, by rw [hcoord, add_sub_cancel_left, hop, smul_neg, neg_smul]⟩
  · rintro ⟨t, ht⟩
    apply (s.graph_eq x hx.1 hx.2).mpr
    have hcoord : coordinates s.chart x = coordinates s.chart p + t • d := by
      rw [← ht]
      abel
    have hnorm : |t| < s.radius := by
      have hball := hx.2
      change ‖coordinates s.chart x - coordinates s.chart p‖ < s.radius at hball
      simpa only [ht, norm_smul, Real.norm_eq_abs, hd, mul_one] using hball
    rcases lt_trichotomy t 0 with hneg | hzero | hpos
    · refine Or.inr ⟨e true, -t, neg_pos.mpr hneg, ?_, ?_⟩
      · rwa [abs_of_neg hneg] at hnorm
      · rw [hop, smul_neg, neg_smul, neg_neg]
        exact hcoord
    · apply Or.inl
      apply s.chart.injOn hx.1 s.mem_source
      apply Subtype.ext
      apply toPlane.injective
      change coordinates s.chart x = coordinates s.chart p
      simpa only [hzero, zero_smul, add_zero] using hcoord
    · refine Or.inr ⟨e false, t, hpos, ?_, hcoord⟩
      rwa [abs_of_pos hpos] at hnorm

lemma star_coordinates_line_complement (s : GraphStar G p)
    (e : Bool ≃ Fin s.rayCount)
    (hop : s.direction (e true) = -s.direction (e false))
    (hmodel : ∀ z ∈ Metric.ball (coordinates s.chart p) s.radius,
      toPlane.symm z ∈ modelSet 2 kind) :
    coordinates s.chart '' (s.neighborhood \ G.carrier) =
      Metric.ball (coordinates s.chart p) s.radius ∩
        {z | planeNormal (s.direction (e false)) (z - coordinates s.chart p) ≠ 0} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx.1.2, fun hz => hx.2 ((star_graph_iff_normal_zero s e hop x hx.1).mpr hz)⟩
  · rintro ⟨hzball, hzG⟩
    let zm : ModelSpace 2 kind := ⟨toPlane.symm z, hmodel z hzball⟩
    have hzt : zm ∈ s.chart.target := by
      apply s.ball_in_target
      simpa only [zm, toPlane.apply_symm_apply] using hzball
    let x := s.chart.symm zm
    have hxsource : x ∈ s.chart.source := s.chart.map_target hzt
    have hxcoord : coordinates s.chart x = z := by
      change toPlane (s.chart (s.chart.symm zm)).val = z
      rw [s.chart.right_inv hzt]
      exact toPlane.apply_symm_apply z
    have hxN : x ∈ s.neighborhood := by
      refine ⟨hxsource, ?_⟩
      change coordinates s.chart x ∈ Metric.ball (coordinates s.chart p) s.radius
      rwa [hxcoord]
    refine ⟨x, ⟨hxN, ?_⟩, hxcoord⟩
    intro hxG
    have hz := (star_graph_iff_normal_zero s e hop x hxN).mp hxG
    rw [hxcoord] at hz
    exact hzG hz

lemma interior_star_component_card_of_ball (s : GraphStar G p)
    (e : Bool ≃ Fin s.rayCount)
    (hop : s.direction (e true) = -s.direction (e false))
    (hmodel : ∀ z ∈ Metric.ball (coordinates s.chart p) s.radius,
      toPlane.symm z ∈ modelSet 2 kind) :
    Nat.card (ConnectedComponents (s.neighborhood \ G.carrier : Set M)) = 2 := by
  rw [component_card_coordinates s.chart _ (fun _ hx => hx.1.1),
    star_coordinates_line_complement s e hop hmodel]
  exact plane_line_complement_component_card _ _ s.radius_pos _ (s.direction_unit _)

lemma star_ball_in_model_of_avoids_boundary (s : GraphStar G p)
    (haway : Disjoint s.neighborhood (intrinsicBoundary S)) :
    ∀ z ∈ Metric.ball (coordinates s.chart p) s.radius,
      toPlane.symm z ∈ modelSet 2 kind := by
  cases kind with
  | euclidean => exact fun _ _ => mem_univ _
  | halfSpace =>
    intro z hzball
    change 0 ≤ z 1
    by_contra hz
    have hzneg : z 1 < 0 := lt_of_not_ge hz
    let c := coordinates s.chart p
    have hc : 0 ≤ c 1 := (s.chart p).property
    let v : Plane := toPlane ![0,1]
    have hv : ‖v‖ = 1 := by
      norm_num [v, toPlane, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    let w := c - c 1 • v
    have hw1 : w 1 = 0 := by change c 1 - c 1 * 1 = 0; ring
    have hwmodel : toPlane.symm w ∈ modelSet 2 .halfSpace := hw1.ge
    have hcball : c 1 < s.radius := by
      have hcoord := PiLp.norm_apply_le (z - c) (1 : Fin 2)
      change |z 1 - c 1| ≤ ‖z - c‖ at hcoord
      rw [abs_of_neg (by linarith : z 1 - c 1 < 0)] at hcoord
      have hlt : ‖z - c‖ < s.radius := hzball
      linarith
    have hwball : w ∈ Metric.ball c s.radius := by
      change ‖w - c‖ < s.radius
      have hdisp : w - c = -(c 1 • v) := by dsimp [w]; abel
      rw [hdisp, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, hv, mul_one]
      exact hcball
    let zm : ModelSpace 2 .halfSpace := ⟨toPlane.symm w, hwmodel⟩
    have hzt : zm ∈ s.chart.target := by
      apply s.ball_in_target
      simpa only [zm, toPlane.apply_symm_apply] using hwball
    let x := s.chart.symm zm
    have hxsource : x ∈ s.chart.source := s.chart.map_target hzt
    have hxcoord : coordinates s.chart x = w := by
      change toPlane (s.chart (s.chart.symm zm)).val = w
      rw [s.chart.right_inv hzt]
      exact toPlane.apply_symm_apply w
    have hxN : x ∈ s.neighborhood := by
      refine ⟨hxsource, ?_⟩
      change coordinates s.chart x ∈ Metric.ball c s.radius
      rwa [hxcoord]
    have hxB : x ∈ intrinsicBoundary S := by
      apply (SmoothManifolds.intrinsicBoundary_iff_chart S s.chart s.chart_mem x hxsource).mpr
      change coordinates s.chart x 1 = 0
      rw [hxcoord, hw1]
    exact Set.disjoint_left.mp haway hxN hxB

lemma interior_star_component_card (s : GraphStar G p)
    (e : Bool ≃ Fin s.rayCount)
    (hop : s.direction (e true) = -s.direction (e false))
    (haway : Disjoint s.neighborhood (intrinsicBoundary S)) :
    Nat.card (ConnectedComponents (s.neighborhood \ G.carrier : Set M)) = 2 :=
  interior_star_component_card_of_ball s e hop (star_ball_in_model_of_avoids_boundary s haway)


lemma interior_incident_pair_of_sector_equiv (D : RegionDecomposition S) (p : M)
    (s : GraphStar D.graph p) (e : Bool ≃ Fin s.rayCount)
    (hop : s.direction (e true) = -s.direction (e false))
    (haway : Disjoint s.neighborhood (intrinsicBoundary S))
    (E : {j : Fin D.regionCount // p ∈ closure (componentSet D.graph.carrierᶜ (D.component j))} ≃
      ConnectedComponents (s.neighborhood \ D.graph.carrier : Set M)) :
    ∃ j k : Fin D.regionCount, j ≠ k ∧
      {j | p ∈ closure (componentSet D.graph.carrierᶜ (D.component j))} = {j,k} := by
  apply Set.ncard_eq_two.mp
  change Nat.card {j : Fin D.regionCount //
    p ∈ closure (componentSet D.graph.carrierᶜ (D.component j))} = 2
  exact (Nat.card_congr E).trans (interior_star_component_card s e hop haway)

lemma boundary_incident_singleton_of_sector_equiv {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M}
    (D : RegionDecomposition S) (p : M) (s : GraphStar D.graph p)
    (hp : p ∈ intrinsicBoundary S) (hc : s.rayCount = 2)
    (E : {j : Fin D.regionCount // p ∈ closure (componentSet D.graph.carrierᶜ (D.component j))} ≃
      ConnectedComponents (s.neighborhood \ D.graph.carrier : Set M)) :
    ∃ j : Fin D.regionCount,
      {j | p ∈ closure (componentSet D.graph.carrierᶜ (D.component j))} = {j} := by
  apply Set.ncard_eq_one.mp
  change Nat.card {j : Fin D.regionCount //
    p ∈ closure (componentSet D.graph.carrierᶜ (D.component j))} = 1
  exact (Nat.card_congr E).trans (boundary_star_component_card s D.contains_boundary hp hc)
end StarSectors

/-! Literal compact-arc transitions and exact support partitions. -/
namespace ArcTransitions
/-- The compact full arc supplies continuity of its inverse off endpoint images.
No smoothness or ambient manifold hypothesis occurs here. -/
theorem compact_arc_neighborhood {X : Type*} [TopologicalSpace X] [T2Space X]
    {d : ℝ → X} {a b t : ℝ} (hd : ContinuousOn d (Icc a b))
    (hinj : InjOn d (Ioo a b)) (ht : t ∈ Ioo a b)
    (hleft : d t ≠ d a) (hright : d t ≠ d b)
    {J : Set ℝ} (hJ : IsOpen J) (htJ : t ∈ J) :
    ∃ U : Set X, IsOpen U ∧ d t ∈ U ∧
      d '' Icc a b ∩ U ⊆ d '' (J ∩ Ioo a b) := by
  let K := Icc a b \ (J ∩ Ioo a b)
  have hK : IsClosed (d '' K) :=
    ((isCompact_Icc.diff (hJ.inter isOpen_Ioo)).image_of_continuousOn
      (hd.mono diff_subset)).isClosed
  refine ⟨(d '' K)ᶜ, hK.isOpen_compl, ?_, ?_⟩
  · rintro ⟨s, hs, hst⟩
    have hsa : s ≠ a := fun he => hleft (hst.symm.trans (congrArg d he))
    have hsb : s ≠ b := fun he => hright (hst.symm.trans (congrArg d he))
    have hsopen : s ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hs.1.1 hsa.symm, lt_of_le_of_ne hs.1.2 hsb⟩
    exact hs.2 (hinj hsopen ht hst ▸ ⟨htJ, ht⟩)
  · rintro p ⟨⟨s, hs, rfl⟩, hp⟩
    by_cases hsJ : s ∈ J ∩ Ioo a b
    · exact ⟨s, hsJ, rfl⟩
    · exact (hp ⟨s, ⟨hs, hsJ⟩, rfl⟩).elim

/-- A fixed inverse parameter is continuous wherever a continuous source arc
maps locally into the target open arc, away from target endpoint images. -/
theorem invFunOn_arc_continuousAt {X : Type*} [TopologicalSpace X] [T2Space X]
    {c d : ℝ → X} {a b s t : ℝ} (hd : ContinuousOn d (Icc a b))
    (hinj : InjOn d (Ioo a b)) (ht : t ∈ Ioo a b)
    (hleft : d t ≠ d a) (hright : d t ≠ d b)
    (hc : ContinuousAt c s) (heq : c s = d t)
    (hmaps : ∀ᶠ x in 𝓝 s, c x ∈ d '' Ioo a b) :
    ContinuousAt (fun x => Function.invFunOn d (Ioo a b) (c x)) s := by
  let φ := fun x => Function.invFunOn d (Ioo a b) (c x)
  have hφs : φ s = t := by
    dsimp [φ]
    rw [heq]
    exact hinj.leftInvOn_invFunOn ht
  change ContinuousAt φ s
  rw [ContinuousAt, hφs]
  apply tendsto_def.mpr
  intro V hV
  obtain ⟨J, hJV, hJ, htJ⟩ := mem_nhds_iff.mp hV
  obtain ⟨U, hU, htU, hsub⟩ := compact_arc_neighborhood hd hinj ht hleft hright hJ htJ
  have hcs : c s ∈ U := heq.symm ▸ htU
  filter_upwards [hc.eventually (hU.mem_nhds hcs), hmaps] with x hxU hxmap
  obtain ⟨y, hy, hyEq⟩ := hsub ⟨image_mono Ioo_subset_Icc_self hxmap, hxU⟩
  have hφx : φ x = y := by
    dsimp [φ]
    rw [← hyEq]
    exact hinj.leftInvOn_invFunOn hy.2
  exact hJV (hφx.symm ▸ hy.1)

/-- Equal cut-free traces admit one fixed continuous bijective inverse
transition, directly on their actual parameter intervals. -/
theorem equal_open_trace_inverse {X : Type*} [TopologicalSpace X] [T2Space X]
    {c d : ℝ → X} {l r a b : ℝ}
    (hc : ContinuousOn c (Icc l r)) (hd : ContinuousOn d (Icc a b))
    (hic : InjOn c (Ioo l r)) (hid : InjOn d (Ioo a b))
    (heq : c '' Ioo l r = d '' Ioo a b)
    (hleft : d a ∉ c '' Ioo l r) (hright : d b ∉ c '' Ioo l r) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Ioo l r) ∧ InjOn φ (Ioo l r) ∧
      φ '' Ioo l r = Ioo a b ∧
      ∀ x ∈ Ioo l r, d (φ x) = c x := by
  let φ := fun x => Function.invFunOn d (Ioo a b) (c x)
  have hφ : ∀ x ∈ Ioo l r, φ x ∈ Ioo a b ∧ d (φ x) = c x := by
    intro x hx
    obtain ⟨y, hy, hyEq⟩ := heq.subset ⟨x, hx, rfl⟩
    have hφx : φ x = y := by
      dsimp [φ]
      rw [← hyEq]
      exact hid.leftInvOn_invFunOn hy
    exact ⟨hφx.symm ▸ hy, by rw [hφx]; exact hyEq⟩
  refine ⟨φ, ?_, ?_, ?_, fun x hx => (hφ x hx).2⟩
  · intro x hx
    apply ContinuousAt.continuousWithinAt
    exact invFunOn_arc_continuousAt hd hid (hφ x hx).1
      (fun he => hleft ⟨x, hx, (hφ x hx).2.symm.trans he⟩)
      (fun he => hright ⟨x, hx, (hφ x hx).2.symm.trans he⟩)
      ((hc x (Ioo_subset_Icc_self hx)).continuousAt (Icc_mem_nhds hx.1 hx.2))
      (hφ x hx).2.symm
      (eventually_of_mem (Ioo_mem_nhds hx.1 hx.2)
        (fun y hy => heq.subset ⟨y, hy, rfl⟩))
  · intro x hx y hy hxy
    apply hic hx hy
    rw [← (hφ x hx).2, ← (hφ y hy).2, hxy]
  · apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact (hφ x hx).1
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := heq.symm.subset ⟨y, hy, rfl⟩
      exact ⟨x, hx, hid (hφ x hx).1 hy ((hφ x hx).2.trans hxy)⟩

/-- Surjectivity on the open parameter interval determines surjectivity of
every continuous closed extension. -/
theorem closed_transition_image {φ : ℝ → ℝ} {l r a b : ℝ}
    (hab : a < b) (hφ : ContinuousOn φ (Icc l r))
    (hmap : MapsTo φ (Icc l r) (Icc a b))
    (hopen : φ '' Ioo l r = Ioo a b) :
    φ '' Icc l r = Icc a b := by
  apply Subset.antisymm
  · exact hmap.image_subset
  · have hclosed : IsClosed (φ '' Icc l r) :=
      (isCompact_Icc.image_of_continuousOn hφ).isClosed
    have hsub : Ioo a b ⊆ φ '' Icc l r := by
      rw [← hopen]
      exact image_mono Ioo_subset_Icc_self
    simpa only [closure_Ioo hab.ne] using hclosed.closure_subset_iff.mpr hsub

/-- One-dimensional invariance of domain in the exact form used for gap
traces in the original open graph edges. -/
theorem continuousOn_injective_image_Ioo_isOpen {φ : ℝ → ℝ} {l r : ℝ}
    (hc : ContinuousOn φ (Ioo l r)) (hi : InjOn φ (Ioo l r)) :
    IsOpen (φ '' Ioo l r) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  let a := (l + x) / 2
  let b := (x + r) / 2
  have hla : l < a := by dsimp [a]; linarith [hx.1]
  have hax : a < x := by dsimp [a]; linarith [hx.1]
  have hxb : x < b := by dsimp [b]; linarith [hx.2]
  have hbr : b < r := by dsimp [b]; linarith [hx.2]
  have hab : a < b := hax.trans hxb
  have hsub : Icc a b ⊆ Ioo l r := by
    intro z hz
    exact ⟨hla.trans_le hz.1, hz.2.trans_lt hbr⟩
  have ha : a ∈ Ioo l r := hsub (left_mem_Icc.mpr hab.le)
  have hb : b ∈ Ioo l r := hsub (right_mem_Icc.mpr hab.le)
  rcases hc.strictMonoOn_of_injOn_Ioo (hx.1.trans hx.2) hi with hm | hm
  · have hEq := (hc.mono hsub).image_Ioo_of_strictMonoOn hab.le (hm.mono hsub)
    refine mem_nhds_iff.mpr ⟨Ioo (φ a) (φ b), ?_, isOpen_Ioo, ?_⟩
    · rw [← hEq]
      exact image_mono (Ioo_subset_Icc_self.trans hsub)
    · exact ⟨hm ha hx hax, hm hx hb hxb⟩
  · have hEq := (hc.mono hsub).image_Ioo_of_strictAntiOn hab.le (hm.mono hsub)
    refine mem_nhds_iff.mpr ⟨Ioo (φ b) (φ a), ?_, isOpen_Ioo, ?_⟩
    · rw [← hEq]
      exact image_mono (Ioo_subset_Icc_self.trans hsub)
    · exact ⟨hm hx hb hxb, hm ha hx hax⟩


open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData
open P202.MetricData P202.SurfaceBoundaryData
open P202.GlobalGaussBonnet

/-- Full original-parameter transition on two equal finite gap traces.
Only continuity and open injectivity are used before the existing actual
regular-arc chain-rule lemma supplies a nonzero derivative. -/
theorem regularArc_equal_trace_transition
    {kind : ModelKind} {M : Type*} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {g : RiemannianMetric S}
    (c d : RegularArc g) {l r a b : ℝ} (hlr : l < r) (hab : a < b)
    (hcsub : Icc l r ⊆ Icc c.left c.right)
    (hdsub : Icc a b ⊆ Icc d.left d.right)
    (hic : InjOn c.curve (Ioo c.left c.right))
    (hid : InjOn d.curve (Ioo d.left d.right))
    (heq : c.curve '' Ioo l r = d.curve '' Ioo a b)
    (hleft : d.curve a ∉ c.curve '' Ioo l r)
    (hright : d.curve b ∉ c.curve '' Ioo l r) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc l r) ∧
      (StrictMonoOn φ (Icc l r) ∨ StrictAntiOn φ (Icc l r)) ∧
      φ '' Ioo l r = Ioo a b ∧ φ '' Icc l r = Icc a b ∧
      (∀ x ∈ Icc l r, c.curve x = d.curve (φ x)) ∧
      (∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x) ∧
      ((∀ x ∈ Ioo l r, 0 < deriv φ x) ∨
        (∀ x ∈ Ioo l r, deriv φ x < 0)) := by
  letI : T2Space M := S.topologicalManifold.hausdorff
  have hcopen : Ioo l r ⊆ Ioo c.left c.right := by
    intro x hx
    exact ⟨(hcsub (left_mem_Icc.mpr hlr.le)).1.trans_lt hx.1,
      hx.2.trans_le (hcsub (right_mem_Icc.mpr hlr.le)).2⟩
  have hdopen : Ioo a b ⊆ Ioo d.left d.right := by
    intro x hx
    exact ⟨(hdsub (left_mem_Icc.mpr hab.le)).1.trans_lt hx.1,
      hx.2.trans_le (hdsub (right_mem_Icc.mpr hab.le)).2⟩
  obtain ⟨ψ, hcψ, hiψ, himgψ, heqψ⟩ := equal_open_trace_inverse
    (c.continuous.mono hcsub) (d.continuous.mono hdsub)
    (hic.mono hcopen) (hid.mono hdopen) heq hleft hright
  have hmapψ : MapsTo ψ (Ioo l r) (Ioo a b) := by
    intro x hx
    rw [← himgψ]
    exact mem_image_of_mem ψ hx
  have hderψ : ∀ x ∈ Ioo l r,
      HasDerivAt ψ (deriv ψ x) x ∧ deriv ψ x ≠ 0 := by
    intro x hx
    have hcψx : ContinuousAt ψ x :=
      (hcψ x hx).continuousAt (isOpen_Ioo.mem_nhds hx)
    have heqgerm : ∀ᶠ y in 𝓝 x, d.curve (ψ y) = c.curve y :=
      eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) (fun y hy => heqψ y hy)
    obtain ⟨k, hk, hψd⟩ := regularArc_transition_hasDerivAt c d ψ x
      (hcopen hx) (hdopen (hmapψ hx)) hcψx heqgerm
    exact ⟨hψd.deriv ▸ hψd, hψd.deriv.symm ▸ hk⟩
  obtain ⟨φ, hcφ, hext, hmapφ, hderφ, hsign⟩ :=
    bounded_interval_transition_extension hlr hcψ hiψ
      (fun x hx => (hderψ x hx).1.differentiableAt)
      (fun x hx => (hderψ x hx).2)
      (fun x hx => Ioo_subset_Icc_self (hmapψ hx))
  have himgφ : φ '' Ioo l r = Ioo a b := by
    rw [← himgψ]
    apply image_congr
    intro x hx
    exact hext hx
  have hclosed : EqOn (fun x => d.curve (φ x)) c.curve (Icc l r) := by
    have hopen : EqOn (fun x => d.curve (φ x)) c.curve (Ioo l r) := by
      intro x hx
      change d.curve (φ x) = c.curve x
      rw [hext hx]
      exact heqψ x hx
    exact Set.EqOn.of_subset_closure hopen
      ((d.continuous.mono hdsub).comp hcφ hmapφ)
      (c.continuous.mono hcsub) Ioo_subset_Icc_self
      (by rw [closure_Ioo hlr.ne])
  have hder : ∀ x ∈ Ioo l r, deriv φ x = deriv ψ x :=
    fun x hx => (hderφ x hx).deriv
  refine ⟨φ, hcφ, ?_, himgφ, closed_transition_image hab hcφ hmapφ himgφ,
    fun x hx => (hclosed hx).symm, ?_, ?_⟩
  · exact hsign.imp And.left And.left
  · intro x hx
    exact hder x hx ▸ hderφ x hx
  · rcases hsign with ⟨_, hs⟩ | ⟨_, hs⟩
    · exact Or.inl (fun x hx => (hder x hx).symm ▸ hs x hx)
    · exact Or.inr (fun x hx => (hder x hx).symm ▸ hs x hx)
end ArcTransitions

namespace TracePartitions
open ArcTransitions
theorem unitInterval_open_embedding {X : Type*} [TopologicalSpace X]
    {f : unitInterval → X}
    (hf : IsEmbedding (fun t : {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} =>
      f t.val)) :
    IsEmbedding (fun t : Ioo (0 : ℝ) 1 => f ⟨t.val, t.property.1.le, t.property.2.le⟩) := by
  let k : Ioo (0 : ℝ) 1 → {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} :=
    fun t => ⟨⟨t.val, t.property.1.le, t.property.2.le⟩, t.property⟩
  have hk : IsEmbedding k := by
    have hval : IsEmbedding
        (fun t : {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} => (t.val : ℝ)) :=
      IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
    apply hval.of_comp_iff.mp
    exact IsEmbedding.subtypeVal
  exact hf.comp hk

/-- The parameter support of an embedded interval arc is an open connected
set in every other embedded real interval containing its literal trace. -/
theorem embedded_interval_arc_support
    {X : Type*} [TopologicalSpace X]
    {v w l r : ℝ} (hvw : v < w)
    (e : Ioo v w → X) (he : IsEmbedding e)
    (c : ℝ → X) (hc : ContinuousOn c (Icc l r))
    (hi : InjOn c (Ioo l r)) (hsub : c '' Ioo l r ⊆ range e) :
    IsOpen (e ⁻¹' (c '' Ioo l r)) ∧ IsPreconnected (e ⁻¹' (c '' Ioo l r)) := by
  letI : Nonempty (Ioo v w) := nonempty_Ioo_subtype hvw
  let ψ : Ioo l r → Ioo v w := fun x => Function.invFun e (c x)
  let φ : ℝ → ℝ := fun x => (Function.invFun e (c x)).val
  have hspec : ∀ x ∈ Ioo l r, e (Function.invFun e (c x)) = c x := by
    intro x hx
    exact Function.invFun_eq (hsub ⟨x, hx, rfl⟩)
  have hcψ : Continuous ψ := by
    apply he.continuous_iff.mpr
    have heq : e ∘ ψ = fun x : Ioo l r => c x := by
      funext x
      exact hspec x x.property
    rw [heq]
    exact (hc.mono Ioo_subset_Icc_self).domRestrict
  have hcφ : ContinuousOn φ (Ioo l r) :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hcψ)
  have hiφ : InjOn φ (Ioo l r) := by
    intro x hx y hy hxy
    apply hi hx hy
    rw [← hspec x hx, ← hspec y hy]
    exact congrArg e (Subtype.ext hxy)
  have hpre : e ⁻¹' (c '' Ioo l r) =
      Subtype.val ⁻¹' (φ '' Ioo l r) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hinv : Function.invFun e (c x) = y :=
        he.injective ((hspec x hx).trans hxy)
      exact ⟨x, hx, congrArg Subtype.val hinv⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, (hspec x hx).symm.trans (congrArg e (Subtype.ext hxy))⟩
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact (continuousOn_injective_image_Ioo_isOpen hcφ hiφ).preimage continuous_subtype_val
  · apply he.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_of_subset hsub]
    exact isPreconnected_Ioo.image c (hc.mono Ioo_subset_Icc_self)

/-- A compact gap can only end in the forbidden set, so two cut-free gap
traces on the same original embedded edge are either equal or disjoint.
Finiteness of the forbidden set is needed for the preceding construction,
not for this geometric maximality argument. -/
theorem embedded_interval_gap_traces_eq_of_inter
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {v w l r a b : ℝ} (hvw : v < w)
    (e : Ioo v w → X) (he : IsEmbedding e)
    (c d : ℝ → X)
    (hc : ContinuousOn c (Icc l r)) (hd : ContinuousOn d (Icc a b))
    (hic : InjOn c (Ioo l r)) (hid : InjOn d (Ioo a b))
    (hce : c '' Ioo l r ⊆ range e) (hde : d '' Ioo a b ⊆ range e)
    (H : Set X)
    (hcl : c l ∈ H) (hcr : c r ∈ H)
    (hdl : d a ∈ H) (hdr : d b ∈ H)
    (hcH : Disjoint (c '' Ioo l r) H) (hdH : Disjoint (d '' Ioo a b) H)
    (hinter : (c '' Ioo l r ∩ d '' Ioo a b).Nonempty) :
    c '' Ioo l r = d '' Ioo a b := by
  let U := e ⁻¹' (c '' Ioo l r)
  let V := e ⁻¹' (d '' Ioo a b)
  obtain ⟨hUo, hUc⟩ := embedded_interval_arc_support hvw e he c hc hic hce
  obtain ⟨hVo, hVc⟩ := embedded_interval_arc_support hvw e he d hd hid hde
  have hUV : (U ∩ V).Nonempty := by
    obtain ⟨p, hpc, hpd⟩ := hinter
    obtain ⟨y, rfl⟩ := hce hpc
    exact ⟨y, hpc, hpd⟩
  have hVU : (V ∩ U).Nonempty := by simpa only [inter_comm] using hUV
  have hUcfull : closure U ⊆ e ⁻¹' (c '' Icc l r) := by
    have hclosed : IsClosed (e ⁻¹' (c '' Icc l r)) :=
      ((isCompact_Icc.image_of_continuousOn hc).isClosed).preimage he.continuous
    apply hclosed.closure_subset_iff.mpr
    exact preimage_mono (image_mono Ioo_subset_Icc_self)
  have hVdfull : closure V ⊆ e ⁻¹' (d '' Icc a b) := by
    have hclosed : IsClosed (e ⁻¹' (d '' Icc a b)) :=
      ((isCompact_Icc.image_of_continuousOn hd).isClosed).preimage he.continuous
    apply hclosed.closure_subset_iff.mpr
    exact preimage_mono (image_mono Ioo_subset_Icc_self)
  have hclUV : closure U ∩ V ⊆ U := by
    rintro y ⟨hyU, hyV⟩
    obtain ⟨x, hx, hxy⟩ := hUcfull hyU
    have hxl : x ≠ l := by
      intro hxl
      exact disjoint_left.mp hdH hyV (hxy ▸ hxl.symm ▸ hcl)
    have hxr : x ≠ r := by
      intro hxr
      exact disjoint_left.mp hdH hyV (hxy ▸ hxr.symm ▸ hcr)
    exact ⟨x, ⟨lt_of_le_of_ne hx.1 hxl.symm, lt_of_le_of_ne hx.2 hxr⟩, hxy⟩
  have hclVU : closure V ∩ U ⊆ V := by
    rintro y ⟨hyV, hyU⟩
    obtain ⟨x, hx, hxy⟩ := hVdfull hyV
    have hxa : x ≠ a := by
      intro hxa
      exact disjoint_left.mp hcH hyU (hxy ▸ hxa.symm ▸ hdl)
    have hxb : x ≠ b := by
      intro hxb
      exact disjoint_left.mp hcH hyU (hxy ▸ hxb.symm ▸ hdr)
    exact ⟨x, ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩, hxy⟩
  have hVsub : V ⊆ U := hVc.subset_of_closure_inter_subset hUo hVU hclUV
  have hUsub : U ⊆ V := hUc.subset_of_closure_inter_subset hVo hUV hclVU
  have hUVeq : U = V := Subset.antisymm hUsub hVsub
  have := congrArg (fun Q => e '' Q) hUVeq
  simpa only [U, V, image_preimage_eq_of_subset hce,
    image_preimage_eq_of_subset hde] using this
end TracePartitions

namespace TracePairing
variable {X ι : Type*}
/-- A family whose supports coincide or are disjoint and have pointwise
multiplicity two has one and only one other occurrence of each support. -/
theorem unique_other_equal_trace (T : ι → Set X)
    (hne : ∀ i, (T i).Nonempty)
    (hcard : ∀ p ∈ ⋃ i, T i, Nat.card {i // p ∈ T i} = 2)
    (heq : ∀ i j, (T i ∩ T j).Nonempty → T i = T j)
    (i : ι) : ∃! j, j ≠ i ∧ T j = T i := by
  obtain ⟨p, hp⟩ := hne i
  let S := {j // p ∈ T j}
  let a : S := ⟨i, hp⟩
  obtain ⟨b, hba, huniq⟩ := (Nat.card_eq_two_iff' a).mp
    (hcard p (mem_iUnion.mpr ⟨i, hp⟩))
  have hbi : b.val ≠ i := fun h => hba (Subtype.ext h)
  refine ⟨b.val, ⟨hbi, heq b.val i ⟨p, b.property, hp⟩⟩, ?_⟩
  intro j hj
  have hpj : p ∈ T j := hj.2.symm ▸ hp
  have hja : (⟨j, hpj⟩ : S) ≠ a := fun h => hj.1 (congrArg Subtype.val h)
  exact congrArg Subtype.val (huniq ⟨j, hpj⟩ hja)

/-- The unique other equal support gives a fixed-point-free mate involution. -/
theorem exists_trace_mate (T : ι → Set X)
    (hne : ∀ i, (T i).Nonempty)
    (hcard : ∀ p ∈ ⋃ i, T i, Nat.card {i // p ∈ T i} = 2)
    (heq : ∀ i j, (T i ∩ T j).Nonempty → T i = T j) :
    ∃ mate : ι → ι, Function.Involutive mate ∧
      (∀ i, mate i ≠ i) ∧ (∀ i, T (mate i) = T i) := by
  have hu := unique_other_equal_trace T hne hcard heq
  let mate := fun i => (hu i).choose
  have hm (i : ι) : mate i ≠ i ∧ T (mate i) = T i := (hu i).choose_spec.1
  refine ⟨mate, ?_, fun i => (hm i).1, fun i => (hm i).2⟩
  intro i
  exact ((hu (mate i)).choose_spec.2 i ⟨(hm i).1.symm, (hm i).2.symm⟩).symm
end TracePairing


open P202Specs.SurfaceRegionsEuler P202.SurfaceBoundaryData
open SmoothManifolds.BoundaryData
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Finite graph stars have dense complement, including on the boundary face. -/
theorem regionDecomposition_graph_compl_dense (D : RegionDecomposition S) :
    Dense D.graph.carrierᶜ := by
  apply dense_iff_inter_open.mpr
  intro O hO hne
  by_contra h
  have hsub : O ⊆ D.graph.carrier := by
    intro x hx
    by_contra hxG
    exact h ⟨x, hx, hxG⟩
  obtain ⟨p, hp⟩ := hne
  obtain ⟨s, hs, _⟩ := D.sectors p (hsub hp) O hO hp
  let W : Set (ModelSpace 2 kind) := s.chart.target ∩ s.chart.symm ⁻¹' s.neighborhood
  have hW : IsOpen W := s.chart.symm.isOpen_inter_preimage
    (GraphStar.isOpen_neighborhood s)
  have hWne : W.Nonempty := by
    refine ⟨s.chart p, s.chart.map_source s.mem_source, ?_⟩
    change s.chart.symm (s.chart p) ∈ s.neighborhood
    rw [s.chart.left_inv s.mem_source]
    exact GraphStar.mem_neighborhood s
  have hpos := SmoothManifolds.Sard.model_open_volume_pos hW hWne
  have hz : MeasureTheory.volume (Subtype.val '' W : Set (Euclidean 2)) = 0 := by
    apply MeasureTheory.measure_mono_null _ (graphStar_coordinate_image_null s)
    rintro _ ⟨z, ⟨hzt, hzn⟩, rfl⟩
    refine ⟨s.chart.symm z, ⟨hsub (hs hzn), hzn⟩, ?_⟩
    exact congrArg Subtype.val (s.chart.right_inv hzt)
  rw [hz] at hpos
  exact (lt_irrefl _ hpos)

/-- The closures of the literal complementary components cover the surface. -/
theorem regionClosures_cover (D : RegionDecomposition S) :
    (⋃ j, regionClosure D j) = univ := by
  have he : (⋃ j, regionClosure D j) = closure D.graph.carrierᶜ := by
    rw [← P202.SurfaceRegionsEuler.regionInteriors_cover D,
      closure_iUnion_of_finite]
  rw [he, (regionDecomposition_graph_compl_dense D).closure_eq]

/-- The union of exactly the incident closures is an actual neighborhood. -/
theorem incident_regionClosures_mem_nhds (D : RegionDecomposition S) (p : M) :
    (⋃ j ∈ incidentRegions D p, regionClosure D j) ∈ 𝓝 p := by
  have he := regional_closures_incident_germ D p
  rw [regionClosures_cover D] at he
  filter_upwards [he] with x hx
  exact Eq.mpr hx (mem_univ x)

/-- Exact two-region incidence determines the occupied union germ. -/
theorem two_incident_regionClosures_mem_nhds (D : RegionDecomposition S)
    (p : M) (j k : Fin D.regionCount) (he : incidentRegions D p = {j, k}) :
    regionClosure D j ∪ regionClosure D k ∈ 𝓝 p := by
  have h := incident_regionClosures_mem_nhds D p
  simpa [he] using h

/-- Exact one-region incidence determines the relative surface neighborhood. -/
theorem one_incident_regionClosure_mem_nhds (D : RegionDecomposition S)
    (p : M) (j : Fin D.regionCount) (he : incidentRegions D p = {j}) :
    regionClosure D j ∈ 𝓝 p := by
  have h := incident_regionClosures_mem_nhds D p
  simpa [he] using h

/-- The complete literal Jordan trace is covered by the given presentation,
including every inserted subdivision endpoint. -/
lemma arcPresentation_trace_eq_iUnion {q : RegularJordanCurve}
    (A : P202Specs.PlaneTurning.ArcPresentation q) :
    q.trace = ⋃ k, A.arc k '' Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro z ⟨v, rfl⟩
    obtain ⟨x, hx, hv⟩ := AddCircle.eq_coe_Ico v
    obtain ⟨k, hk0, hk1⟩ := P202.PlaneTangentComparison.presentation_interval A hx.1 hx.2
    have hd : 0 < A.time k.succ - A.time k.castSucc :=
      sub_pos.mpr (A.strictMono k.castSucc_lt_succ)
    let t := (x - A.time k.castSucc) / (A.time k.succ - A.time k.castSucc)
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hk0) hd.le
      · exact (div_le_one hd).mpr (by linarith)
    have he : A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * t = x := by
      dsimp [t]
      field_simp
      <;> ring
    refine mem_iUnion.mpr ⟨k, t, ht, ?_⟩
    rw [A.agrees k t ht, he]
    change q.parametrization (x : ParameterCircle) = q.parametrization v
    rw [hv]
  · rintro z hz
    obtain ⟨k, t, ht, rfl⟩ := mem_iUnion.mp hz
    rw [A.agrees k t ht]
    exact ⟨_, rfl⟩

/-- Every point of an actual regional closure on the graph is represented
by a literal arc of its supplied A-family. -/
theorem incident_region_mem_closed_arc {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (j : Fin D.regionCount) {p : M}
    (hp : p ∈ regionClosure D j) (hG : p ∈ D.graph.carrier) :
    ∃ i k t, t ∈ Icc (0 : ℝ) 1 ∧ (R.arc j i k).curve t = p := by
  have hc : coordinates (D.chart j) p ∈ (D.region j).boundary := by
    rw [region_boundary_eq_coordinates_graph D j]
    exact ⟨p, ⟨hp, hG⟩, rfl⟩
  change coordinates (D.chart j) p ∈ frontier (D.region j).domain at hc
  rw [(D.region j).boundary_eq] at hc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hc
  rw [arcPresentation_trace_eq_iUnion (A j i)] at hi
  obtain ⟨k, t, ht, hcoord⟩ := mem_iUnion.mp hi
  refine ⟨i, k, t, ht, ?_⟩
  apply coordinates_injOn (D.chart j) (R.literal j i k t ht).2.1 (D.closure_in_chart j hp)
  exact (R.literal j i k t ht).2.2.trans hcoord

/-- Off the common forbidden point set, each incident region occurs exactly
once among its genuine original open A-arcs. -/
theorem incident_region_unique_open_arc {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (j : Fin D.regionCount) {p : M}
    (hp : p ∈ regionClosure D j) (hG : p ∈ D.graph.carrier)
    (hF : p ∉ refinementForbiddenPoints R B) :
    ∃! a : Σ i : Fin (D.region j).boundaryCount, Fin (A j i).count,
      p ∈ (R.arc j a.1 a.2).curve '' Ioo (0 : ℝ) 1 := by
  obtain ⟨i, k, t, ht, htp⟩ := incident_region_mem_closed_arc R j hp hG
  have h0 : t ≠ 0 := by
    intro he
    apply hF
    apply Or.inl
    apply Or.inr
    apply Or.inl
    refine ⟨.inl ⟨j, i, k⟩, ?_⟩
    simpa only [occurrenceArc, R.left, ← he] using htp
  have h1 : t ≠ 1 := by
    intro he
    apply hF
    apply Or.inl
    apply Or.inr
    apply Or.inr
    refine ⟨.inl ⟨j, i, k⟩, ?_⟩
    simpa only [occurrenceArc, R.right, ← he] using htp
  have htopen : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 h0.symm, lt_of_le_of_ne ht.2 h1⟩
  refine ⟨⟨i, k⟩, ⟨t, htopen, htp⟩, ?_⟩
  intro a ha
  by_contra hne
  exact Set.disjoint_left.mp (R.disjoint j hne) ha ⟨t, htopen, htp⟩

/-- Off the forbidden points, intrinsic boundary points occur exactly once
in the original B-family. -/
theorem intrinsicBoundary_unique_open_arc {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    {p : M} (hp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (hF : p ∉ refinementForbiddenPoints R B) :
    ∃! b : Fin B.count, p ∈ (B.arc b).curve '' Ioo (B.arc b).left (B.arc b).right := by
  rw [B.covers] at hp
  obtain ⟨b, t, ht, htp⟩ := mem_iUnion.mp hp
  have h0 : t ≠ (B.arc b).left := by
    intro he
    apply hF
    exact Or.inl (Or.inr (Or.inl ⟨.inr b, by simpa only [occurrenceArc, ← he] using htp⟩))
  have h1 : t ≠ (B.arc b).right := by
    intro he
    apply hF
    exact Or.inl (Or.inr (Or.inr ⟨.inr b, by simpa only [occurrenceArc, ← he] using htp⟩))
  have htopen : t ∈ Ioo (B.arc b).left (B.arc b).right :=
    ⟨lt_of_le_of_ne ht.1 h0.symm, lt_of_le_of_ne ht.2 h1⟩
  refine ⟨b, ⟨t, htopen, htp⟩, ?_⟩
  intro a ha
  by_contra hne
  exact Set.disjoint_left.mp (B.disjoint hne) ha ⟨t, htopen, htp⟩

open OpenEdgeStars StarSectors
/-- The two occupied regions at an interior nonvertex point are distinct,
exhaust the actual regional closures incident at that point, and fill its germ. -/
theorem regional_nonvertex_interior_incidence (D : RegionDecomposition S) (p : M)
    (hp : p ∈ D.graph.carrier) (hpV : p ∉ range D.graph.vertex)
    (hpB : p ∉ intrinsicBoundary S) :
    ∃ j k : Fin D.regionCount, j ≠ k ∧ incidentRegions D p = {j,k} ∧
      regionClosure D j ∪ regionClosure D k ∈ 𝓝 p := by
  obtain ⟨s,hs,⟨E⟩⟩ := regional_incidence_equiv_star_components D p hp (intrinsicBoundary S)ᶜ
    (SmoothManifolds.isClosed_intrinsicBoundary S).isOpen_compl hpB
  obtain ⟨e,hop⟩ := graphStar_nonvertex_two_rays D.graph p hp hpV s
  have haway : Disjoint s.neighborhood (intrinsicBoundary S) :=
    Set.disjoint_left.mpr (fun _ hxN hxB => hs hxN hxB)
  obtain ⟨j,k,hjk,he⟩ := interior_incident_pair_of_sector_equiv D p s e hop haway E
  have he' : incidentRegions D p = {j,k} := he
  refine ⟨j,k,hjk,he',?_⟩
  simpa [he'] using incident_regionClosures_mem_nhds D p

/-- At an original boundary nonvertex point exactly one regional closure
occurs, and that closure is a relative original-surface neighborhood. -/
theorem regional_nonvertex_boundary_incidence (D : RegionDecomposition S) (p : M)
    (hp : p ∈ D.graph.carrier) (hpV : p ∉ range D.graph.vertex)
    (hpB : p ∈ intrinsicBoundary S) :
    ∃ j : Fin D.regionCount, incidentRegions D p = {j} ∧ regionClosure D j ∈ 𝓝 p := by
  cases kind with
  | euclidean =>
    exact False.elim (by simpa only [SmoothManifolds.intrinsicBoundary_euclidean,
      Set.mem_empty_iff_false] using hpB)
  | halfSpace =>
    obtain ⟨s,_,⟨E⟩⟩ := regional_incidence_equiv_star_components D p hp univ isOpen_univ (mem_univ p)
    obtain ⟨e,_⟩ := graphStar_nonvertex_two_rays D.graph p hp hpV s
    have hc : s.rayCount = 2 := by
      simpa only [Fintype.card_bool,Fintype.card_fin] using (Fintype.card_congr e).symm
    obtain ⟨j,he⟩ := boundary_incident_singleton_of_sector_equiv D p s hpB hc E
    have he' : incidentRegions D p = {j} := he
    refine ⟨j,he',?_⟩
    simpa [he'] using incident_regionClosures_mem_nhds D p


open ArcTransitions TracePartitions

/-- Every canonical cut is the parameter of one of the common forbidden points. -/
lemma refinementCuts_curve_mem_forbidden {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (o : Occurrence A B) {t : ℝ} (ht : t ∈ refinementCuts R B o) :
    (occurrenceArc R B o).curve t ∈ refinementForbiddenPoints R B := by
  rcases Finset.mem_insert.mp ht with h | ht
  · subst t
    exact Or.inl (Or.inr (Or.inl ⟨o, rfl⟩))
  rcases Finset.mem_insert.mp ht with h | ht
  · subst t
    exact Or.inl (Or.inr (Or.inr ⟨o, rfl⟩))
  exact ((occurrenceArc_cutParameters_finite R B o
    (refinementForbiddenPoints_finite R B)).mem_toFinset.mp ht).2

lemma canonical_piece_left_mem_forbidden {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (h : Fin (finiteSubdivision g D A R B).count) :
    (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve
      ((finiteSubdivision g D A R B).left h) ∈ refinementForbiddenPoints R B :=
  refinementCuts_curve_mem_forbidden R B _ ((finiteSubdivision g D A R B).left_cut h)

lemma canonical_piece_right_mem_forbidden {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (h : Fin (finiteSubdivision g D A R B).count) :
    (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve
      ((finiteSubdivision g D A R B).right h) ∈ refinementForbiddenPoints R B :=
  refinementCuts_curve_mem_forbidden R B _ ((finiteSubdivision g D A R B).right_cut h)

lemma canonical_piece_avoids_forbidden {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (h : Fin (finiteSubdivision g D A R B).count) :
    Disjoint
      ((occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve ''
        Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h))
      (refinementForbiddenPoints R B) := by
  let F := finiteSubdivision g D A R B
  apply disjoint_left.mpr
  rintro p ⟨t, ht, rfl⟩ hp
  exact F.cut_free h t ht (mem_refinementCuts_of_point R B (F.occurrence h)
    (subdivision_piece_bounds F h (Ioo_subset_Icc_self ht)) hp)

/-- Intersecting pieces in the canonical simultaneous partition have
identical original-surface open traces. -/
theorem canonical_piece_traces_eq_of_inter {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (h k : Fin (finiteSubdivision g D A R B).count)
    (hinter :
      ((occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve ''
        Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h) ∩
      (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence k)).curve ''
        Ioo ((finiteSubdivision g D A R B).left k) ((finiteSubdivision g D A R B).right k)).Nonempty) :
    (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve ''
        Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h) =
      (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence k)).curve ''
        Ioo ((finiteSubdivision g D A R B).left k) ((finiteSubdivision g D A R B).right k) := by
  letI : T2Space M := S.topologicalManifold.hausdorff
  let F := finiteSubdivision g D A R B
  let c := occurrenceArc R B (F.occurrence h)
  let d := occurrenceArc R B (F.occurrence k)
  obtain ⟨i, hi⟩ := subdivision_piece_one_openEdge R B F h
  obtain ⟨j, hj⟩ := subdivision_piece_one_openEdge R B F k
  have hij : i = j := by
    by_contra hn
    obtain ⟨p, hp, hq⟩ := hinter
    exact disjoint_left.mp (D.graph.disjoint_open_edges hn) (hi hp) (hj hq)
  subst j
  let e : Ioo (0 : ℝ) 1 → M := fun t => D.graph.edge i
    ⟨t.val, t.property.1.le, t.property.2.le⟩
  have he : IsEmbedding e := unitInterval_open_embedding
    (P202.SurfaceRegionConstruction.EmbeddedGraph.open_edge_embedding D.graph i)
  have hce : c.curve '' Ioo (F.left h) (F.right h) ⊆ range e := by
    intro p hp
    obtain ⟨t, ht, htp⟩ := hi hp
    exact ⟨⟨t.val, ht⟩, htp⟩
  have hde : d.curve '' Ioo (F.left k) (F.right k) ⊆ range e := by
    intro p hp
    obtain ⟨t, ht, htp⟩ := hj hp
    exact ⟨⟨t.val, ht⟩, htp⟩
  have hcop : Ioo (F.left h) (F.right h) ⊆ Ioo c.left c.right := by
    intro t ht
    exact ⟨(subdivision_piece_bounds F h (left_mem_Icc.mpr (F.ordered h).le)).1.trans_lt ht.1,
      ht.2.trans_le (subdivision_piece_bounds F h (right_mem_Icc.mpr (F.ordered h).le)).2⟩
  have hdop : Ioo (F.left k) (F.right k) ⊆ Ioo d.left d.right := by
    intro t ht
    exact ⟨(subdivision_piece_bounds F k (left_mem_Icc.mpr (F.ordered k).le)).1.trans_lt ht.1,
      ht.2.trans_le (subdivision_piece_bounds F k (right_mem_Icc.mpr (F.ordered k).le)).2⟩
  exact embedded_interval_gap_traces_eq_of_inter zero_lt_one e he c.curve d.curve
    (c.continuous.mono (subdivision_piece_bounds F h))
    (d.continuous.mono (subdivision_piece_bounds F k))
    ((occurrenceArc_injective R B (F.occurrence h)).mono hcop)
    ((occurrenceArc_injective R B (F.occurrence k)).mono hdop)
    hce hde (refinementForbiddenPoints R B)
    (canonical_piece_left_mem_forbidden R B h)
    (canonical_piece_right_mem_forbidden R B h)
    (canonical_piece_left_mem_forbidden R B k)
    (canonical_piece_right_mem_forbidden R B k)
    (canonical_piece_avoids_forbidden R B h)
    (canonical_piece_avoids_forbidden R B k) hinter

/-- Equal canonical piece traces have the full required closed transition. -/
theorem canonical_piece_transition {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (h k : Fin (finiteSubdivision g D A R B).count)
    (heq :
      (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve ''
        Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h) =
      (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence k)).curve ''
        Ioo ((finiteSubdivision g D A R B).left k) ((finiteSubdivision g D A R B).right k)) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Icc ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h)) ∧
      (StrictMonoOn φ (Icc ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h)) ∨
        StrictAntiOn φ (Icc ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h))) ∧
      φ '' Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h) =
        Ioo ((finiteSubdivision g D A R B).left k) ((finiteSubdivision g D A R B).right k) ∧
      φ '' Icc ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h) =
        Icc ((finiteSubdivision g D A R B).left k) ((finiteSubdivision g D A R B).right k) ∧
      (∀ x ∈ Icc ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h),
        (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve x =
          (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence k)).curve (φ x)) ∧
      (∀ x ∈ Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h),
        HasDerivAt φ (deriv φ x) x) ∧
      ((∀ x ∈ Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h),
        0 < deriv φ x) ∨
        (∀ x ∈ Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h),
          deriv φ x < 0)) := by
  let F := finiteSubdivision g D A R B
  apply regularArc_equal_trace_transition
    (occurrenceArc R B (F.occurrence h)) (occurrenceArc R B (F.occurrence k))
    (F.ordered h) (F.ordered k) (subdivision_piece_bounds F h) (subdivision_piece_bounds F k)
    (occurrenceArc_injective R B (F.occurrence h))
    (occurrenceArc_injective R B (F.occurrence k)) heq
  · intro hp
    exact disjoint_left.mp (canonical_piece_avoids_forbidden R B h) hp
      (canonical_piece_left_mem_forbidden R B k)
  · intro hp
    exact disjoint_left.mp (canonical_piece_avoids_forbidden R B h) hp
      (canonical_piece_right_mem_forbidden R B k)


variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Forgetting the unique literal regional open arc identifies its pointwise
support with the original regional closures incident at the point. -/
def regionalSupportEquivIncident {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (p : M) (hG : p ∈ D.graph.carrier) (hF : p ∉ refinementForbiddenPoints R B) :
    {a : RegionalIndex D A // p ∈
      (occurrenceArc R B (.inl a)).curve ''
        Ioo (occurrenceArc R B (.inl a)).left (occurrenceArc R B (.inl a)).right} ≃
    {j : Fin D.regionCount // p ∈ regionClosure D j} := by
  let T := {a : RegionalIndex D A // p ∈
      (occurrenceArc R B (.inl a)).curve ''
        Ioo (occurrenceArc R B (.inl a)).left (occurrenceArc R B (.inl a)).right}
  let J := {j : Fin D.regionCount // p ∈ regionClosure D j}
  let f : T → J := fun a => ⟨a.val.1, by
    rcases a with ⟨⟨j,i,k⟩, ha⟩
    obtain ⟨t, ht, htp⟩ := ha
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [occurrenceArc, R.left, R.right] using Ioo_subset_Icc_self ht
    change p ∈ regionClosure D j
    rw [← htp]
    exact (R.literal j i k t ht').1.1⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    have hj := congrArg (fun j : J => j.val) hab
    rcases a with ⟨⟨j,i,k⟩, ha⟩
    rcases b with ⟨⟨j',i',k'⟩, hb⟩
    change j = j' at hj
    subst j'
    have hpj : p ∈ regionClosure D j := (f ⟨⟨j,i,k⟩,ha⟩).property
    obtain ⟨u, hu, huniq⟩ := incident_region_unique_open_arc R B j hpj hG hF
    have ha' : p ∈ (R.arc j i k).curve '' Ioo (0 : ℝ) 1 := by
      simpa only [occurrenceArc, R.left, R.right] using ha
    have hb' : p ∈ (R.arc j i' k').curve '' Ioo (0 : ℝ) 1 := by
      simpa only [occurrenceArc, R.left, R.right] using hb
    have hab' : (⟨i,k⟩ : Σ i : Fin (D.region j).boundaryCount, Fin (A j i).count) = ⟨i',k'⟩ :=
      (huniq _ ha').trans (huniq _ hb').symm
    exact congrArg (Sigma.mk j) hab'
  · intro j
    obtain ⟨⟨i,k⟩, hmem, huniq⟩ := incident_region_unique_open_arc R B j.val j.property hG hF
    let a : T := ⟨⟨j.val,i,k⟩, by
      simpa only [occurrenceArc, R.left, R.right] using hmem⟩
    exact ⟨a, Subtype.ext rfl⟩

/-- The number of original open occurrence traces through a non-forbidden graph
point is the regional incidence count plus the original boundary-arc count. -/
theorem occurrence_support_card_eq {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (p : M) (hG : p ∈ D.graph.carrier) (hF : p ∉ refinementForbiddenPoints R B) :
    Nat.card {o : Occurrence A B // p ∈ (occurrenceArc R B o).curve ''
      Ioo (occurrenceArc R B o).left (occurrenceArc R B o).right} =
    Nat.card {j : Fin D.regionCount // p ∈ regionClosure D j} +
      Nat.card {b : Fin B.count // p ∈ (B.arc b).curve '' Ioo (B.arc b).left (B.arc b).right} := by
  rw [Nat.card_congr (Equiv.subtypeSum (p := fun o : Occurrence A B =>
    p ∈ (occurrenceArc R B o).curve ''
      Ioo (occurrenceArc R B o).left (occurrenceArc R B o).right)), Nat.card_sum]
  rw [Nat.card_congr (regionalSupportEquivIncident R B p hG hF)]
  rfl

/-- Original boundary open arcs do not occur at an intrinsic interior point. -/
theorem boundary_support_card_zero {g : RiemannianMetric S}
    (B : BoundaryPresentation g) (p : M) (hp : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S) :
    Nat.card {b : Fin B.count // p ∈
      (B.arc b).curve '' Ioo (B.arc b).left (B.arc b).right} = 0 := by
  let : IsEmpty {b : Fin B.count // p ∈
      (B.arc b).curve '' Ioo (B.arc b).left (B.arc b).right} := ⟨by
    rintro ⟨b,t,ht,htp⟩
    apply hp
    rw [B.covers]
    exact mem_iUnion.mpr ⟨b,t,Ioo_subset_Icc_self ht,htp⟩⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- Off the common endpoint cuts an intrinsic boundary point lies on one
and only one original open B-arc. -/
theorem boundary_support_card_one {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (p : M) (hp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (hF : p ∉ refinementForbiddenPoints R B) :
    Nat.card {b : Fin B.count // p ∈
      (B.arc b).curve '' Ioo (B.arc b).left (B.arc b).right} = 1 := by
  obtain ⟨b,hb,huniq⟩ := intrinsicBoundary_unique_open_arc R B hp hF
  let : Nonempty {b : Fin B.count // p ∈
      (B.arc b).curve '' Ioo (B.arc b).left (B.arc b).right} := ⟨⟨b,hb⟩⟩
  let : Subsingleton {b : Fin B.count // p ∈
      (B.arc b).curve '' Ioo (B.arc b).left (B.arc b).right} := ⟨by
    intro a c
    exact Subtype.ext ((huniq a.val a.property).trans (huniq c.val c.property).symm)⟩
  exact Nat.card_unique

/-- Regional incidence two in the interior, or one at the boundary, gives
pointwise multiplicity two among the literal original occurrences. -/
theorem occurrence_support_card_two_of_incidence {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (p : M) (hG : p ∈ D.graph.carrier) (hF : p ∉ refinementForbiddenPoints R B)
    (hinterior : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S →
      Nat.card {j : Fin D.regionCount // p ∈ regionClosure D j} = 2)
    (hboundary : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S →
      Nat.card {j : Fin D.regionCount // p ∈ regionClosure D j} = 1) :
    Nat.card {o : Occurrence A B // p ∈ (occurrenceArc R B o).curve ''
      Ioo (occurrenceArc R B o).left (occurrenceArc R B o).right} = 2 := by
  rw [occurrence_support_card_eq R B p hG hF]
  by_cases hp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S
  · rw [hboundary hp, boundary_support_card_one R B p hp hF]
  · rw [hinterior hp, boundary_support_card_zero B p hp]


/-- Exactly two original open occurrences pass through every graph point
away from the common finite geometric cuts. -/
theorem occurrence_support_card_two {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (p : M) (hG : p ∈ D.graph.carrier) (hF : p ∉ refinementForbiddenPoints R B) :
    Nat.card {o : Occurrence A B // p ∈ (occurrenceArc R B o).curve ''
      Ioo (occurrenceArc R B o).left (occurrenceArc R B o).right} = 2 := by
  have hpV : p ∉ range D.graph.vertex := fun hpV => hF (Or.inl (Or.inl hpV))
  apply occurrence_support_card_two_of_incidence R B p hG hF
  · intro hpB
    obtain ⟨j,k,hjk,he,_⟩ := regional_nonvertex_interior_incidence D p hG hpV hpB
    change (incidentRegions D p).ncard = 2
    rw [he, Set.ncard_pair hjk]
  · intro hpB
    obtain ⟨j,he,_⟩ := regional_nonvertex_boundary_incidence D p hG hpV hpB
    change (incidentRegions D p).ncard = 1
    rw [he, Set.ncard_singleton]

/-- Subdivision pieces preserve pointwise multiplicity away from the cut images.
The equivalence sends a piece to its literal original occurrence. -/
def subdivisionPointSupportEquiv {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : P202Specs.GlobalGaussBonnet.BoundaryPresentation g)
    (F : FiniteSubdivision R B) (Z : Set M)
    (hcut : ∀ o t, t ∈ F.cuts o → (occurrenceArc R B o).curve t ∈ Z)
    (p : M) (hp : p ∉ Z) :
    {h : Fin F.count // p ∈ (occurrenceArc R B (F.occurrence h)).curve '' Ioo (F.left h) (F.right h)} ≃
      {o : Occurrence A B // p ∈ (occurrenceArc R B o).curve ''
        Ioo (occurrenceArc R B o).left (occurrenceArc R B o).right} := by
  have hsub (h : Fin F.count) : Ioo (F.left h) (F.right h) ⊆
      Ioo (occurrenceArc R B (F.occurrence h)).left
        (occurrenceArc R B (F.occurrence h)).right := by
    intro t ht
    exact ⟨(F.cuts_bounds _ (F.left_cut h)).1.trans_lt ht.1,
      ht.2.trans_le (F.cuts_bounds _ (F.right_cut h)).2⟩
  let f : {h : Fin F.count // p ∈ (occurrenceArc R B (F.occurrence h)).curve '' Ioo (F.left h) (F.right h)} →
      {o : Occurrence A B // p ∈ (occurrenceArc R B o).curve ''
        Ioo (occurrenceArc R B o).left (occurrenceArc R B o).right} := fun h =>
    ⟨F.occurrence h.val, by
      obtain ⟨t,ht,htp⟩ := h.property
      exact ⟨t,hsub h.val ht,htp⟩⟩
  have hfinj : Function.Injective f := by
    intro h k heq
    apply Subtype.ext
    have hocc : F.occurrence h.val = F.occurrence k.val := congrArg Subtype.val heq
    by_contra hne
    obtain ⟨s,hs,hsp⟩ := h.property
    obtain ⟨t,ht,htp⟩ := k.property
    have htp' : (occurrenceArc R B (F.occurrence h.val)).curve t = p := by
      rwa [hocc]
    have ht' : t ∈ Ioo (occurrenceArc R B (F.occurrence h.val)).left
        (occurrenceArc R B (F.occurrence h.val)).right := by
      rw [hocc]
      exact hsub k.val ht
    have hst : s = t := occurrenceArc_injective R B (F.occurrence h.val)
      (hsub h.val hs) ht' (hsp.trans htp'.symm)
    rw [hst] at hs
    exact disjoint_left.mp (F.disjoint h.val k.val hne hocc) hs ht
  have hfsurj : Function.Surjective f := by
    intro o
    obtain ⟨t,ht,htp⟩ := o.property
    have hn : t ∉ F.cuts o.val := by
      intro hct
      exact hp (htp ▸ hcut o.val t hct)
    obtain ⟨h,hocc,hth⟩ := F.covers o.val t ht hn
    refine ⟨⟨h,t,hth,?_⟩,Subtype.ext hocc⟩
    rw [hocc]
    exact htp
  exact Equiv.ofBijective f ⟨hfinj,hfsurj⟩

theorem subdivision_point_support_card {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : P202Specs.GlobalGaussBonnet.BoundaryPresentation g)
    (F : FiniteSubdivision R B) (Z : Set M)
    (hcut : ∀ o t, t ∈ F.cuts o → (occurrenceArc R B o).curve t ∈ Z)
    (p : M) (hp : p ∉ Z) :
    Nat.card {h : Fin F.count // p ∈ (occurrenceArc R B (F.occurrence h)).curve '' Ioo (F.left h) (F.right h)} =
      Nat.card {o : Occurrence A B // p ∈ (occurrenceArc R B o).curve ''
        Ioo (occurrenceArc R B o).left (occurrenceArc R B o).right} :=
  Nat.card_congr (subdivisionPointSupportEquiv R B F Z hcut p hp)

/-- The canonical partition has the same point multiplicities as the original
occurrences at every point outside the common finite forbidden set. -/
theorem canonical_point_support_card {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) (p : M) (hp : p ∉ refinementForbiddenPoints R B) :
    let F := finiteSubdivision g D A R B
    Nat.card {h : Fin F.count // p ∈ (occurrenceArc R B (F.occurrence h)).curve '' Ioo (F.left h) (F.right h)} =
      Nat.card {o : Occurrence A B // p ∈ (occurrenceArc R B o).curve ''
        Ioo (occurrenceArc R B o).left (occurrenceArc R B o).right} := by
  exact subdivision_point_support_card R B (finiteSubdivision g D A R B)
    (refinementForbiddenPoints R B)
    (fun o t ht => refinementCuts_curve_mem_forbidden R B o ht) p hp

/-- Every open piece lies in its occurrence's original open interval. -/
lemma subdivision_piece_open_bounds {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    {R : RegionalRepresentatives g D A} {B : BoundaryPresentation g}
    (F : FiniteSubdivision R B) (h : Fin F.count) :
    Ioo (F.left h) (F.right h) ⊆
      Ioo (occurrenceArc R B (F.occurrence h)).left
        (occurrenceArc R B (F.occurrence h)).right := by
  intro t ht
  exact ⟨(subdivision_piece_bounds F h (left_mem_Icc.mpr (F.ordered h).le)).1.trans_lt ht.1,
    ht.2.trans_le (subdivision_piece_bounds F h (right_mem_Icc.mpr (F.ordered h).le)).2⟩

/-- Distinct parameter gaps of one literal occurrence have disjoint traces. -/
theorem subdivision_piece_same_occurrence_eq {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (F : FiniteSubdivision R B) (h k : Fin F.count)
    (ho : F.occurrence h = F.occurrence k)
    (hinter :
      ((occurrenceArc R B (F.occurrence h)).curve '' Ioo (F.left h) (F.right h) ∩
        (occurrenceArc R B (F.occurrence k)).curve '' Ioo (F.left k) (F.right k)).Nonempty) :
    h = k := by
  by_contra hne
  obtain ⟨p, ⟨t, ht, htp⟩, ⟨u, hu, hup⟩⟩ := hinter
  have hut : u ∈ Ioo (occurrenceArc R B (F.occurrence h)).left
      (occurrenceArc R B (F.occurrence h)).right := by
    simpa only [ho] using subdivision_piece_open_bounds F k hu
  have hcurve : (occurrenceArc R B (F.occurrence h)).curve t =
      (occurrenceArc R B (F.occurrence h)).curve u := by
    simpa only [ho] using htp.trans hup.symm
  have htu := occurrenceArc_injective R B (F.occurrence h)
    (subdivision_piece_open_bounds F h ht) hut hcurve
  exact disjoint_left.mp (F.disjoint h k hne ho) ht (htu.symm ▸ hu)

/-- Any two boundary-labelled pieces whose traces meet are the same piece. -/
theorem subdivision_boundary_pieces_eq {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (F : FiniteSubdivision R B) (h k : Fin F.count) (b c : Fin B.count)
    (hoh : F.occurrence h = .inr b) (hok : F.occurrence k = .inr c)
    (hinter :
      ((occurrenceArc R B (F.occurrence h)).curve '' Ioo (F.left h) (F.right h) ∩
        (occurrenceArc R B (F.occurrence k)).curve '' Ioo (F.left k) (F.right k)).Nonempty) :
    h = k := by
  have hbc : b = c := by
    by_contra hne
    obtain ⟨p, ⟨t, ht, htp⟩, ⟨u, hu, hup⟩⟩ := hinter
    apply disjoint_left.mp (B.disjoint hne)
    · refine ⟨t, ?_, ?_⟩
      · simpa only [hoh, occurrenceArc] using subdivision_piece_open_bounds F h ht
      · simpa only [hoh, occurrenceArc] using htp
    · refine ⟨u, ?_, ?_⟩
      · simpa only [hok, occurrenceArc] using subdivision_piece_open_bounds F k hu
      · simpa only [hok, occurrenceArc] using hup
  apply subdivision_piece_same_occurrence_eq R B F h k _ hinter
  rw [hoh, hok, hbc]

/-- A regional closure contributes at most one occurrence through every
non-cut point, including arbitrary extra smooth subdivisions in A. -/
theorem subdivision_same_region_pieces_eq {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (F : FiniteSubdivision R B) (h k : Fin F.count) (j : Fin D.regionCount)
    (i i' : Fin (D.region j).boundaryCount) (z : Fin (A j i).count)
    (z' : Fin (A j i').count)
    (hoh : F.occurrence h = .inl ⟨j, i, z⟩)
    (hok : F.occurrence k = .inl ⟨j, i', z'⟩)
    (hinter :
      ((occurrenceArc R B (F.occurrence h)).curve '' Ioo (F.left h) (F.right h) ∩
        (occurrenceArc R B (F.occurrence k)).curve '' Ioo (F.left k) (F.right k)).Nonempty) :
    h = k := by
  have hpair : (⟨i, z⟩ : Σ i : Fin (D.region j).boundaryCount, Fin (A j i).count) = ⟨i', z'⟩ := by
    by_contra hne
    obtain ⟨p, ⟨t, ht, htp⟩, ⟨u, hu, hup⟩⟩ := hinter
    apply disjoint_left.mp (R.disjoint j hne)
    · refine ⟨t, ?_, ?_⟩
      · simpa only [hoh, occurrenceArc, R.left, R.right] using
          subdivision_piece_open_bounds F h ht
      · simpa only [hoh, occurrenceArc] using htp
    · refine ⟨u, ?_, ?_⟩
      · simpa only [hok, occurrenceArc, R.left, R.right] using
          subdivision_piece_open_bounds F k hu
      · simpa only [hok, occurrenceArc] using hup
  apply subdivision_piece_same_occurrence_eq R B F h k _ hinter
  rw [hoh, hok]
  exact congrArg (fun a => Sum.inl (⟨j, a⟩ : RegionalIndex D A)) hpair

/-- Distinct meeting regional pieces have distinct original regional labels. -/
theorem subdivision_distinct_regional_labels {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (F : FiniteSubdivision R B) (h k : Fin F.count) (hne : h ≠ k)
    (j j' : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (i' : Fin (D.region j').boundaryCount) (z : Fin (A j i).count)
    (z' : Fin (A j' i').count)
    (hoh : F.occurrence h = .inl ⟨j, i, z⟩)
    (hok : F.occurrence k = .inl ⟨j', i', z'⟩)
    (hinter :
      ((occurrenceArc R B (F.occurrence h)).curve '' Ioo (F.left h) (F.right h) ∩
        (occurrenceArc R B (F.occurrence k)).curve '' Ioo (F.left k) (F.right k)).Nonempty) :
    j ≠ j' := by
  rintro rfl
  exact hne (subdivision_same_region_pieces_eq R B F h k j i i' z z' hoh hok hinter)


lemma subdivision_regional_piece_mem_regionClosure {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (F : FiniteSubdivision R B) (h : Fin F.count)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount) (z : Fin (A j i).count)
    (ho : F.occurrence h = .inl ⟨j, i, z⟩) {p : M}
    (hp : p ∈ (occurrenceArc R B (F.occurrence h)).curve '' Ioo (F.left h) (F.right h)) :
    p ∈ regionClosure D j := by
  obtain ⟨t, ht, rfl⟩ := hp
  have htunit : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [ho, occurrenceArc, R.left, R.right] using
      subdivision_piece_bounds F h (Ioo_subset_Icc_self ht)
  simpa only [ho, occurrenceArc] using (R.literal j i z t htunit).1.1

lemma canonical_piece_point_graph_nonvertex {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (h : Fin (finiteSubdivision g D A R B).count) {p : M}
    (hp : p ∈ (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve ''
      Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h)) :
    p ∈ D.graph.carrier ∧ p ∉ range D.graph.vertex := by
  let F := finiteSubdivision g D A R B
  constructor
  · obtain ⟨t, ht, rfl⟩ := hp
    exact occurrenceArc_on_graph R B (F.occurrence h)
      (subdivision_piece_bounds F h (Ioo_subset_Icc_self ht))
  · intro hpV
    exact disjoint_left.mp (canonical_piece_avoids_forbidden R B h) hp
      (Or.inl (Or.inl hpV))

theorem canonical_piece_no_boundary_boundary {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (h k : Fin (finiteSubdivision g D A R B).count) (hne : h ≠ k)
    (heq :
      (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve ''
        Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h) =
      (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence k)).curve ''
        Ioo ((finiteSubdivision g D A R B).left k) ((finiteSubdivision g D A R B).right k))
    (b c : Fin B.count)
    (hoh : (finiteSubdivision g D A R B).occurrence h = .inr b) :
    (finiteSubdivision g D A R B).occurrence k ≠ .inr c := by
  intro hok
  let F := finiteSubdivision g D A R B
  obtain ⟨p, hp⟩ := (nonempty_Ioo.mpr (F.ordered h)).image
    (occurrenceArc R B (F.occurrence h)).curve
  exact hne (subdivision_boundary_pieces_eq R B F h k b c hoh hok
    ⟨p, hp, heq ▸ hp⟩)

theorem canonical_piece_regional_regional_incidence {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (h k : Fin (finiteSubdivision g D A R B).count) (hne : h ≠ k)
    (heq :
      (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve ''
        Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h) =
      (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence k)).curve ''
        Ioo ((finiteSubdivision g D A R B).left k) ((finiteSubdivision g D A R B).right k))
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount) (z : Fin (A j i).count)
    (j' : Fin D.regionCount) (i' : Fin (D.region j').boundaryCount) (z' : Fin (A j' i').count)
    (hoh : (finiteSubdivision g D A R B).occurrence h = .inl ⟨j, i, z⟩)
    (hok : (finiteSubdivision g D A R B).occurrence k = .inl ⟨j', i', z'⟩) :
    j ≠ j' ∧ ∀ p ∈
      (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve ''
        Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h),
      p ∉ intrinsicBoundary S ∧ incidentRegions D p = {j, j'} ∧
        regionClosure D j ∪ regionClosure D j' ∈ 𝓝 p := by
  let F := finiteSubdivision g D A R B
  obtain ⟨q, hq⟩ := (nonempty_Ioo.mpr (F.ordered h)).image
    (occurrenceArc R B (F.occurrence h)).curve
  have hjj : j ≠ j' := subdivision_distinct_regional_labels R B F h k hne
    j j' i i' z z' hoh hok ⟨q, hq, heq ▸ hq⟩
  refine ⟨hjj, ?_⟩
  intro p hp
  have hpk := heq ▸ hp
  have hpj : j ∈ incidentRegions D p :=
    subdivision_regional_piece_mem_regionClosure R B F h j i z hoh hp
  have hpj' : j' ∈ incidentRegions D p :=
    subdivision_regional_piece_mem_regionClosure R B F k j' i' z' hok hpk
  obtain ⟨hpG, hpV⟩ := canonical_piece_point_graph_nonvertex R B h hp
  have hpB : p ∉ intrinsicBoundary S := by
    intro hpB
    obtain ⟨x, hx, _⟩ := regional_nonvertex_boundary_incidence D p hpG hpV hpB
    have hjx : j = x := by simpa only [hx, mem_singleton_iff] using hpj
    have hj'x : j' = x := by simpa only [hx, mem_singleton_iff] using hpj'
    exact hjj (hjx.trans hj'x.symm)
  obtain ⟨x, y, _, hxy, _⟩ := regional_nonvertex_interior_incidence D p hpG hpV hpB
  have hjxy : j ∈ ({x, y} : Set (Fin D.regionCount)) := hxy ▸ hpj
  have hj'xy : j' ∈ ({x, y} : Set (Fin D.regionCount)) := hxy ▸ hpj'
  have hpair : ({x, y} : Set (Fin D.regionCount)) = {j, j'} := by
    simp only [mem_insert_iff, mem_singleton_iff] at hjxy hj'xy
    rcases hjxy with rfl | rfl <;> rcases hj'xy with rfl | rfl
    · exact False.elim (hjj rfl)
    · rfl
    · exact pair_comm _ _
    · exact False.elim (hjj rfl)
  have hfinal : incidentRegions D p = {j, j'} := hxy.trans hpair
  exact ⟨hpB, hfinal, two_incident_regionClosures_mem_nhds D p j j' hfinal⟩

theorem canonical_piece_regional_boundary_incidence {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (h k : Fin (finiteSubdivision g D A R B).count)
    (heq :
      (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve ''
        Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h) =
      (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence k)).curve ''
        Ioo ((finiteSubdivision g D A R B).left k) ((finiteSubdivision g D A R B).right k))
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount) (z : Fin (A j i).count)
    (b : Fin B.count)
    (hoh : (finiteSubdivision g D A R B).occurrence h = .inl ⟨j, i, z⟩)
    (hok : (finiteSubdivision g D A R B).occurrence k = .inr b) :
    ∀ p ∈ (occurrenceArc R B ((finiteSubdivision g D A R B).occurrence h)).curve ''
      Ioo ((finiteSubdivision g D A R B).left h) ((finiteSubdivision g D A R B).right h),
      p ∈ intrinsicBoundary S ∧ incidentRegions D p = {j} ∧ regionClosure D j ∈ 𝓝 p := by
  let F := finiteSubdivision g D A R B
  intro p hp
  have hpj : j ∈ incidentRegions D p :=
    subdivision_regional_piece_mem_regionClosure R B F h j i z hoh hp
  obtain ⟨hpG, hpV⟩ := canonical_piece_point_graph_nonvertex R B h hp
  have hpB : p ∈ intrinsicBoundary S := by
    obtain ⟨t, ht, htp⟩ := heq ▸ hp
    rw [B.covers]
    apply mem_iUnion.mpr
    refine ⟨b, t, ?_, ?_⟩
    · simpa only [F, hok, occurrenceArc] using
        subdivision_piece_bounds F k (Ioo_subset_Icc_self ht)
    · simpa only [F, hok, occurrenceArc] using htp
  obtain ⟨x, hx, _⟩ := regional_nonvertex_boundary_incidence D p hpG hpV hpB
  have hjx : j = x := by simpa only [hx, mem_singleton_iff] using hpj
  have hfinal : incidentRegions D p = {j} := by simpa only [hjx] using hx
  exact ⟨hpB, hfinal, one_incident_regionClosure_mem_nhds D p j hfinal⟩

/-- The canonical finite subdivision carries an actual fixed-point-free mate
involution, all literal closed transitions, and the exact occupied-set germs. -/
theorem canonical_commonRefinement_exists {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g) :
    Nonempty (CommonRefinement R B) := by
  classical
  let F := finiteSubdivision g D A R B
  let T : Fin F.count → Set M := fun h =>
    (occurrenceArc R B (F.occurrence h)).curve '' Ioo (F.left h) (F.right h)
  have hne : ∀ h, (T h).Nonempty := by
    intro h
    exact (isConnected_Ioo (F.ordered h)).nonempty.image _
  have hcard : ∀ p ∈ ⋃ h, T h, Nat.card {h // p ∈ T h} = 2 := by
    intro p hp
    obtain ⟨h, hph⟩ := mem_iUnion.mp hp
    have hF : p ∉ refinementForbiddenPoints R B :=
      fun hpF => Set.disjoint_left.mp (canonical_piece_avoids_forbidden R B h) hph hpF
    have hG : p ∈ D.graph.carrier := by
      obtain ⟨t, ht, rfl⟩ := hph
      exact occurrenceArc_on_graph R B (F.occurrence h)
        (subdivision_piece_bounds F h (Ioo_subset_Icc_self ht))
    exact (canonical_point_support_card R B p hF).trans
      (occurrence_support_card_two R B p hG hF)
  have hmeet : ∀ h k, (T h ∩ T k).Nonempty → T h = T k :=
    fun h k hp => canonical_piece_traces_eq_of_inter R B h k hp
  obtain ⟨mate, hmate, hfixed, htrace⟩ := TracePairing.exists_trace_mate T hne hcard hmeet
  let edge : Fin F.count → Fin D.graph.edgeCount :=
    fun h => (subdivision_piece_one_openEdge R B F h).choose
  have hedge : ∀ h, T h ⊆ D.graph.edge (edge h) ''
      {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} :=
    fun h => (subdivision_piece_one_openEdge R B F h).choose_spec
  have hedge_mate : ∀ h, edge (mate h) = edge h := by
    intro h
    by_contra hneedge
    obtain ⟨p, hp⟩ := hne h
    have hpm : p ∈ T (mate h) := (htrace h).symm ▸ hp
    exact Set.disjoint_left.mp (D.graph.disjoint_open_edges hneedge)
      (hedge (mate h) hpm) (hedge h hp)
  let transition : Fin F.count → ℝ → ℝ := fun h =>
    (canonical_piece_transition R B h (mate h) (htrace h).symm).choose
  have htransition (h : Fin F.count) :=
    (canonical_piece_transition R B h (mate h) (htrace h).symm).choose_spec
  refine ⟨{
    toFiniteSubdivision := F
    mate := mate
    involutive := hmate
    fixed_point_free := hfixed
    no_boundary_boundary := ?_
    edge := edge
    edge_mate := hedge_mate
    in_edge := hedge
    trace_eq := fun h => (htrace h).symm
    transition := transition
    continuous := fun h => (htransition h).1
    monotone := fun h => (htransition h).2.1
    image_open := fun h => (htransition h).2.2.1
    image_closed := fun h => (htransition h).2.2.2.1
    point_eq := fun h => (htransition h).2.2.2.2.1
    hasDerivAt := fun h => (htransition h).2.2.2.2.2.1
    derivative_sign := fun h => (htransition h).2.2.2.2.2.2
    interior_incidence := ?_
    boundary_incidence := ?_ }⟩
  · intro h b c hb hc
    exact canonical_piece_no_boundary_boundary R B h (mate h) (hfixed h).symm
      (htrace h).symm b c hb hc
  · intro h j i k j' i' k' hh hm
    exact canonical_piece_regional_regional_incidence R B h (mate h) (hfixed h).symm
      (htrace h).symm j i k j' i' k' hh hm
  · intro h j i k b hh hm
    exact canonical_piece_regional_boundary_incidence R B h (mate h)
      (htrace h).symm j i k b hh hm

/-- Full original regional/boundary common refinement, for every supplied
original D, A and B and with no geometric certificates as premises. -/
theorem regional_boundary_refinement :
    P202Specs.RegionalBoundaryRefinement.Expected.commonRefinement.{u} := by
  intro kind M _ _ S g D A B
  let R := regionalRepresentatives g D A
  exact ⟨R, canonical_commonRefinement_exists R B⟩

end P202.GlobalGaussBonnet.BoundaryGluing
