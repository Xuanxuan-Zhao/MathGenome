import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.GraphFundamentalGroup
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.ContractibleCollapse
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.ContractibleCollapse
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.FundamentalGroupoid
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.BasicFundamentalGroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.DiscreteSubset
import Mathlib.Data.Fintype.Option

/-!
The graph conclusion of paper.tex, Theorem 2.5, for arbitrary connected CW
graphs. We construct a spanning maximal tree, contract its actual carrier by
compatible rooted edge squares, and identify its collapse with the weak bouquet.
Open collar deformations and van Kampen give the finite-bouquet calculation;
continuous retractions and compact support give the arbitrary-generator case.
The final isomorphism records the actual oriented edges at every basepoint.
-/

noncomputable section
open Set Topology ContinuousMap
open scoped unitInterval
open P202.Cellular P202Specs.Topology
universe u v

namespace P202.Cellular.EdgeEndpoints
variable {V : Type u} {E : Type v} (d : EdgeEndpoints V E)

lemma support_mono {S T : Set E} (h : S ⊆ T) : d.support S ≤ d.support T := by
  intro x y hxy
  exact ⟨hxy.1, hxy.2.imp fun e he => ⟨h he.1, he.2⟩⟩

lemma support_adj_iff (T : Set E) (x y : V) :
    (d.support T).Adj x y ↔ x ≠ y ∧ ∃ e ∈ T, d.ends e = s(x,y) := by
  simp only [support, ends, Sym2.eq_iff]

/-- Choose exactly one original edge above each edge of a simple subgraph.
The unused parallel edges, and every loop, stay in the complement. -/
theorem exists_edge_selection (F : SimpleGraph V) (hF : F ≤ d.support univ) :
    ∃ T : Set E, (∀ e ∈ T, d.source e ≠ d.target e) ∧
      Set.InjOn d.ends T ∧ d.support T = F := by
  classical
  have hex : ∀ a : F.edgeSet, ∃ e : E, d.ends e = a.val := by
    rintro ⟨a, ha⟩
    induction a using Sym2.ind with
    | _ x y =>
      have hxy := hF ha
      obtain ⟨e, _, he⟩ := ((d.support_adj_iff univ x y).mp hxy).2
      exact ⟨e, he⟩
  choose f hf using hex
  let T : Set E := range f
  have hn : ∀ e ∈ T, d.source e ≠ d.target e := by
    rintro e ⟨a, rfl⟩ he
    apply F.not_isDiag_of_mem_edgeSet a.property
    rw [← hf a]
    exact Sym2.mk_isDiag_iff.mpr he
  have hinj : Set.InjOn d.ends T := by
    rintro e ⟨a, rfl⟩ e' ⟨b, rfl⟩ h
    have hab : a = b := Subtype.ext ((hf a).symm.trans (h.trans (hf b)))
    exact congrArg f hab
  refine ⟨T, hn, hinj, ?_⟩
  ext x y
  rw [d.support_adj_iff]
  constructor
  · rintro ⟨_, e, ⟨a, rfl⟩, he⟩
    have ha := a.property
    rwa [← hf a, he] at ha
  · intro hxy
    refine ⟨hxy.ne, f ⟨s(x,y), hxy⟩, ⟨⟨s(x,y), hxy⟩, rfl⟩, hf _⟩

/-- A spanning multigraph tree is maximal acyclic, including with respect to
adding parallel edges or loops. -/
theorem IsSpanningTree.maximal {T : Set E} (hT : d.IsSpanningTree T) :
    Maximal d.IsForest T := by
  refine ⟨hT.1, ?_⟩
  intro S hS hTS
  have hsupp : d.support T = d.support S := by
    have hc : (d.support S).Connected :=
      SimpleGraph.Connected.mono (d.support_mono hTS) hT.2
    have hmax := (hc.maximal_le_isAcyclic_iff_isTree (d.support_mono hTS)).mpr
      ⟨hT.2, hT.1.2.2⟩
    exact hmax.eq_of_le ⟨le_rfl, hS.2.2⟩ (d.support_mono hTS)
  intro e he
  have he' : (d.support S).Adj (d.source e) (d.target e) :=
    ⟨hS.1 e he, e, he, Or.inl ⟨rfl, rfl⟩⟩
  rw [← hsupp] at he'
  obtain ⟨f, hf, hfe⟩ := ((d.support_adj_iff T _ _).mp he').2
  have hfe' : f = e := hS.2.1 (hTS hf) he hfe
  exact hfe' ▸ hf

/-- The full choice argument for arbitrary multigraphs; no finiteness of the
vertex set, edge set, or valences is needed. -/
theorem exists_spanningTree_of_connected (h : (d.support univ).Connected) :
    ∃ T : Set E, d.IsSpanningTree T ∧ Maximal d.IsForest T := by
  obtain ⟨F, hF, ht⟩ := h.exists_isTree_le
  obtain ⟨T, hn, hi, he⟩ := d.exists_edge_selection F hF
  have hT : d.IsSpanningTree T := by
    refine ⟨⟨hn, hi, ?_⟩, ?_⟩
    · simpa only [he] using ht.isAcyclic
    · simpa only [he] using ht.connected
  exact ⟨T, hT, hT.maximal⟩

end P202.Cellular.EdgeEndpoints

namespace P202.Topology
open private cell_unique closedCell_subset_cell_union_skeleton from MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellTopology

variable {X : Type u} [TopologicalSpace X] [CWStructure X]

lemma mem_graphVertex_iff (x : X) :
    x ∈ skeletonLT X 1 ↔ ∃ c : Cell X 0, x ∈ openCell X 0 c := by
  simp [skeletonLT]

lemma graph_point_cases (h : IsGraph X) (x : X) :
    x ∈ skeletonLT X 1 ∨ ∃ e : Cell X 1, x ∈ openCell X 1 e := by
  have hc : x ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
    rw [CWStructure.cover]
    trivial
  obtain ⟨n, c, hxc⟩ := mem_iUnion₂.mp hc
  cases n with
  | zero => exact Or.inl ((mem_graphVertex_iff x).mpr ⟨c, hxc⟩)
  | succ n =>
    cases n with
    | zero => exact Or.inr ⟨c, hxc⟩
    | succ n =>
      haveI := h (n + 2) (by omega)
      exact isEmptyElim c

lemma vertex_not_in_open_edge {x : X} (hx : x ∈ skeletonLT X 1)
    (e : Cell X 1) : x ∉ openCell X 1 e := by
  obtain ⟨c, hc⟩ := (mem_graphVertex_iff x).mp hx
  intro he
  have h := congrArg Sigma.fst (cell_unique (d := ⟨0, c⟩) (e := ⟨1, e⟩) hc he)
  exact Nat.zero_ne_one h

/-- Select a vertex in the same edge as a point. This map need not itself be
continuous; its connected-component class will be continuous. -/
def graphVertexRepresentative (h : IsGraph X) (x : X) : GraphVertex X := by
  classical
  exact if hv : x ∈ skeletonLT X 1 then ⟨x, hv⟩ else
    (graphEndpoints X).source ((graph_point_cases h x).resolve_left hv).choose

lemma graphVertexRepresentative_vertex (h : IsGraph X) (v : GraphVertex X) :
    graphVertexRepresentative h v.val = v := by
  classical
  simp [graphVertexRepresentative, v.property]

lemma graphVertexRepresentative_edge (h : IsGraph X) (e : Cell X 1)
    {x : X} (hx : x ∈ openCell X 1 e) :
    graphVertexRepresentative h x = (graphEndpoints X).source e := by
  classical
  have hv : x ∉ skeletonLT X 1 := fun hv => vertex_not_in_open_edge hv e hx
  simp only [graphVertexRepresentative, dite_eq_right hv]
  congr 1
  have hc := ((graph_point_cases h x).resolve_left hv).choose_spec
  exact eq_of_heq (Sigma.mk.inj_iff.mp (cell_unique hc hx)).2

lemma diskOne_boundary_cases (z : Sphere 1) :
    boundaryInclusion 1 z = edgeDiskPoint 0 ∨
    boundaryInclusion 1 z = edgeDiskPoint 1 := by
  have hz : z.val = EuclideanSpace.single 0 (z.val 0) := by
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simp [EuclideanSpace.single]
  have hn : |z.val 0| = 1 := by
    have hm : ‖z.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.property
    rw [hz] at hm
    simpa [EuclideanSpace.single] using hm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with hp | hm
  · right
    apply Subtype.ext
    simpa [edgeDiskPoint, boundaryInclusion, hp, show (2 : ℝ) - 1 = 1 by norm_num] using hz
  · left
    apply Subtype.ext
    simpa [edgeDiskPoint, boundaryInclusion, hm] using hz

lemma diskOne_cases (z : Disk 1) :
    (∃ y : OpenDisk 1, interiorInclusion 1 y = z) ∨
    z = edgeDiskPoint 0 ∨ z = edgeDiskPoint 1 := by
  have hz : ‖z.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  rcases lt_or_eq_of_le hz with hz | hz
  · left
    exact ⟨⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩, rfl⟩
  · right
    exact diskOne_boundary_cases ⟨z.val, by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩

lemma graph_edge_endpoints_reachable (e : Cell X 1) :
    ((graphEndpoints X).support univ).Reachable
      ((graphEndpoints X).source e) ((graphEndpoints X).target e) := by
  by_cases h : (graphEndpoints X).source e = (graphEndpoints X).target e
  · rw [h]
  · exact SimpleGraph.Adj.reachable ⟨h, e, mem_univ _, Or.inl ⟨rfl, rfl⟩⟩

/-- Pointwise component assignment for the graph. -/
def graphComponentMap (h : IsGraph X) :
    X → ((graphEndpoints X).support univ).ConnectedComponent :=
  fun x => ((graphEndpoints X).support univ).connectedComponentMk
    (graphVertexRepresentative h x)

lemma graphComponentMap_vertex (h : IsGraph X) (v : GraphVertex X) :
    graphComponentMap h v.val =
      ((graphEndpoints X).support univ).connectedComponentMk v := by
  simp only [graphComponentMap, graphVertexRepresentative_vertex]

lemma graphComponentMap_edge (h : IsGraph X) (e : Cell X 1) (z : Disk 1) :
    graphComponentMap h (characteristic X 1 e z) =
      ((graphEndpoints X).support univ).connectedComponentMk
        ((graphEndpoints X).source e) := by
  rcases diskOne_cases z with ⟨y, rfl⟩ | rfl | rfl
  · exact congrArg _ (graphVertexRepresentative_edge h e ⟨y, rfl⟩)
  · exact graphComponentMap_vertex h ((graphEndpoints X).source e)
  · exact (graphComponentMap_vertex h ((graphEndpoints X).target e)).trans
      (SimpleGraph.ConnectedComponent.sound (graph_edge_endpoints_reachable e)).symm

/-- The weak topology turns the component assignment into a continuous map
to a discrete space, also for infinitely many cells. -/
lemma graphComponentMap_continuous (h : IsGraph X) :
    @Continuous X _ inferInstance ⊥ (graphComponentMap h) := by
  letI : TopologicalSpace ((graphEndpoints X).support univ).ConnectedComponent := ⊥
  apply (continuityTest (graphComponentMap h)).mpr
  intro n c
  cases n with
  | zero => exact continuous_of_const fun a b => congrArg _ (Subsingleton.elim a b)
  | succ n =>
    cases n with
    | zero =>
      have he : graphComponentMap h ∘ characteristic X 1 c = fun _ =>
          ((graphEndpoints X).support univ).connectedComponentMk
            ((graphEndpoints X).source c) := funext (graphComponentMap_edge h c)
      rw [he]
      exact continuous_const
    | succ n =>
      haveI := h (n + 2) (by omega)
      exact isEmptyElim c

/-- Nonempty CW graphs contain a vertex, even when the initially chosen point
is in an open edge. -/
lemma graphVertex_nonempty (h : IsGraph X) [Nonempty X] : Nonempty (GraphVertex X) :=
  ⟨graphVertexRepresentative h (Classical.choice ‹Nonempty X›)⟩

/-- Topological connectedness implies combinatorial connectedness without
assuming a finite graph or local finiteness. -/
theorem graph_support_connected (h : IsGraph X) [ConnectedSpace X] :
    ((graphEndpoints X).support univ).Connected := by
  letI : TopologicalSpace ((graphEndpoints X).support univ).ConnectedComponent := ⊥
  letI : DiscreteTopology ((graphEndpoints X).support univ).ConnectedComponent :=
    discreteTopology_bot _
  letI := graphVertex_nonempty h
  refine ⟨?_⟩
  intro v w
  apply SimpleGraph.ConnectedComponent.exact
  have he := TotallyDisconnectedSpace.eq_of_continuous
    (graphComponentMap h) (graphComponentMap_continuous h) v.val w.val
  simpa only [graphComponentMap_vertex] using he

/-- The spanning maximal tree assertion for the original topological graph,
with its actual geometric edge labels. -/
theorem graph_spanningTree_exists (h : IsGraph X) [ConnectedSpace X] :
    ∃ T : Set (Cell X 1), (graphEndpoints X).IsSpanningTree T ∧
      Maximal (graphEndpoints X).IsForest T :=
  (graphEndpoints X).exists_spanningTree_of_connected (graph_support_connected h)


private def graphSelectedCells (T : Set (Cell X 1)) : ∀ n, Set (Cell X n)
  | 0 => univ
  | 1 => T
  | _ + 2 => ∅

/-- The genuine subcomplex consisting of all vertices and the selected edges.
It exists in any CW complex, with no constraint on its higher-dimensional cells. -/
def graphSubcomplex (T : Set (Cell X 1)) : Subcomplex X where
  cells := graphSelectedCells T
  contains_closures := by
    intro n c hc x hx
    rw [closureOpenCell n c] at hx
    rcases closedCell_subset_cell_union_skeleton n c hx with ho | hs
    · exact mem_iUnion₂.mpr ⟨n, ⟨c, hc⟩, ho⟩
    · cases n with
      | zero => simp [skeletonLT] at hs
      | succ n =>
        cases n with
        | zero =>
          obtain ⟨c₀, hc₀⟩ := (mem_graphVertex_iff x).mp hs
          exact mem_iUnion₂.mpr ⟨0, ⟨c₀, mem_univ _⟩, hc₀⟩
        | succ n => exact hc.elim

lemma graphSubcomplex_carrier (T : Set (Cell X 1)) :
    (graphSubcomplex T).carrier = graphTreeCarrier T := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, c, hxc⟩ := mem_iUnion₂.mp hx
    cases n with
    | zero => exact Or.inl ((mem_graphVertex_iff x).mpr ⟨c.val, hxc⟩)
    | succ n =>
      cases n with
      | zero => exact Or.inr (mem_iUnion₂.mpr ⟨c.val, c.property, hxc⟩)
      | succ n => exact c.property.elim
  · intro hx
    rcases hx with hv | he
    · obtain ⟨c, hc⟩ := (mem_graphVertex_iff x).mp hv
      exact mem_iUnion₂.mpr ⟨0, ⟨c, mem_univ _⟩, hc⟩
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp he
      exact mem_iUnion₂.mpr ⟨1, ⟨e, he⟩, hxe⟩

lemma graphTreeCarrier_closed (T : Set (Cell X 1)) : IsClosed (graphTreeCarrier T) := by
  rw [← graphSubcomplex_carrier]
  exact subcomplexClosed _

lemma graphEdgePath_mem_tree {T : Set (Cell X 1)} {e : Cell X 1} (he : e ∈ T)
    (t : unitInterval) : graphEdgePath e t ∈ graphTreeCarrier T := by
  have hh : graphEdgePath e t ∈ closedCell X 1 e := ⟨edgeDiskPoint t, rfl⟩
  rcases closedCell_subset_cell_union_skeleton 1 e hh with ho | hv
  · exact Or.inr (mem_iUnion₂.mpr ⟨e, he, ho⟩)
  · exact Or.inl hv

/-- Any adjacency in the simple support is realized by a path along an actual
selected characteristic edge; parallel edge labels are not identified. -/
lemma graph_support_adj_path {T : Set (Cell X 1)} {v w : GraphVertex X}
    (h : ((graphEndpoints X).support T).Adj v w) :
    ∃ p : Path v.val w.val, ∀ t, p t ∈ graphTreeCarrier T := by
  obtain ⟨_, e, he, hor⟩ := h
  rcases hor with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · exact ⟨(graphEdgePath e).cast (congrArg Subtype.val hs.symm)
        (congrArg Subtype.val ht.symm), graphEdgePath_mem_tree he⟩
  · exact ⟨(graphEdgePath e).symm.cast (congrArg Subtype.val hs.symm)
        (congrArg Subtype.val ht.symm), fun t => graphEdgePath_mem_tree he _⟩

/-- Finite combinatorial walks give paths in the spanning subcomplex. -/
lemma graph_support_walk_path {T : Set (Cell X 1)} {v w : GraphVertex X}
    (p : ((graphEndpoints X).support T).Walk v w) :
    ∃ q : Path v.val w.val, ∀ t, q t ∈ graphTreeCarrier T := by
  induction p with
  | @nil v => exact ⟨Path.refl _, fun _ => Or.inl v.property⟩
  | @cons v w z hvw tail ih =>
    obtain ⟨a, ha⟩ := graph_support_adj_path hvw
    obtain ⟨b, hb⟩ := ih
    refine ⟨a.trans b, ?_⟩
    intro t
    have hh : a.trans b t ∈ range a ∪ range b := by
      rw [← Path.trans_range]
      exact mem_range_self _
    rcases hh with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [← hs]; exact ha s
    · rw [← hs]; exact hb s

/-- Tree paths needed for the oriented generators in the independent target. -/
theorem graph_tree_paths {T : Set (Cell X 1)}
    (h : (graphEndpoints X).IsSpanningTree T) (r : GraphVertex X) :
    ∃ p : ∀ v : GraphVertex X, Path r.val v.val,
      ∀ v t, p v t ∈ graphTreeCarrier T := by
  have hh : ∀ v : GraphVertex X, ∃ p : Path r.val v.val,
      ∀ t, p t ∈ graphTreeCarrier T := by
    intro v
    obtain ⟨w⟩ := h.2 r v
    exact graph_support_walk_path w
  choose p hp using hh
  exact ⟨p, hp⟩


/-- Restriction of a path to a containing subcomplex with specified endpoints. -/
def pathInSubcomplex {x y : X} (A : Subcomplex X) (hx : x ∈ A.carrier)
    (hy : y ∈ A.carrier) (p : Path x y) (hp : ∀ t, p t ∈ A.carrier) :
    Path (⟨x, hx⟩ : A) ⟨y, hy⟩ where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

def subcomplexPointedInclusion (A : Subcomplex X) (x : X) (hx : x ∈ A.carrier) :
    PointedMap A X ⟨x, hx⟩ x :=
  ⟨⟨Subtype.val, continuous_subtype_val⟩, rfl⟩

/-- Every loop class comes from a finite subcomplex, without a finite ambient
complex assumption. This is the surjectivity part of the finite-support passage. -/
theorem fundamentalGroup_finite_support (x : X) (a : Pi1 X x) :
    ∃ (A : Subcomplex X), A.IsFinite ∧ ∃ hx : x ∈ A.carrier,
      ∃ b : Pi1 A ⟨x, hx⟩, (subcomplexPointedInclusion A x hx).induced b = a := by
  obtain ⟨p, rfl⟩ := loopClass_surjective a
  obtain ⟨A, hfin, hA⟩ := intervalMapFiniteSupport p.toContinuousMap
  have hp : ∀ t, p t ∈ A.carrier := fun t => hA (mem_range_self t)
  have hx : x ∈ A.carrier := p.source ▸ hp 0
  refine ⟨A, hfin, hx, loopClass (pathInSubcomplex A hx hx p hp), ?_⟩
  rw [inducedFormula]
  congr 1

/-- A homotopy of paths is already an endpoint-fixed homotopy in one finite
subcomplex. Thus equality of loop classes is detected at a finite stage, not
just the existence of representatives. -/
theorem pathHomotopy_finite_support {x y : X} {a b : Path x y}
    (H : a.Homotopy b) :
    ∃ (A : Subcomplex X), A.IsFinite ∧
      ∃ (hx : x ∈ A.carrier) (hy : y ∈ A.carrier)
        (aA bA : Path (⟨x, hx⟩ : A) ⟨y, hy⟩),
        Nonempty (aA.Homotopy bA) ∧
        (∀ t, (aA t).val = a t) ∧ (∀ t, (bA t).val = b t) := by
  obtain ⟨A, hfin, hA⟩ := intervalHomotopyFiniteSupport H.toHomotopy.toContinuousMap
  have hH : ∀ z, H z ∈ A.carrier := fun z => hA (mem_range_self z)
  have ha : ∀ t, a t ∈ A.carrier := fun t => H.map_zero_left t ▸ hH (0,t)
  have hb : ∀ t, b t ∈ A.carrier := fun t => H.map_one_left t ▸ hH (1,t)
  have hx : x ∈ A.carrier := a.source ▸ ha 0
  have hy : y ∈ A.carrier := a.target ▸ ha 1
  let aA := pathInSubcomplex A hx hy a ha
  let bA := pathInSubcomplex A hx hy b hb
  refine ⟨A, hfin, hx, hy, aA, bA, ⟨?_⟩, fun _ => rfl, fun _ => rfl⟩
  exact {
    toFun := fun z => ⟨H z, hH z⟩
    continuous_toFun := H.continuous.subtype_mk _
    map_zero_left := fun t => Subtype.ext (H.map_zero_left t)
    map_one_left := fun t => Subtype.ext (H.map_one_left t)
    prop' := fun t z hz => Subtype.ext (H.eq_fst t hz) }


/-- The chosen orientation parametrizes the entire characteristic disk. -/
lemma edgeDiskPoint_surjective : Function.Surjective edgeDiskPoint := by
  intro z
  have hz : z.val = EuclideanSpace.single 0 (z.val 0) := by
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simp [EuclideanSpace.single]
  have hn : |z.val 0| ≤ 1 := by
    have hm : ‖z.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
    rw [hz] at hm
    simpa [EuclideanSpace.single] using hm
  let t : unitInterval := ⟨(z.val 0 + 1) / 2,
    by constructor <;> linarith [(abs_le.mp hn).1, (abs_le.mp hn).2]⟩
  refine ⟨t, ?_⟩
  apply Subtype.ext
  dsimp [edgeDiskPoint, t]
  rw [show 2 * ((z.val 0 + 1) / 2) - 1 = z.val 0 by ring]
  exact hz.symm

/-- A point of the selected spanning subcomplex can be joined to a vertex
through the same selected edge. -/
lemma graph_point_joined_vertex {T : Set (Cell X 1)} {x : X}
    (hx : x ∈ graphTreeCarrier T) :
    ∃ v : GraphVertex X, ∃ p : Path v.val x, ∀ t, p t ∈ graphTreeCarrier T := by
  rcases hx with hv | he
  · exact ⟨⟨x, hv⟩, Path.refl x, fun _ => Or.inl hv⟩
  · obtain ⟨e, he, y, hxy⟩ := mem_iUnion₂.mp he
    obtain ⟨t, ht⟩ := edgeDiskPoint_surjective (interiorInclusion 1 y)
    have hp : graphEdgePath e t = x := by
      change characteristic X 1 e (edgeDiskPoint t) = x
      rw [ht]
      exact hxy
    let p := (graphEdgePath e).truncateOfLE t.property.1
    refine ⟨(graphEndpoints X).source e,
      p.cast ((graphEdgePath e).extend_zero.symm)
        (((graphEdgePath e).extend_extends' t).trans hp).symm, ?_⟩
    intro s
    have hmem : p s ∈ range (graphEdgePath e) :=
      Path.truncate_range _ (mem_range_self s)
    obtain ⟨z, hz⟩ := hmem
    change p s ∈ graphTreeCarrier T
    rw [← hz]
    exact graphEdgePath_mem_tree he z

/-- The actual spanning subcomplex is path connected. -/
theorem graph_tree_pathConnected {T : Set (Cell X 1)}
    (h : (graphEndpoints X).IsSpanningTree T) :
    IsPathConnected (graphTreeCarrier T) := by
  haveI := h.2.nonempty
  let r : GraphVertex X := Classical.choice h.2.nonempty
  refine ⟨r.val, Or.inl r.property, ?_⟩
  intro x hx
  obtain ⟨v, b, hb⟩ := graph_point_joined_vertex hx
  obtain ⟨p, hp⟩ := graph_tree_paths h r
  refine ⟨(p v).trans b, ?_⟩
  intro t
  have hh : (p v).trans b t ∈ range (p v) ∪ range b := by
    rw [← Path.trans_range]
    exact mem_range_self _
  rcases hh with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]; exact hp v s
  · rw [← hs]; exact hb s

/-- Connected CW graphs are path connected; this supplies the path from an
arbitrary basepoint to the root required by the oriented-generator formula. -/
theorem graph_pathConnected (h : IsGraph X) [ConnectedSpace X] : PathConnectedSpace X := by
  obtain ⟨T, hT, _⟩ := graph_spanningTree_exists h
  haveI := hT.2.nonempty
  let r : GraphVertex X := Classical.choice hT.2.nonempty
  have hr : r.val ∈ graphTreeCarrier T := Or.inl r.property
  have ht := graph_tree_pathConnected hT
  apply pathConnectedSpace_iff_eq.mpr
  refine ⟨r.val, Set.eq_univ_of_forall fun x => ?_⟩
  rcases graph_point_cases h x with hv | ⟨e, he⟩
  · exact (ht.joinedIn r.val hr x (Or.inl hv)).joined
  · obtain ⟨v, p, _⟩ := graph_point_joined_vertex
      (T := (univ : Set (Cell X 1))) (Or.inr (mem_iUnion₂.mpr ⟨e, mem_univ _, he⟩))
    exact ((ht.joinedIn r.val hr v.val (Or.inl v.property)).joined).trans ⟨p⟩

/-- Apply the current upstream collapse theorem once tree contractibility
has been established. -/
theorem graph_tree_collapse
    (T : Set (Cell X 1)) (hn : Nonempty (GraphVertex X))
    (hc : ContractibleSpace (graphSubcomplex T)) :
    ∃ e : X ≃ₕ Collapse (graphSubcomplex T),
      e.toFun = collapseProjection (graphSubcomplex T) := by
  apply contractibleCollapse _ _ hc
  obtain ⟨v⟩ := hn
  rw [graphSubcomplex_carrier]
  exact ⟨v.val, Or.inl v.property⟩

end P202.Topology

namespace P202.Topology

/-- Every element of a free group is supported on finitely many generators.
This is independent of cardinality and is compatible with the canonical maps. -/
theorem freeGroup_finite_support {E : Type u} (g : FreeGroup E) :
    ∃ S : Finset E, ∃ w : FreeGroup S,
      FreeGroup.map (Subtype.val : S → E) w = g := by
  classical
  induction g using FreeGroup.induction_on with
  | one => exact ⟨∅, 1, map_one _⟩
  | of e => exact ⟨{e}, FreeGroup.of ⟨e, Finset.mem_singleton_self e⟩, rfl⟩
  | inv_of e ih =>
    obtain ⟨S, w, hw⟩ := ih
    exact ⟨S, w⁻¹, by rw [map_inv, hw]⟩
  | mul a b ha hb =>
    obtain ⟨S, w, hw⟩ := ha
    obtain ⟨T, z, hz⟩ := hb
    let i : S → ↥(S ∪ T) := fun e => ⟨e.val, Finset.mem_union_left _ e.property⟩
    let j : T → ↥(S ∪ T) := fun e => ⟨e.val, Finset.mem_union_right _ e.property⟩
    refine ⟨S ∪ T, FreeGroup.map i w * FreeGroup.map j z, ?_⟩
    rw [map_mul, FreeGroup.map.comp, FreeGroup.map.comp]
    exact congrArg₂ (· * ·) hw hz

/-- Restricting the generator assignment commutes with the canonical free-group
map; this is the compatibility needed for an infinite bouquet calculation. -/
lemma freeGroup_lift_map {E : Type u} {G : Type v} [Group G] (f : E → G)
    (S : Finset E) (w : FreeGroup S) :
    FreeGroup.lift f (FreeGroup.map (Subtype.val : S → E) w) =
      FreeGroup.lift (fun e : S => f e.val) w := by
  have he : (FreeGroup.lift f).comp (FreeGroup.map (Subtype.val : S → E)) =
      FreeGroup.lift (fun e : S => f e.val) := by
    apply FreeGroup.ext_hom
    intro e
    simp
  exact DFunLike.congr_fun he w

/-- Finite calculations determine the infinite free group calculation once
surjectivity and injectivity are known at the finite stages. The hypotheses
are explicit; this lemma does not supply the finite bouquet theorem. -/
theorem freeGroup_lift_bijective_of_finite {E : Type u} {G : Type v} [Group G]
    (f : E → G)
    (hinj : ∀ S : Finset E, Function.Injective (FreeGroup.lift (fun e : S => f e.val)))
    (hsurj : ∀ g : G, ∃ (S : Finset E) (w : FreeGroup S),
      FreeGroup.lift (fun e : S => f e.val) w = g) :
    Function.Bijective (FreeGroup.lift f) := by
  constructor
  · apply (injective_iff_map_eq_one _).mpr
    intro g hg
    obtain ⟨S, w, hw⟩ := freeGroup_finite_support g
    have hh : FreeGroup.lift (fun e : S => f e.val) w = 1 := by
      rw [← freeGroup_lift_map f, hw, hg]
    have hw1 : w = 1 := hinj S (hh.trans (map_one _).symm)
    rw [← hw, hw1, map_one]
  · intro g
    obtain ⟨S, w, hw⟩ := hsurj g
    exact ⟨FreeGroup.map (Subtype.val : S → E) w,
      (freeGroup_lift_map f S w).trans hw⟩

end P202.Topology

namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

attribute [local instance] Classical.propDecidable
open private cell_unique from MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellTopology

/-- The inverse affine coordinate on the actual characteristic one-disk. -/
def edgeDiskParameter (z : Disk 1) : unitInterval :=
  ⟨(z.val 0 + 1) / 2, by
    have hz : z.val = EuclideanSpace.single 0 (z.val 0) := by
      ext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simp [EuclideanSpace.single]
    have hn : |z.val 0| ≤ 1 := by
      have hm : ‖z.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      rw [hz] at hm
      simpa [EuclideanSpace.single] using hm
    constructor <;> linarith [(abs_le.mp hn).1, (abs_le.mp hn).2]⟩

@[simp] lemma edgeDiskParameter_point (t : unitInterval) :
    edgeDiskParameter (edgeDiskPoint t) = t := by
  apply Subtype.ext
  simp [edgeDiskParameter, edgeDiskPoint, EuclideanSpace.single]

@[simp] lemma edgeDiskPoint_parameter (z : Disk 1) :
    edgeDiskPoint (edgeDiskParameter z) = z := by
  obtain ⟨t, rfl⟩ := edgeDiskPoint_surjective z
  rw [edgeDiskParameter_point]

lemma edgeDiskParameter_continuous : Continuous edgeDiskParameter := by
  apply Continuous.subtype_mk
  fun_prop

private def graphBouquetMapInterior (T : Set (Cell X 1)) (e : Cell X 1)
    (x : openCell X 1 e) : WeakBouquet {e : Cell X 1 // e ∉ T} :=
  if he : e ∈ T then bouquetVertex _ else
    bouquetLoop ⟨e, he⟩
      (edgeDiskParameter (interiorInclusion 1 ((cellHomeomorph 1 e).symm x)))

private lemma graphBouquetMapInterior_congr (T : Set (Cell X 1))
    {e f : Cell X 1} {x : X} (he : x ∈ openCell X 1 e)
    (hf : x ∈ openCell X 1 f) (hef : e = f) :
    graphBouquetMapInterior T e ⟨x, he⟩ = graphBouquetMapInterior T f ⟨x, hf⟩ := by
  subst f
  rfl

/-- Collapse every selected edge and all vertices, retaining the coordinates
and labels of the remaining open edges. -/
def graphBouquetMap (h : IsGraph X) (T : Set (Cell X 1)) (x : X) :
    WeakBouquet {e : Cell X 1 // e ∉ T} :=
  if hv : x ∈ skeletonLT X 1 then bouquetVertex _ else
    graphBouquetMapInterior T ((graph_point_cases h x).resolve_left hv).choose
      ⟨x, ((graph_point_cases h x).resolve_left hv).choose_spec⟩

@[simp] lemma graphBouquetMap_vertex (h : IsGraph X) (T : Set (Cell X 1))
    (v : GraphVertex X) : graphBouquetMap h T v.val = bouquetVertex _ := by
  simp [graphBouquetMap, v.property]

lemma graphBouquetMap_interior (h : IsGraph X) (T : Set (Cell X 1))
    (e : Cell X 1) (y : OpenDisk 1) :
    graphBouquetMap h T (interiorMap X 1 e y) =
      if he : e ∈ T then bouquetVertex _ else
        bouquetLoop ⟨e, he⟩ (edgeDiskParameter (interiorInclusion 1 y)) := by
  classical
  have hv : interiorMap X 1 e y ∉ skeletonLT X 1 :=
    fun hv => vertex_not_in_open_edge hv e ⟨y, rfl⟩
  have heq : ((graph_point_cases h (interiorMap X 1 e y)).resolve_left hv).choose = e := by
    have hc := ((graph_point_cases h (interiorMap X 1 e y)).resolve_left hv).choose_spec
    exact eq_of_heq (Sigma.mk.inj_iff.mp (cell_unique hc ⟨y, rfl⟩)).2
  simp only [graphBouquetMap, dite_eq_right hv]
  trans graphBouquetMapInterior T e ⟨interiorMap X 1 e y, ⟨y, rfl⟩⟩
  · exact graphBouquetMapInterior_congr T _ _ heq
  unfold graphBouquetMapInterior
  have hy : (cellHomeomorph 1 e).symm
      ⟨interiorMap X 1 e y, ⟨y, rfl⟩⟩ = y :=
    (cellHomeomorph 1 e).symm_apply_apply y
  rw [hy]

lemma graphBouquetMap_characteristic (h : IsGraph X) (T : Set (Cell X 1))
    (e : Cell X 1) (z : Disk 1) :
    graphBouquetMap h T (characteristic X 1 e z) =
      if he : e ∈ T then bouquetVertex _ else
        bouquetLoop ⟨e, he⟩ (edgeDiskParameter z) := by
  rcases diskOne_cases z with ⟨y, rfl⟩ | rfl | rfl
  · exact graphBouquetMap_interior h T e y
  · rw [edgeDiskParameter_point]
    change graphBouquetMap h T ((graphEndpoints X).source e).val = _
    rw [graphBouquetMap_vertex]
    split_ifs
    · rfl
    · exact (bouquetLoop _).source.symm
  · rw [edgeDiskParameter_point]
    change graphBouquetMap h T ((graphEndpoints X).target e).val = _
    rw [graphBouquetMap_vertex]
    split_ifs
    · rfl
    · exact (bouquetLoop _).target.symm

/-- Continuity in the weak topology, including at vertices of infinite valence. -/
lemma graphBouquetMap_continuous (h : IsGraph X) (T : Set (Cell X 1)) :
    Continuous (graphBouquetMap h T) := by
  apply (continuityTest _).mpr
  intro n c
  cases n with
  | zero => exact continuous_of_const fun a b => congrArg _ (Subsingleton.elim a b)
  | succ n =>
    cases n with
    | zero =>
      have he : graphBouquetMap h T ∘ characteristic X 1 c =
          fun z => if hc : c ∈ T then bouquetVertex _ else
            bouquetLoop ⟨c, hc⟩ (edgeDiskParameter z) :=
        funext (graphBouquetMap_characteristic h T c)
      rw [he]
      split_ifs
      · exact continuous_const
      · exact (bouquetLoop _).continuous.comp edgeDiskParameter_continuous
    | succ n =>
      haveI := h (n + 2) (by omega)
      exact isEmptyElim c

lemma graphBouquetMap_tree (h : IsGraph X) (T : Set (Cell X 1))
    {x : X} (hx : x ∈ graphTreeCarrier T) :
    graphBouquetMap h T x = bouquetVertex _ := by
  rcases hx with hv | hxE
  · exact graphBouquetMap_vertex h T ⟨x, hv⟩
  · obtain ⟨e, he, y, rfl⟩ := mem_iUnion₂.mp hxE
    rw [graphBouquetMap_interior, dite_eq_left he]

end P202.Topology

namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]
attribute [local instance] Classical.propDecidable

/-- The continuous map on the actual graph quotient, not merely a bijection
of edge labels. -/
def graphCollapseToBouquet (h : IsGraph X) (T : Set (Cell X 1)) :
    C(Collapse (graphSubcomplex T), WeakBouquet {e : Cell X 1 // e ∉ T}) := by
  let f := graphBouquetMap h T
  have hf : ∀ a b, (collapseSetoid (graphSubcomplex T)).r a b → f a = f b := by
    intro a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · rfl
    · rw [graphSubcomplex_carrier] at ha hb
      exact (graphBouquetMap_tree h T ha).trans (graphBouquetMap_tree h T hb).symm
  exact ⟨Quotient.lift f hf, (graphBouquetMap_continuous h T).quotient_lift hf⟩

@[simp] lemma graphCollapseToBouquet_projection (h : IsGraph X)
    (T : Set (Cell X 1)) (x : X) :
    graphCollapseToBouquet h T (collapseProjection (graphSubcomplex T) x) =
      graphBouquetMap h T x := rfl

/-- Map the vertex to a chosen root and each oriented bouquet edge to the
image of its original characteristic edge. -/
def graphBouquetInverseRaw (T : Set (Cell X 1)) (r : GraphVertex X) :
    BouquetPresentation {e : Cell X 1 // e ∉ T} → Collapse (graphSubcomplex T) :=
  Sum.elim (fun _ => collapseProjection (graphSubcomplex T) r.val)
    (fun p => collapseProjection (graphSubcomplex T) (graphEdgePath p.1.val p.2))

lemma graphBouquetInverseRaw_continuous (T : Set (Cell X 1)) (r : GraphVertex X) :
    Continuous (graphBouquetInverseRaw T r) := by
  apply continuous_sum_dom.mpr
  refine ⟨continuous_const, continuous_sigma fun e => ?_⟩
  exact (collapseProjection _).continuous.comp (graphEdgePath e.val).continuous

lemma graphCollapseProjection_vertex_eq (T : Set (Cell X 1)) (v w : GraphVertex X) :
    collapseProjection (graphSubcomplex T) v.val =
      collapseProjection (graphSubcomplex T) w.val := by
  apply Quotient.sound
  right
  rw [graphSubcomplex_carrier]
  exact ⟨Or.inl v.property, Or.inl w.property⟩

lemma graphBouquetInverseRaw_vertex (T : Set (Cell X 1)) (r : GraphVertex X)
    (a : BouquetPresentation {e : Cell X 1 // e ∉ T}) (ha : bouquetVertexLocus a) :
    graphBouquetInverseRaw T r a = collapseProjection (graphSubcomplex T) r.val := by
  rcases a with _ | ⟨e, t⟩
  · rfl
  · rcases ha with rfl | rfl
    · change collapseProjection _ (graphEdgePath e.val 0) = _
      rw [Path.source]
      exact graphCollapseProjection_vertex_eq T _ _
    · change collapseProjection _ (graphEdgePath e.val 1) = _
      rw [Path.target]
      exact graphCollapseProjection_vertex_eq T _ _

def graphBouquetToCollapse (T : Set (Cell X 1)) (r : GraphVertex X) :
    C(WeakBouquet {e : Cell X 1 // e ∉ T}, Collapse (graphSubcomplex T)) := by
  have hf : ∀ a b, (bouquetSetoid {e : Cell X 1 // e ∉ T}).r a b →
      graphBouquetInverseRaw T r a = graphBouquetInverseRaw T r b := by
    intro a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · rfl
    · exact (graphBouquetInverseRaw_vertex T r a ha).trans
        (graphBouquetInverseRaw_vertex T r b hb).symm
  exact ⟨Quotient.lift _ hf, (graphBouquetInverseRaw_continuous T r).quotient_lift hf⟩

@[simp] lemma graphBouquetToCollapse_vertex (T : Set (Cell X 1)) (r : GraphVertex X) :
    graphBouquetToCollapse T r (bouquetVertex _) =
      collapseProjection (graphSubcomplex T) r.val := rfl

@[simp] lemma graphBouquetToCollapse_loop (T : Set (Cell X 1)) (r : GraphVertex X)
    (e : {e : Cell X 1 // e ∉ T}) (t : unitInterval) :
    graphBouquetToCollapse T r (bouquetLoop e t) =
      collapseProjection (graphSubcomplex T) (graphEdgePath e.val t) := rfl

lemma graph_bouquet_rightInverse (h : IsGraph X) (T : Set (Cell X 1))
    (r : GraphVertex X) :
    Function.RightInverse (graphBouquetToCollapse T r) (graphCollapseToBouquet h T) := by
  intro z
  induction z using Quotient.inductionOn with
  | h a =>
    rcases a with _ | ⟨e, t⟩
    · exact graphBouquetMap_vertex h T r
    · change graphBouquetMap h T (characteristic X 1 e.val (edgeDiskPoint t)) = _
      rw [graphBouquetMap_characteristic, dite_eq_right e.property, edgeDiskParameter_point]
      rfl

lemma graph_bouquet_leftInverse (h : IsGraph X) (T : Set (Cell X 1))
    (r : GraphVertex X) :
    Function.LeftInverse (graphBouquetToCollapse T r) (graphCollapseToBouquet h T) := by
  intro z
  induction z using Quotient.inductionOn with
  | h x =>
    change graphBouquetToCollapse T r (graphBouquetMap h T x) =
      collapseProjection (graphSubcomplex T) x
    rcases graph_point_cases h x with hv | ⟨e, y, rfl⟩
    · rw [graphBouquetMap_vertex h T ⟨x, hv⟩, graphBouquetToCollapse_vertex]
      exact graphCollapseProjection_vertex_eq T r ⟨x, hv⟩
    · rw [graphBouquetMap_interior]
      split_ifs with he
      · rw [graphBouquetToCollapse_vertex]
        apply Quotient.sound
        right
        rw [graphSubcomplex_carrier]
        exact ⟨Or.inl r.property, Or.inr (mem_iUnion₂.mpr ⟨e, he, y, rfl⟩)⟩
      · rw [graphBouquetToCollapse_loop]
        change collapseProjection _ (characteristic X 1 e
          (edgeDiskPoint (edgeDiskParameter (interiorInclusion 1 y)))) = _
        rw [edgeDiskPoint_parameter]
        rfl

/-- Collapsing all vertices and the selected edges gives exactly the weak
bouquet on the complementary original edge labels. This holds without
finiteness, local finiteness, or a prior contractibility assumption. -/
def graphCollapseBouquetHomeomorph (h : IsGraph X) (T : Set (Cell X 1))
    (r : GraphVertex X) :
    Collapse (graphSubcomplex T) ≃ₜ WeakBouquet {e : Cell X 1 // e ∉ T} where
  toFun := graphCollapseToBouquet h T
  invFun := graphBouquetToCollapse T r
  left_inv := graph_bouquet_leftInverse h T r
  right_inv := graph_bouquet_rightInverse h T r
  continuous_toFun := (graphCollapseToBouquet h T).continuous
  continuous_invFun := (graphBouquetToCollapse T r).continuous

end P202.Topology

namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

/-- The continuous graph-to-bouquet map, with its root as basepoint. -/
def graphBouquetPointedMap (h : IsGraph X) (T : Set (Cell X 1)) (r : GraphVertex X) :
    PointedMap X (WeakBouquet {e : Cell X 1 // e ∉ T}) r.val (bouquetVertex _) :=
  ⟨⟨graphBouquetMap h T, graphBouquetMap_continuous h T⟩, graphBouquetMap_vertex h T r⟩

/-- The map used in the quotient identification is a homotopy equivalence
when the actual selected subcomplex is contractible. -/
theorem graph_bouquet_homotopyEquivalence (h : IsGraph X) (T : Set (Cell X 1))
    (r : GraphVertex X) (hc : ContractibleSpace ↥(graphTreeCarrier T)) :
    ∃ e : X ≃ₕ WeakBouquet {e : Cell X 1 // e ∉ T},
      e.toFun = (graphBouquetPointedMap h T r).map := by
  letI := hc
  have hcA : ContractibleSpace (graphSubcomplex T) :=
    (Homeomorph.setCongr (graphSubcomplex_carrier T)).contractibleSpace
  obtain ⟨q, hq⟩ := graph_tree_collapse T ⟨r⟩ hcA
  refine ⟨q.trans (graphCollapseBouquetHomeomorph h T r).toHomotopyEquiv, ?_⟩
  ext x
  change graphCollapseToBouquet h T (q.toFun x) = graphBouquetMap h T x
  rw [hq]
  rfl

/-- The group homomorphism induced by a homotopy equivalence is bijective.
The proof passes through the fundamental groupoid equivalence and the explicit
opposite bridge, so it respects the source's path product convention. -/
theorem homotopyEquiv_induced_bijective {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₕ B)
    (x : A) (y : B) (hy : e.toFun x = y) :
    Function.Bijective (PointedMap.induced (⟨e.toFun, hy⟩ : PointedMap A B x y)) := by
  subst y
  let Ψ : Pi1 A x ≃* Pi1 B (e.toFun x) := oppositeEquiv
    ((FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
      (FundamentalGroupoid.mk x))
  have hf : (⟨e.toFun, rfl⟩ : PointedMap A B x (e.toFun x)).induced = Ψ.toMonoidHom := by
    ext a
    apply pathClass_injective
    rw [induced_pathClass, Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  rw [hf]
  exact Ψ.bijective

lemma graphBouquetPointedMap_induced_bijective (h : IsGraph X)
    (T : Set (Cell X 1)) (r : GraphVertex X)
    (hc : ContractibleSpace ↥(graphTreeCarrier T)) :
    Function.Bijective (graphBouquetPointedMap h T r).induced := by
  obtain ⟨e, he⟩ := graph_bouquet_homotopyEquivalence h T r hc
  have hp : e.toFun r.val = bouquetVertex _ := by
    rw [he]
    exact (graphBouquetPointedMap h T r).point
  have hm : (⟨e.toFun, hp⟩ : PointedMap X _ r.val (bouquetVertex _)) =
      graphBouquetPointedMap h T r := by
    have extMap : ∀ (f g : PointedMap X
        (WeakBouquet {e : Cell X 1 // e ∉ T}) r.val (bouquetVertex _)),
        f.map = g.map → f = g := by
      rintro ⟨f, hf⟩ ⟨g, hg⟩ hfg
      cases hfg
      rfl
    exact extMap _ _ he
  rw [← hm]
  exact homotopyEquiv_induced_bijective e _ _ hp

/-- The quotient sends the actual tree-joined edge loop to its correspondingly
labelled and oriented bouquet loop. No assumption about a free-group
calculation is used here. -/
theorem graphBouquetPointedMap_generator (h : IsGraph X)
    (T : Set (Cell X 1)) (r : GraphVertex X)
    (p : ∀ v : GraphVertex X, Path r.val v.val)
    (hp : ∀ v t, p v t ∈ graphTreeCarrier T)
    (e : {e : Cell X 1 // e ∉ T}) :
    (graphBouquetPointedMap h T r).induced
      (loopClass (((p ((graphEndpoints X).source e.val)).trans (graphEdgePath e.val)).trans
        (p ((graphEndpoints X).target e.val)).symm)) =
      loopClass (bouquetLoop e) := by
  let F := graphBouquetPointedMap h T r
  have hv (v : GraphVertex X) : F.map v.val = bouquetVertex _ :=
    graphBouquetMap_vertex h T v
  have hp' (v : GraphVertex X) :
      ((p v).map F.map.continuous).cast (hv r).symm (hv v).symm =
        Path.refl (bouquetVertex {e : Cell X 1 // e ∉ T}) := by
    ext t
    exact graphBouquetMap_tree h T (hp v t)
  have he' : ((graphEdgePath e.val).map F.map.continuous).cast
      (hv ((graphEndpoints X).source e.val)).symm
      (hv ((graphEndpoints X).target e.val)).symm = bouquetLoop e := by
    ext t
    change graphBouquetMap h T (characteristic X 1 e.val (edgeDiskPoint t)) = _
    rw [graphBouquetMap_characteristic, dite_eq_right e.property, edgeDiskParameter_point]
  rw [inducedFormula]
  apply pathClass_injective
  simp only [pathClass_loopClass]
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm,
    Path.cast_trans _ _ (hv r).symm (hv ((graphEndpoints X).target e.val)).symm (hv r).symm,
    Path.cast_trans _ _ (hv r).symm (hv ((graphEndpoints X).source e.val)).symm
      (hv ((graphEndpoints X).target e.val)).symm,
    Path.cast_symm, hp', he', hp']
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl,
    Path.refl_symm,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl]

end P202.Topology

namespace P202.Topology

/-- Assembly of the original graph assertion from the two geometric results
still needed in this file. The hypotheses are independent full propositions;
this auxiliary theorem is not the unconditional graph-group theorem. -/
theorem graphFundamentalGroup_of_treeContractibility_of_bouquetFreeGroup
    (tree : P202Specs.Topology.GraphFundamentalGroup.treeContractibility.{u})
    (bouquet : P202Specs.Topology.GraphFundamentalGroup.bouquetFreeGroup.{u}) :
    P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u} := by
  intro X _ _ hg hconn x
  letI := hconn
  obtain ⟨T, hT, hmax⟩ := graph_spanningTree_exists hg
  let r : GraphVertex X := Classical.choice hT.2.nonempty
  obtain ⟨p, hp⟩ := graph_tree_paths hT r
  letI := graph_pathConnected hg
  obtain ⟨d⟩ := PathConnectedSpace.joined x r.val
  obtain ⟨Φ, hΦ⟩ := bouquet {e : Cell X 1 // e ∉ T}
  let Ψ : Pi1 X r.val ≃* Pi1 (WeakBouquet {e : Cell X 1 // e ∉ T}) (bouquetVertex _) :=
    MulEquiv.ofBijective (graphBouquetPointedMap hg T r).induced
      (graphBouquetPointedMap_induced_bijective hg T r (tree T hT))
  refine ⟨T, hT, hmax, r, d, p, hp, (Φ.trans Ψ.symm).trans (changeBasepoint d), ?_⟩
  intro e
  change changeBasepoint d (Ψ.symm (Φ (FreeGroup.of e))) = _
  have hroot : Ψ.symm (Φ (FreeGroup.of e)) =
      loopClass (((p ((graphEndpoints X).source e.val)).trans (graphEdgePath e.val)).trans
        (p ((graphEndpoints X).target e.val)).symm) := by
    apply Ψ.injective
    rw [Ψ.apply_symm_apply, hΦ e]
    exact (graphBouquetPointedMap_generator hg T r p hp e).symm
  rw [hroot]
  apply pathClass_injective
  simp only [changeBasepoint_pathClass, pathClass_loopClass,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]

end P202.Topology

namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

/-- The sum of selected characteristic disks with their actual carrier map. -/
def subcomplexDiskProjection (A : Subcomplex X) :
    (Σ n, Σ _ : A.cells n, Disk n) → A := fun p =>
  ⟨characteristic X p.1 p.2.1.val p.2.2, by
    apply A.contains_closures p.1 p.2.1.val p.2.1.property
    rw [closureOpenCell]
    exact ⟨p.2.2, rfl⟩⟩

/-- The characteristic disks determine the actual subspace topology of every
subcomplex, without a local finiteness hypothesis. -/
theorem subcomplexDiskProjection_quotient (A : Subcomplex X) :
    IsQuotientMap (subcomplexDiskProjection A) := by
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · intro x
    obtain ⟨n, c, y, hy⟩ := mem_iUnion₂.mp x.property
    exact ⟨⟨n, c, interiorInclusion n y⟩, Subtype.ext hy⟩
  · intro S
    let B : Set X := Subtype.val '' S
    have hB : B ⊆ A.carrier := by
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    have hpre : (Subtype.val : A → X) ⁻¹' B = S := by
      ext x
      simp [B]
    rw [← hpre, subcomplexWeakTopology A B hB,
      isClosed_sigma_iff]
    apply forall_congr'
    intro n
    rw [isClosed_sigma_iff]
    constructor
    · intro h c
      exact h c.val c.property
    · intro h c hc
      exact h ⟨c,hc⟩

/-- A mapping test for the topology on an arbitrary subcomplex. -/
theorem subcomplex_continuityTest (A : Subcomplex X) {Y : Type v}
    [TopologicalSpace Y] (f : A → Y) :
    Continuous f ↔ ∀ n (c : A.cells n),
      Continuous (fun z : Disk n => f (subcomplexDiskProjection A ⟨n,c,z⟩)) := by
  rw [(subcomplexDiskProjection_quotient A).continuous_iff,
    continuous_sigma_iff]
  exact forall_congr' fun n => continuous_sigma_iff

/-- Joint continuity on the actual product with the interval follows from
joint continuity on each selected closed cell. -/
theorem subcomplex_homotopyContinuityTest (A : Subcomplex X) {Y : Type v}
    [TopologicalSpace Y] (H : A × unitInterval → Y) :
    Continuous H ↔ ∀ n (c : A.cells n), Continuous (fun z : Disk n × unitInterval =>
      H (subcomplexDiskProjection A ⟨n,c,z.1⟩, z.2)) := by
  constructor
  · intro h n c
    apply h.comp
    exact ((subcomplexDiskProjection_quotient A).continuous.comp
      (continuous_sigmaMk.comp continuous_sigmaMk)).prodMap continuous_id
  · intro h
    apply (quotientProductInterval _ (subcomplexDiskProjection_quotient A)).continuous_iff.mpr
    let e := (Homeomorph.sigmaProdDistrib
      (X := fun n => Σ _ : A.cells n, Disk n) (Y := unitInterval))
    apply e.symm.isQuotientMap.continuous_iff.mpr
    apply continuous_sigma
    intro n
    let e' := (Homeomorph.sigmaProdDistrib (X := fun _ : A.cells n => Disk n)
      (Y := unitInterval))
    apply e'.symm.isQuotientMap.continuous_iff.mpr
    exact continuous_sigma (h n)
end P202.Topology

namespace P202.Topology
variable {Y : Type v} [TopologicalSpace Y] {a b r : Y}

/-- A coherent square that moves a whole oriented edge toward its near
endpoint and then follows that endpoint's already chosen path to the root. -/
def rootedEdgeSquare (e : Path a b) (q : Path a r) : C(unitInterval × unitInterval, Y) where
  toFun z := if (z.1 : ℝ) * (1 + (z.2 : ℝ)) ≤ (z.2 : ℝ) then
      e.extend ((z.2 : ℝ) - (z.1 : ℝ) * (1 + (z.2 : ℝ)))
    else q.extend ((z.1 : ℝ) * (1 + (z.2 : ℝ)) - (z.2 : ℝ))
  continuous_toFun := by
    apply Continuous.if_le (e.continuous_extend.comp (by fun_prop))
      (q.continuous_extend.comp (by fun_prop)) (by fun_prop) (by fun_prop)
    intro z hz
    dsimp only [Function.comp_apply]
    rw [show (z.2 : ℝ) - (z.1 : ℝ) * (1 + (z.2 : ℝ)) = 0 by linarith,
      show (z.1 : ℝ) * (1 + (z.2 : ℝ)) - (z.2 : ℝ) = 0 by linarith,
      e.extend_zero, q.extend_zero]

@[simp] lemma rootedEdgeSquare_zero (e : Path a b) (q : Path a r) (t : unitInterval) :
    rootedEdgeSquare e q (0,t) = e t := by
  simp only [rootedEdgeSquare, ContinuousMap.coe_mk, Set.Icc.coe_zero,
    zero_mul, sub_zero]
  rw [ite_eq_left t.property.1, e.extend_extends']

@[simp] lemma rootedEdgeSquare_one (e : Path a b) (q : Path a r) (t : unitInterval) :
    rootedEdgeSquare e q (1,t) = r := by
  simp only [rootedEdgeSquare, ContinuousMap.coe_mk, Set.Icc.coe_one, one_mul]
  rw [ite_eq_right (by linarith : ¬1 + (t : ℝ) ≤ (t : ℝ)),
    show 1 + (t : ℝ) - (t : ℝ) = 1 by ring, q.extend_one]

@[simp] lemma rootedEdgeSquare_left (e : Path a b) (q : Path a r) (s : unitInterval) :
    rootedEdgeSquare e q (s,0) = q s := by
  simp only [rootedEdgeSquare, ContinuousMap.coe_mk, Set.Icc.coe_zero,
    add_zero, mul_one, sub_zero]
  split_ifs with hs
  · have hz : s = 0 := Subtype.ext (le_antisymm hs s.property.1)
    subst s
    simp [e.extend_zero, q.source]
  · exact q.extend_extends' s

@[simp] lemma rootedEdgeSquare_right (e : Path a b) (q : Path a r) (s : unitInterval) :
    rootedEdgeSquare e q (s,1) = (e.symm.trans q) s := by
  rw [← (e.symm.trans q).extend_extends' s]
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · rw [Path.extend_trans_of_le_half _ _ hs, Path.extend_symm_apply]
    dsimp only [rootedEdgeSquare, ContinuousMap.coe_mk, Set.Icc.coe_one]
    rw [ite_eq_left (by linarith : (s : ℝ) * (1 + 1) ≤ 1)]
    congr 1
    ring
  · rw [Path.extend_trans_of_half_le _ _ (le_of_lt (lt_of_not_ge hs))]
    dsimp only [rootedEdgeSquare, ContinuousMap.coe_mk, Set.Icc.coe_one]
    rw [ite_eq_right (by linarith : ¬(s : ℝ) * (1 + 1) ≤ 1)]
    congr 1
    ring
end P202.Topology

namespace P202.Topology.Bouquet
open P202.Cellular P202Specs.Topology

lemma loop_eq_vertex_iff {E : Type u} (e : E) (t : unitInterval) :
    bouquetLoop e t = bouquetVertex E ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    rcases Quotient.exact h with h | h
    · cases h
    · exact h.1
  · intro h
    exact Quotient.sound (Or.inr ⟨h, trivial⟩)

lemma loop_eq_loop_iff {E : Type u} (e f : E) (s t : unitInterval)
    (hs : s ≠ 0 ∧ s ≠ 1) :
    bouquetLoop e s = bouquetLoop f t ↔ e = f ∧ s = t := by
  constructor
  · intro h
    rcases Quotient.exact h with h | h
    · cases h
      exact ⟨rfl, rfl⟩
    · exact ((h.1.elim hs.1 hs.2)).elim
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The actual open edge, with its endpoints excluded. -/
def openEdge {E : Type u} (e : E) : Set (WeakBouquet E) :=
  bouquetLoop e '' {t | t ≠ 0 ∧ t ≠ 1}

lemma vertex_not_mem_openEdge {E : Type u} (e : E) :
    bouquetVertex E ∉ openEdge e := by
  rintro ⟨t, ht, he⟩
  exact (loop_eq_vertex_iff e t).mp he |>.elim ht.1 ht.2

lemma openEdge_unique {E : Type u} {e f : E} {x : WeakBouquet E}
    (he : x ∈ openEdge e) (hf : x ∈ openEdge f) : e = f := by
  obtain ⟨s, hs, rfl⟩ := he
  obtain ⟨t, ht, heq⟩ := hf
  exact ((loop_eq_loop_iff e f s t hs).mp heq.symm).1

lemma closed_of_openEdge_subsingleton {E : Type u} (S : Set (WeakBouquet E))
    (hv : bouquetVertex E ∉ S)
    (hS : ∀ e : E, (S ∩ openEdge e).Subsingleton) : IsClosed S := by
  have hq : IsQuotientMap (Quotient.mk (bouquetSetoid E)) :=
    isQuotientMap_quotient_mk'
  apply hq.isClosed_preimage.mp
  rw [isClosed_sum_iff]
  constructor
  · have he : Sum.inl ⁻¹' (Quotient.mk (bouquetSetoid E) ⁻¹' S) = (∅ : Set Unit) := by
      ext x
      cases x
      simp only [mem_preimage, Set.mem_empty_iff_false, iff_false]
      exact hv
    rw [he]
    exact isClosed_empty
  · rw [isClosed_sigma_iff]
    intro e
    have hs : ((fun t : unitInterval => bouquetLoop e t) ⁻¹' S).Subsingleton := by
      intro s hs t ht
      have hs' : s ≠ 0 ∧ s ≠ 1 := by
        constructor <;> intro h <;> subst_vars
        · exact hv (by simpa using hs)
        · exact hv (by simpa using hs)
      have ht' : t ≠ 0 ∧ t ≠ 1 := by
        constructor <;> intro h <;> subst_vars
        · exact hv (by simpa using ht)
        · exact hv (by simpa using ht)
      have hh := hS e ⟨hs, ⟨s, hs', rfl⟩⟩ ⟨ht, ⟨t, ht', rfl⟩⟩
      exact ((loop_eq_loop_iff e e s t hs').mp hh).2
    exact hs.finite.isClosed

/-- A compact subset of the weak bouquet meets only finitely many open edges. -/
theorem compact_finite_edges {E : Type u} (K : Set (WeakBouquet E))
    (hK : IsCompact K) :
    {e : E | (K ∩ openEdge e).Nonempty}.Finite := by
  classical
  let M := {e : E // (K ∩ openEdge e).Nonempty}
  let f : M → WeakBouquet E := fun e => e.2.choose
  have hfK : ∀ e, f e ∈ K := fun e => e.2.choose_spec.1
  have hfe : ∀ e, f e ∈ openEdge e.1 := fun e => e.2.choose_spec.2
  have hfinj : Function.Injective f := by
    intro e d h
    apply Subtype.ext
    exact openEdge_unique (hfe e) (h ▸ hfe d)
  have hclosed : ∀ T ⊆ range f, IsClosed T := by
    intro T hT
    apply closed_of_openEdge_subsingleton T
    · intro hv
      obtain ⟨e, he⟩ := hT hv
      exact vertex_not_mem_openEdge e.1 (he ▸ hfe e)
    · intro e x hx y hy
      obtain ⟨d, rfl⟩ := hT hx.1
      obtain ⟨c, rfl⟩ := hT hy.1
      have hd := openEdge_unique (hfe d) hx.2
      have hc := openEdge_unique (hfe c) hy.2
      exact congrArg f (Subtype.ext (hd.trans hc.symm))
  have hcompact : IsCompact (range f) :=
    hK.of_isClosed_subset (hclosed _ Subset.rfl) (by rintro x ⟨e, rfl⟩; exact hfK e)
  have hdiscrete : IsDiscrete (range f) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro T hT
    exact ⟨T, hclosed T hT, inter_eq_left.mpr hT⟩
  have hrange := hcompact.finite hdiscrete
  have hM : Finite M := (Set.finite_range_iff hfinj).mp hrange
  exact Set.finite_coe_iff.mp hM

/-- Maps from the actual weak quotient bouquet are determined by based edge loops. -/
def desc {E : Type u} {Y : Type v} [TopologicalSpace Y]
    (y : Y) (a : E → Path y y) : PointedMap (WeakBouquet E) Y (bouquetVertex E) y := by
  let raw : BouquetPresentation E → Y :=
    Sum.elim (fun _ => y) (fun p => a p.1 p.2)
  have hv : ∀ p, bouquetVertexLocus p → raw p = y := by
    rintro (_ | ⟨e,t⟩) hp
    · rfl
    · rcases hp with rfl | rfl
      · exact (a e).source
      · exact (a e).target
  have hr : ∀ p q, (bouquetSetoid E).r p q → raw p = raw q := by
    intro p q h
    rcases h with rfl | ⟨hp,hq⟩
    · rfl
    · exact (hv p hp).trans (hv q hq).symm
  have hc : Continuous raw := continuous_sum_dom.mpr
    ⟨continuous_const, continuous_sigma fun e => (a e).continuous⟩
  exact ⟨⟨Quotient.lift raw hr, hc.quotient_lift hr⟩, rfl⟩

@[simp] lemma desc_vertex {E : Type u} {Y : Type v} [TopologicalSpace Y]
    (y : Y) (a : E → Path y y) : (desc y a).map (bouquetVertex E) = y := rfl

@[simp] lemma desc_loop {E : Type u} {Y : Type v} [TopologicalSpace Y]
    (y : Y) (a : E → Path y y) (e : E) (t : unitInterval) :
    (desc y a).map (bouquetLoop e t) = a e t := rfl

lemma desc_induced {E : Type u} {Y : Type v} [TopologicalSpace Y]
    (y : Y) (a : E → Path y y) (e : E) :
    (desc y a).induced (loopClass (bouquetLoop e)) = loopClass (a e) := by
  rw [P202.Topology.inducedFormula]
  congr 1

/-- The natural map on bouquets sends the oriented edge e to the oriented edge f(e). -/
def map {E : Type u} {F : Type v} (f : E → F) :
    PointedMap (WeakBouquet E) (WeakBouquet F) (bouquetVertex E) (bouquetVertex F) :=
  desc (bouquetVertex F) (fun e => bouquetLoop (f e))

@[simp] lemma map_vertex {E : Type u} {F : Type v} (f : E → F) :
    (map f).map (bouquetVertex E) = bouquetVertex F := rfl

@[simp] lemma map_loop {E : Type u} {F : Type v} (f : E → F) (e : E) (t : unitInterval) :
    (map f).map (bouquetLoop e t) = bouquetLoop (f e) t := rfl

@[simp] lemma map_induced {E : Type u} {F : Type v} (f : E → F) (e : E) :
    (map f).induced (loopClass (bouquetLoop e)) = loopClass (bouquetLoop (f e)) :=
  desc_induced _ _ _

/-- Collapse all the edges outside S to the bouquet vertex. -/
def retract {E : Type u} (S : Set E) :
    PointedMap (WeakBouquet E) (WeakBouquet S) (bouquetVertex E) (bouquetVertex S) := by
  classical
  exact desc (bouquetVertex S)
    (fun e => if h : e ∈ S then bouquetLoop ⟨e,h⟩ else Path.refl (bouquetVertex S))

@[simp] lemma retract_vertex {E : Type u} (S : Set E) :
    (retract S).map (bouquetVertex E) = bouquetVertex S := rfl

@[simp] lemma retract_loop {E : Type u} (S : Set E) (e : S) (t : unitInterval) :
    (retract S).map (bouquetLoop e.val t) = bouquetLoop e t := by
  classical
  simp only [retract, desc_loop, dite_eq_left e.property]

private lemma pointedMap_ext {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    {f g : PointedMap X Y x y} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

lemma retract_map {E : Type u} (S : Set E) :
    (retract S).comp (map (Subtype.val : S → E)) = PointedMap.id (bouquetVertex S) := by
  apply pointedMap_ext
  ext x
  induction x using Quotient.inductionOn with
  | h a =>
    rcases a with _ | ⟨e,t⟩
    · rfl
    · exact retract_loop S e t

/-- A finite subbouquet's inclusion is injective on the fundamental group;
in fact the statement holds for every subset. -/
theorem map_subtype_induced_injective {E : Type u} (S : Set E) :
    Function.Injective (map (Subtype.val : S → E)).induced := by
  have h : (retract S).induced.comp (map (Subtype.val : S → E)).induced =
      MonoidHom.id _ := by
    rw [← P202.Topology.induced_comp, retract_map, P202.Topology.induced_id]
  intro a b hab
  have hh := congrArg (retract S).induced hab
  simpa only [← MonoidHom.comp_apply, h, MonoidHom.id_apply] using hh

lemma map_retract_of_mem {E : Type u} (S : Set E) (x : WeakBouquet E)
    (hx : x = bouquetVertex E ∨ ∃ e ∈ S, x ∈ openEdge e) :
    (map (Subtype.val : S → E)).map ((retract S).map x) = x := by
  rcases hx with rfl | ⟨e, he, t, ht, rfl⟩
  · rfl
  · rw [retract_loop S ⟨e,he⟩, map_loop]

lemma vertex_or_openEdge {E : Type u} (x : WeakBouquet E) :
    x = bouquetVertex E ∨ ∃ e, x ∈ openEdge e := by
  induction x using Quotient.inductionOn with
  | h a =>
    rcases a with _ | ⟨e,t⟩
    · exact Or.inl rfl
    · by_cases h : t = 0 ∨ t = 1
      · exact Or.inl ((loop_eq_vertex_iff e t).mpr h)
      · exact Or.inr ⟨e, t, not_or.mp h, rfl⟩

/-- Every continuous map with compact domain factors through a finite bouquet
via the continuous retraction, with equality of actual maps. -/
theorem compact_range_finite_support {E : Type u} {K : Type v} [TopologicalSpace K]
    [CompactSpace K] (f : C(K, WeakBouquet E)) :
    ∃ S : Finset E, ∀ k,
      (map (Subtype.val : S → E)).map ((retract (S : Set E)).map (f k)) = f k := by
  classical
  let A := {e : E | (range f ∩ openEdge e).Nonempty}
  have hA : A.Finite := compact_finite_edges _ (isCompact_range f.continuous)
  refine ⟨hA.toFinset, fun k => map_retract_of_mem _ _ ?_⟩
  rcases vertex_or_openEdge (f k) with h | ⟨e,he⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hA.mem_toFinset.mpr ⟨f k, ⟨⟨k,rfl⟩,he⟩⟩, he⟩

/-- Every loop class comes from a finite subbouquet, through the actual
inclusion and with the prescribed basepoint. -/
theorem pi1_finite_support {E : Type u} (g : Pi1 (WeakBouquet E) (bouquetVertex E)) :
    ∃ (S : Finset E) (gS : Pi1 (WeakBouquet S) (bouquetVertex S)),
      (map (Subtype.val : S → E)).induced gS = g := by
  obtain ⟨a,rfl⟩ := P202.Topology.loopClass_surjective g
  obtain ⟨S,hS⟩ := compact_range_finite_support a.toContinuousMap
  refine ⟨S,(retract (S : Set E)).induced (loopClass a),?_⟩
  rw [P202.Topology.inducedFormula, P202.Topology.inducedFormula]
  congr 1
  ext t
  exact hS t

/-- The infinite weak-bouquet theorem follows from the finite theorem. This
proves the entire infinite-support passage directly from the quotient topology;
no local finiteness, metrizability or CW instance is required. -/
theorem bouquetFreeGroup_of_finite
    (hfinite : ∀ (E : Type u) [Finite E],
      ∃ Φ : FreeGroup E ≃* Pi1 (WeakBouquet E) (bouquetVertex E),
        ∀ e : E, Φ (FreeGroup.of e) = loopClass (bouquetLoop e)) :
    P202Specs.Topology.GraphFundamentalGroup.bouquetFreeGroup.{u} := by
  intro E
  let f : E → Pi1 (WeakBouquet E) (bouquetVertex E) := fun e => loopClass (bouquetLoop e)
  have hfS (S : Finset E) :
      ∃ Φ : FreeGroup S ≃* Pi1 (WeakBouquet S) (bouquetVertex S),
        (map (Subtype.val : S → E)).induced.comp Φ.toMonoidHom =
          FreeGroup.lift (fun e : S => f e.val) := by
    obtain ⟨Φ,hΦ⟩ := hfinite S
    refine ⟨Φ,?_⟩
    apply FreeGroup.ext_hom
    intro e
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hΦ,
      FreeGroup.lift_apply_of]
    exact map_induced _ _
  have hinjS (S : Finset E) :
      Function.Injective (FreeGroup.lift (fun e : S => f e.val)) := by
    obtain ⟨Φ,hΦ⟩ := hfS S
    rw [← hΦ]
    exact (map_subtype_induced_injective (S : Set E)).comp Φ.injective
  have hinj : Function.Injective (FreeGroup.lift f) := by
    apply (injective_iff_map_eq_one _).mpr
    intro g hg
    obtain ⟨S,w,hw⟩ := freeGroup_finite_support g
    have hh : FreeGroup.lift (fun e : S => f e.val) w = 1 := by
      rw [← freeGroup_lift_map f, hw, hg]
    have hw1 : w = 1 := hinjS S (hh.trans (map_one _).symm)
    rw [← hw, hw1, map_one]
  have hsurj : Function.Surjective (FreeGroup.lift f) := by
    intro g
    obtain ⟨S,gS,hgS⟩ := pi1_finite_support g
    obtain ⟨Φ,hΦ⟩ := hfS S
    refine ⟨FreeGroup.map (Subtype.val : S → E) (Φ.symm gS),?_⟩
    rw [freeGroup_lift_map, ← hΦ]
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using hgS
  exact ⟨MulEquiv.ofBijective (FreeGroup.lift f) ⟨hinj,hsurj⟩,
    fun e => FreeGroup.lift_apply_of⟩

end P202.Topology.Bouquet

namespace P202.Topology

/-- The full original graph theorem reduces to tree contractibility and the
finite-bouquet calculation. All passages to infinite graphs and generator
sets, quotient identifications, orientations and basepoints are proved here. -/
theorem graphFundamentalGroup_of_treeContractibility_of_finiteBouquetFreeGroup
    (tree : P202Specs.Topology.GraphFundamentalGroup.treeContractibility.{u})
    (finiteBouquet : P202Specs.Topology.GraphFundamentalGroup.finiteBouquetFreeGroup.{u}) :
    P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u} :=
  graphFundamentalGroup_of_treeContractibility_of_bouquetFreeGroup tree
    (Bouquet.bouquetFreeGroup_of_finite finiteBouquet)

end P202.Topology

namespace P202.Topology.Bouquet

/-- The finite calculation starts correctly with no circles. -/
theorem bouquetFreeGroup_empty (E : Type u) [IsEmpty E] :
    ∃ Φ : FreeGroup E ≃* Pi1 (WeakBouquet E) (bouquetVertex E),
      ∀ e : E, Φ (FreeGroup.of e) = loopClass (bouquetLoop e) := by
  have hx (x : WeakBouquet E) : x = bouquetVertex E := by
    induction x using Quotient.inductionOn with
    | h a =>
      rcases a with _ | ⟨e,t⟩
      · rfl
      · exact isEmptyElim e
  let : Subsingleton (WeakBouquet E) := ⟨fun x y => (hx x).trans (hx y).symm⟩
  let : Subsingleton (Path (bouquetVertex E) (bouquetVertex E)) :=
    ⟨fun a b => by ext t; exact Subsingleton.elim _ _⟩
  let : Subsingleton (Pi1 (WeakBouquet E) (bouquetVertex E)) :=
    ⟨fun a b => by
      obtain ⟨p,rfl⟩ := P202.Topology.loopClass_surjective a
      obtain ⟨q,rfl⟩ := P202.Topology.loopClass_surjective b
      exact congrArg loopClass (Subsingleton.elim p q)⟩
  let f := FreeGroup.lift (fun e : E => loopClass (bouquetLoop e))
  exact ⟨MulEquiv.ofBijective f
    ⟨fun a b _ => Subsingleton.elim a b, fun g => ⟨1,Subsingleton.elim _ _⟩⟩,
    fun e => isEmptyElim e⟩


end P202.Topology.Bouquet

namespace SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

theorem IsAcyclic.root_paths_cons {r v w : V} (hG : G.IsAcyclic)
    (p : G.Path v r) (q : G.Path w r) (hvw : G.Adj v w) :
    p.val = Walk.cons hvw q.val ∨ q.val = Walk.cons hvw.symm p.val := by
  classical
  by_cases hv : v ∈ q.val.reverse.support
  · right
    have hh := hG.path_concat p.property.reverse q.property.reverse hvw hv
    have hr := congrArg Walk.reverse hh
    simpa only [Walk.reverse_reverse, Walk.reverse_concat] using hr
  · left
    have hw : w ∈ p.val.reverse.support :=
      hG.mem_support_of_ne_mem_support_of_adj_of_isPath
        p.property.reverse q.property.reverse hvw hv
    have hh := hG.path_concat q.property.reverse p.property.reverse hvw.symm hw
    have hr := congrArg Walk.reverse hh
    simpa only [Walk.reverse_reverse, Walk.reverse_concat] using hr

variable {Y : Type v} [TopologicalSpace Y]

/-- Realize a finite graph walk by its assigned directed continuous edge paths.
The recursion on cons preserves exact concatenation at the first edge. -/
def Walk.toTopologicalPath (f : V → Y)
    (edge : ∀ {v w}, G.Adj v w → _root_.Path (f v) (f w)) :
    ∀ {v w}, G.Walk v w → _root_.Path (f v) (f w) := by
  intro v w p
  induction p with
  | nil => exact _root_.Path.refl _
  | cons h p ih => exact (edge h).trans ih

@[simp] theorem Walk.toTopologicalPath_nil (f : V → Y)
    (edge : ∀ {v w}, G.Adj v w → _root_.Path (f v) (f w)) (v : V) :
    (Walk.nil : G.Walk v v).toTopologicalPath f edge = _root_.Path.refl (f v) := rfl

@[simp] theorem Walk.toTopologicalPath_cons (f : V → Y)
    (edge : ∀ {v w}, G.Adj v w → _root_.Path (f v) (f w))
    {v w z : V} (h : G.Adj v w) (p : G.Walk w z) :
    (Walk.cons h p).toTopologicalPath f edge =
      (edge h).trans (Walk.toTopologicalPath f edge p) := rfl

/-- The canonical finite simple path to a fixed root. -/
def rootSimplePath (hc : G.Connected) (r v : V) : G.Path v r :=
  by
    classical
    exact (hc v r).some.toPath

def rootedVertexPath (hc : G.Connected) (f : V → Y)
    (edge : ∀ {v w}, G.Adj v w → _root_.Path (f v) (f w)) (r v : V) : _root_.Path (f v) (f r) :=
  (rootSimplePath hc r v).val.toTopologicalPath f edge

/-- Every edge of an acyclic connected graph joins successive root paths.
This exact path identity is the compatibility needed by `rootedEdgeSquare`. -/
theorem rootedVertexPath_adj (hG : G.IsAcyclic) (hc : G.Connected) (f : V → Y)
    (edge : ∀ {v w}, G.Adj v w → _root_.Path (f v) (f w)) (r : V)
    {v w : V} (h : G.Adj v w) :
    rootedVertexPath hc f edge r v =
        (edge h).trans (rootedVertexPath hc f edge r w) ∨
      rootedVertexPath hc f edge r w =
        (edge h.symm).trans (rootedVertexPath hc f edge r v) := by
  obtain hp | hp := hG.root_paths_cons (rootSimplePath hc r v) (rootSimplePath hc r w) h
  · left
    unfold rootedVertexPath
    rw [hp, Walk.toTopologicalPath_cons]
  · right
    unfold rootedVertexPath
    rw [hp, Walk.toTopologicalPath_cons]

@[simp] theorem rootedVertexPath_root (hG : G.IsAcyclic) (hc : G.Connected) (f : V → Y)
    (edge : ∀ {v w}, G.Adj v w → _root_.Path (f v) (f w)) (r : V) :
    rootedVertexPath hc f edge r r = _root_.Path.refl (f r) := by
  have hh : rootSimplePath hc r r = ⟨Walk.nil, Walk.IsPath.nil⟩ :=
    (hG.subsingleton_path r r).elim _ _
  unfold rootedVertexPath
  rw [hh]
  rfl
end SimpleGraph

namespace SimpleGraph
variable {V : Type u} {G : SimpleGraph V}
variable {Y : Type v} [TopologicalSpace Y]

theorem Walk.toTopologicalPath_mem (f : V → Y)
    (edge : ∀ {v w}, G.Adj v w → _root_.Path (f v) (f w))
    (S : Set Y) (hf : ∀ v, f v ∈ S)
    (he : ∀ {v w} (h : G.Adj v w) t, edge h t ∈ S)
    {v w : V} (p : G.Walk v w) (t : unitInterval) :
    p.toTopologicalPath f edge t ∈ S := by
  induction p generalizing t with
  | nil => exact hf _
  | cons h p ih =>
    rw [Walk.toTopologicalPath_cons]
    have hh : ((edge h).trans (p.toTopologicalPath f edge)) t ∈
        range (edge h) ∪ range (p.toTopologicalPath f edge) := by
      rw [← _root_.Path.trans_range]
      exact mem_range_self _
    rcases hh with ⟨s, hs⟩ | ⟨s,hs⟩
    · rw [← hs]; exact he h s
    · rw [← hs]; exact ih s
end SimpleGraph

open P202.Cellular P202Specs.Topology
namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]
attribute [local instance] Classical.propDecidable

def treeAdjEdge {T : Set (Cell X 1)} {v w : GraphVertex X}
    (h : ((graphEndpoints X).support T).Adj v w) : Cell X 1 := h.2.choose

lemma treeAdjEdge_mem {T : Set (Cell X 1)} {v w : GraphVertex X}
    (h : ((graphEndpoints X).support T).Adj v w) : treeAdjEdge h ∈ T :=
  h.2.choose_spec.1

lemma treeAdjEdge_ends {T : Set (Cell X 1)} {v w : GraphVertex X}
    (h : ((graphEndpoints X).support T).Adj v w) :
    ((graphEndpoints X).source (treeAdjEdge h) = v ∧
      (graphEndpoints X).target (treeAdjEdge h) = w) ∨
    ((graphEndpoints X).source (treeAdjEdge h) = w ∧
      (graphEndpoints X).target (treeAdjEdge h) = v) := h.2.choose_spec.2

lemma treeAdjEdge_target_of_source {T : Set (Cell X 1)} {v w : GraphVertex X}
    (h : ((graphEndpoints X).support T).Adj v w)
    (hs : (graphEndpoints X).source (treeAdjEdge h) = v) :
    (graphEndpoints X).target (treeAdjEdge h) = w := by
  rcases treeAdjEdge_ends h with ⟨_, ht⟩ | ⟨hs', _⟩
  · exact ht
  · exact (h.1 (hs.symm.trans hs')).elim

lemma treeAdjEdge_reverse_of_source_ne {T : Set (Cell X 1)} {v w : GraphVertex X}
    (h : ((graphEndpoints X).support T).Adj v w)
    (hs : (graphEndpoints X).source (treeAdjEdge h) ≠ v) :
    (graphEndpoints X).source (treeAdjEdge h) = w ∧
    (graphEndpoints X).target (treeAdjEdge h) = v :=
  (treeAdjEdge_ends h).resolve_left (fun hh => hs hh.1)

def treeAdjPath {T : Set (Cell X 1)} {v w : GraphVertex X}
    (h : ((graphEndpoints X).support T).Adj v w) : Path v.val w.val :=
  if hs : (graphEndpoints X).source (treeAdjEdge h) = v then
    (graphEdgePath (treeAdjEdge h)).cast (congrArg Subtype.val hs.symm)
      (congrArg Subtype.val (treeAdjEdge_target_of_source h hs).symm)
  else
    (graphEdgePath (treeAdjEdge h)).symm.cast
      (congrArg Subtype.val (treeAdjEdge_reverse_of_source_ne h hs).2.symm)
      (congrArg Subtype.val (treeAdjEdge_reverse_of_source_ne h hs).1.symm)

lemma treeAdjEdge_eq_of_edge {T : Set (Cell X 1)}
    (hF : (graphEndpoints X).IsForest T) {v w : GraphVertex X}
    (h : ((graphEndpoints X).support T).Adj v w) (e : Cell X 1) (he : e ∈ T)
    (hs : (graphEndpoints X).source e = v) (ht : (graphEndpoints X).target e = w) :
    treeAdjEdge h = e := by
  apply hF.2.1 (treeAdjEdge_mem h) he
  rcases treeAdjEdge_ends h with ⟨hv, hw⟩ | ⟨hw, hv⟩
  · simp only [P202.Cellular.EdgeEndpoints.ends, hv, hw, hs, ht]
  · simp only [P202.Cellular.EdgeEndpoints.ends, hv, hw, hs, ht, Sym2.eq_swap]

lemma treeAdjPath_edge {T : Set (Cell X 1)}
    (hF : (graphEndpoints X).IsForest T) (e : Cell X 1) (he : e ∈ T) :
    treeAdjPath (⟨hF.1 e he, e, he, Or.inl ⟨rfl, rfl⟩⟩ :
      ((graphEndpoints X).support T).Adj ((graphEndpoints X).source e)
        ((graphEndpoints X).target e)) = graphEdgePath e := by
  have hh := treeAdjEdge_eq_of_edge hF
    (⟨hF.1 e he, e, he, Or.inl ⟨rfl, rfl⟩⟩ :
      ((graphEndpoints X).support T).Adj ((graphEndpoints X).source e)
        ((graphEndpoints X).target e)) e he rfl rfl
  have hs := congrArg (graphEndpoints X).source hh
  unfold treeAdjPath
  rw [dif_pos hs]
  ext t
  change graphEdgePath _ t = graphEdgePath e t
  rw [hh]

lemma treeAdjPath_mem {T : Set (Cell X 1)} {v w : GraphVertex X}
    (h : ((graphEndpoints X).support T).Adj v w) (t : unitInterval) :
    treeAdjPath h t ∈ graphTreeCarrier T := by
  unfold treeAdjPath
  split_ifs
  · exact graphEdgePath_mem_tree (treeAdjEdge_mem h) _
  · exact graphEdgePath_mem_tree (treeAdjEdge_mem h) _

lemma treeAdjEdge_symm {T : Set (Cell X 1)}
    (hF : (graphEndpoints X).IsForest T) {v w : GraphVertex X}
    (h : ((graphEndpoints X).support T).Adj v w) :
    treeAdjEdge h.symm = treeAdjEdge h := by
  apply hF.2.1 (treeAdjEdge_mem h.symm) (treeAdjEdge_mem h)
  rcases treeAdjEdge_ends h with ⟨hv, hw⟩ | ⟨hw, hv⟩ <;>
    rcases treeAdjEdge_ends h.symm with ⟨hw', hv'⟩ | ⟨hv', hw'⟩ <;>
    simp only [P202.Cellular.EdgeEndpoints.ends, hv, hw, hv', hw', Sym2.eq_swap]

lemma treeAdjPath_symm {T : Set (Cell X 1)}
    (hF : (graphEndpoints X).IsForest T) {v w : GraphVertex X}
    (h : ((graphEndpoints X).support T).Adj v w) :
    treeAdjPath h.symm = (treeAdjPath h).symm := by
  have heq := treeAdjEdge_symm hF h
  unfold treeAdjPath
  ext t
  split_ifs with hs hs' hs' <;>
    simp only [heq] at hs hs' ⊢
  · exact (h.1 (hs'.symm.trans hs)).elim
  · change graphEdgePath (treeAdjEdge h.symm) t =
      (graphEdgePath (treeAdjEdge h)).symm.symm t
    rw [heq, Path.symm_symm]
  · change (graphEdgePath (treeAdjEdge h.symm)).symm t =
      (graphEdgePath (treeAdjEdge h)).symm t
    rw [heq]
  · have hh := treeAdjEdge_reverse_of_source_ne h hs'
    exact (hs hh.1).elim

end P202.Topology

namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

def treeVertexRootPath {T : Set (Cell X 1)}
    (hT : (graphEndpoints X).IsSpanningTree T) (r v : GraphVertex X) : Path v.val r.val :=
  SimpleGraph.rootedVertexPath hT.2 Subtype.val (fun h => treeAdjPath h) r v

lemma treeVertexRootPath_mem {T : Set (Cell X 1)}
    (hT : (graphEndpoints X).IsSpanningTree T) (r v : GraphVertex X) (t : unitInterval) :
    treeVertexRootPath hT r v t ∈ graphTreeCarrier T := by
  apply SimpleGraph.Walk.toTopologicalPath_mem
  · intro v; exact Or.inl v.property
  · exact fun h t => treeAdjPath_mem h t

lemma treeVertexRootPath_edge {T : Set (Cell X 1)}
    (hT : (graphEndpoints X).IsSpanningTree T) (r : GraphVertex X)
    (e : Cell X 1) (he : e ∈ T) :
    treeVertexRootPath hT r ((graphEndpoints X).source e) =
        (graphEdgePath e).trans (treeVertexRootPath hT r ((graphEndpoints X).target e)) ∨
      treeVertexRootPath hT r ((graphEndpoints X).target e) =
        (graphEdgePath e).symm.trans (treeVertexRootPath hT r ((graphEndpoints X).source e)) := by
  have h : ((graphEndpoints X).support T).Adj
      ((graphEndpoints X).source e) ((graphEndpoints X).target e) :=
    ⟨hT.1.1 e he, e, he, Or.inl ⟨rfl,rfl⟩⟩
  have hh := SimpleGraph.rootedVertexPath_adj hT.1.2.2 hT.2
    Subtype.val (fun h => treeAdjPath h) r h
  rw [treeAdjPath_symm hT.1 h, treeAdjPath_edge hT.1 e he] at hh
  exact hh

/-- The coherent vertex paths are constant at the root itself. -/
@[simp] lemma treeVertexRootPath_root {T : Set (Cell X 1)}
    (hT : (graphEndpoints X).IsSpanningTree T) (r : GraphVertex X) :
    treeVertexRootPath hT r r = Path.refl r.val :=
  SimpleGraph.rootedVertexPath_root hT.1.2.2 hT.2 _ _ _
end P202.Topology

namespace P202.Topology
variable {Y : Type v} [TopologicalSpace Y] {a b r : Y}

lemma rootedEdgeSquare_mem (e : Path a b) (q : Path a r) (S : Set Y)
    (he : ∀ t, e t ∈ S) (hq : ∀ t, q t ∈ S) (z : unitInterval × unitInterval) :
    rootedEdgeSquare e q z ∈ S := by
  dsimp only [rootedEdgeSquare, ContinuousMap.coe_mk]
  split_ifs
  · have hh : e.extend ((z.2 : ℝ) - (z.1 : ℝ) * (1 + (z.2 : ℝ))) ∈ range e := by
      rw [← e.extend_range]
      exact mem_range_self _
    obtain ⟨t,ht⟩ := hh
    rw [← ht]; exact he t
  · have hh : q.extend ((z.1 : ℝ) * (1 + (z.2 : ℝ)) - (z.2 : ℝ)) ∈ range q := by
      rw [← q.extend_range]
      exact mem_range_self _
    obtain ⟨t,ht⟩ := hh
    rw [← ht]; exact hq t

variable {X : Type u} [TopologicalSpace X] [CWStructure X]

def treeEdgeSquare {T : Set (Cell X 1)}
    (hT : (graphEndpoints X).IsSpanningTree T) (r : GraphVertex X)
    (e : Cell X 1) : C(unitInterval × unitInterval,X) := by
  classical
  exact if treeVertexRootPath hT r ((graphEndpoints X).target e) =
      (graphEdgePath e).symm.trans
        (treeVertexRootPath hT r ((graphEndpoints X).source e)) then
    rootedEdgeSquare (graphEdgePath e) (treeVertexRootPath hT r ((graphEndpoints X).source e))
  else
    (rootedEdgeSquare (graphEdgePath e).symm
      (treeVertexRootPath hT r ((graphEndpoints X).target e))).comp
      ⟨fun z => (z.1,unitInterval.symm z.2), by fun_prop⟩

@[simp] lemma treeEdgeSquare_zero {T : Set (Cell X 1)}
    (hT : (graphEndpoints X).IsSpanningTree T) (r : GraphVertex X)
    (e : Cell X 1) (t : unitInterval) :
    treeEdgeSquare hT r e (0,t) = graphEdgePath e t := by
  classical
  unfold treeEdgeSquare
  split_ifs
  · exact rootedEdgeSquare_zero _ _ t
  · simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      rootedEdgeSquare_zero, Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]

@[simp] lemma treeEdgeSquare_one {T : Set (Cell X 1)}
    (hT : (graphEndpoints X).IsSpanningTree T) (r : GraphVertex X)
    (e : Cell X 1) (t : unitInterval) :
    treeEdgeSquare hT r e (1,t) = r.val := by
  classical
  unfold treeEdgeSquare
  split_ifs
  · exact rootedEdgeSquare_one _ _ t
  · exact rootedEdgeSquare_one _ _ _

@[simp] lemma treeEdgeSquare_left {T : Set (Cell X 1)}
    (hT : (graphEndpoints X).IsSpanningTree T) (r : GraphVertex X)
    (e : Cell X 1) (he : e ∈ T) (s : unitInterval) :
    treeEdgeSquare hT r e (s,0) =
      treeVertexRootPath hT r ((graphEndpoints X).source e) s := by
  classical
  unfold treeEdgeSquare
  split_ifs with hh
  · exact rootedEdgeSquare_left _ _ s
  · have hp := (treeVertexRootPath_edge hT r e he).resolve_right hh
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      unitInterval.symm_zero, rootedEdgeSquare_right, Path.symm_symm, ← hp]

@[simp] lemma treeEdgeSquare_right {T : Set (Cell X 1)}
    (hT : (graphEndpoints X).IsSpanningTree T) (r : GraphVertex X)
    (e : Cell X 1) (he : e ∈ T) (s : unitInterval) :
    treeEdgeSquare hT r e (s,1) =
      treeVertexRootPath hT r ((graphEndpoints X).target e) s := by
  classical
  unfold treeEdgeSquare
  split_ifs with hh
  · simpa only [rootedEdgeSquare_right, ← hh]
  · simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      unitInterval.symm_one, rootedEdgeSquare_left]

lemma treeEdgeSquare_mem {T : Set (Cell X 1)}
    (hT : (graphEndpoints X).IsSpanningTree T) (r : GraphVertex X)
    (e : Cell X 1) (he : e ∈ T) (z : unitInterval × unitInterval) :
    treeEdgeSquare hT r e z ∈ graphTreeCarrier T := by
  classical
  unfold treeEdgeSquare
  split_ifs
  · exact rootedEdgeSquare_mem _ _ _ (graphEdgePath_mem_tree he)
      (treeVertexRootPath_mem hT r _) z
  · exact rootedEdgeSquare_mem (graphEdgePath e).symm
      (treeVertexRootPath hT r ((graphEndpoints X).target e)) _
      (fun t => graphEdgePath_mem_tree he _) (treeVertexRootPath_mem hT r _)
      (z.1,unitInterval.symm z.2)
end P202.Topology

namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

/-- Every point of the selected graph carrier is a vertex or belongs to an
actual selected characteristic edge, with its chosen interval parameter. -/
lemma graphTreeCarrier_point_cases {T : Set (Cell X 1)} {x : X}
    (hx : x ∈ graphTreeCarrier T) :
    (∃ v : GraphVertex X, x = v.val) ∨
      ∃ e ∈ T, ∃ t : unitInterval, x = graphEdgePath e t := by
  rcases hx with hv | he
  · exact Or.inl ⟨⟨x,hv⟩,rfl⟩
  · obtain ⟨e,he,y,hy⟩ := mem_iUnion₂.mp he
    obtain ⟨t,ht⟩ := edgeDiskPoint_surjective (interiorInclusion 1 y)
    refine Or.inr ⟨e,he,t,?_⟩
    change x = characteristic X 1 e (edgeDiskPoint t)
    rw [ht]
    exact hy.symm
end P202.Topology
namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]
variable {Y : Type v} [TopologicalSpace Y]
attribute [local instance] Classical.propDecidable
open private cell_unique from MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellTopology

private def graphSubcomplexHomotopyInterior (T : Set (Cell X 1))
    (eH : ∀ e : T, C(unitInterval × unitInterval, Y)) (e : T)
    (x : openCell X 1 e.val) (s : unitInterval) : Y :=
  eH e (s, edgeDiskParameter (interiorInclusion 1 ((cellHomeomorph 1 e.val).symm x)))

/-- The pointwise pasting of vertex trajectories and selected-edge squares. -/
def graphSubcomplexHomotopyMap (T : Set (Cell X 1))
    (vH : ∀ v : GraphVertex X, C(unitInterval, Y))
    (eH : ∀ e : T, C(unitInterval × unitInterval, Y))
    (z : (graphSubcomplex T) × unitInterval) : Y :=
  if hv : z.1.val ∈ skeletonLT X 1 then vH ⟨z.1.val,hv⟩ z.2 else
    let hx : ∃ e ∈ T, z.1.val ∈ openCell X 1 e :=
      by simpa only [exists_prop] using mem_iUnion₂.mp ((show z.1.val ∈ graphTreeCarrier T by
        rw [← graphSubcomplex_carrier]; exact z.1.property).resolve_left hv)
    graphSubcomplexHomotopyInterior T eH ⟨hx.choose,hx.choose_spec.1⟩
      ⟨z.1.val,hx.choose_spec.2⟩ z.2

lemma graphSubcomplexHomotopyMap_vertex (T : Set (Cell X 1))
    (vH : ∀ v : GraphVertex X, C(unitInterval, Y))
    (eH : ∀ e : T, C(unitInterval × unitInterval, Y))
    (v : GraphVertex X) (hv : v.val ∈ (graphSubcomplex T).carrier) (s : unitInterval) :
    graphSubcomplexHomotopyMap T vH eH (⟨v.val,hv⟩,s) = vH v s := by
  simp [graphSubcomplexHomotopyMap, v.property]

lemma graphSubcomplexHomotopyMap_interior (T : Set (Cell X 1))
    (vH : ∀ v : GraphVertex X, C(unitInterval, Y))
    (eH : ∀ e : T, C(unitInterval × unitInterval, Y))
    (e : T) (y : OpenDisk 1)
    (hx : interiorMap X 1 e.val y ∈ (graphSubcomplex T).carrier) (s : unitInterval) :
    graphSubcomplexHomotopyMap T vH eH (⟨interiorMap X 1 e.val y,hx⟩,s) =
      eH e (s, edgeDiskParameter (interiorInclusion 1 y)) := by
  have hv : interiorMap X 1 e.val y ∉ skeletonLT X 1 :=
    fun hv => vertex_not_in_open_edge hv e.val ⟨y,rfl⟩
  let hp : ∃ f ∈ T, interiorMap X 1 e.val y ∈ openCell X 1 f :=
    by simpa only [exists_prop] using mem_iUnion₂.mp ((show interiorMap X 1 e.val y ∈ graphTreeCarrier T by
      rw [← graphSubcomplex_carrier]; exact hx).resolve_left hv)
  have heq : hp.choose = e.val := by
    have hc := hp.choose_spec.2
    exact eq_of_heq (Sigma.mk.inj_iff.mp (cell_unique hc ⟨y,rfl⟩)).2
  have heq' : (⟨hp.choose,hp.choose_spec.1⟩ : T) = e := Subtype.ext heq
  unfold graphSubcomplexHomotopyMap
  rw [dite_eq_right hv]
  change graphSubcomplexHomotopyInterior T eH ⟨hp.choose,hp.choose_spec.1⟩ _ _ = _
  have hcongr : ∀ (f g : T) (hf : interiorMap X 1 e.val y ∈ openCell X 1 f.val)
      (hg : interiorMap X 1 e.val y ∈ openCell X 1 g.val), f = g →
      graphSubcomplexHomotopyInterior T eH f ⟨_,hf⟩ s =
        graphSubcomplexHomotopyInterior T eH g ⟨_,hg⟩ s := by
    rintro f g hf hg rfl
    rfl
  trans graphSubcomplexHomotopyInterior T eH e ⟨_,⟨y,rfl⟩⟩ s
  · exact hcongr _ _ _ _ heq'
  unfold graphSubcomplexHomotopyInterior
  have hy : (cellHomeomorph 1 e.val).symm
      ⟨interiorMap X 1 e.val y,⟨y,rfl⟩⟩ = y :=
    (cellHomeomorph 1 e.val).symm_apply_apply y
  rw [hy]

lemma graphSubcomplexHomotopyMap_characteristic (T : Set (Cell X 1))
    (vH : ∀ v : GraphVertex X, C(unitInterval, Y))
    (eH : ∀ e : T, C(unitInterval × unitInterval, Y))
    (hleft : ∀ (e : T) s, eH e (s,0) = vH ((graphEndpoints X).source e.val) s)
    (hright : ∀ (e : T) s, eH e (s,1) = vH ((graphEndpoints X).target e.val) s)
    (e : T) (z : Disk 1)
    (hx : characteristic X 1 e.val z ∈ (graphSubcomplex T).carrier) (s : unitInterval) :
    graphSubcomplexHomotopyMap T vH eH (⟨characteristic X 1 e.val z,hx⟩,s) =
      eH e (s, edgeDiskParameter z) := by
  rcases diskOne_cases z with ⟨y,rfl⟩ | rfl | rfl
  · exact graphSubcomplexHomotopyMap_interior T vH eH e y hx s
  · rw [edgeDiskParameter_point, hleft]
    exact graphSubcomplexHomotopyMap_vertex T vH eH ((graphEndpoints X).source e.val) hx s
  · rw [edgeDiskParameter_point, hright]
    exact graphSubcomplexHomotopyMap_vertex T vH eH ((graphEndpoints X).target e.val) hx s

lemma graphSubcomplexHomotopyMap_continuous (T : Set (Cell X 1))
    (vH : ∀ v : GraphVertex X, C(unitInterval, Y))
    (eH : ∀ e : T, C(unitInterval × unitInterval, Y))
    (hleft : ∀ (e : T) s, eH e (s,0) = vH ((graphEndpoints X).source e.val) s)
    (hright : ∀ (e : T) s, eH e (s,1) = vH ((graphEndpoints X).target e.val) s) :
    Continuous (graphSubcomplexHomotopyMap T vH eH) := by
  apply (subcomplex_homotopyContinuityTest _ _).mpr
  intro n c
  cases n with
  | zero =>
    let z₀ : Disk 0 := ⟨0, by simp⟩
    have hv : characteristic X 0 c.val z₀ ∈ skeletonLT X 1 := by
      apply (mem_graphVertex_iff _).mpr
      refine ⟨c.val, ⟨⟨0,by simp⟩,?_⟩⟩
      rfl
    let v : GraphVertex X := ⟨characteristic X 0 c.val z₀,hv⟩
    have hh : (fun z : Disk 0 × unitInterval => graphSubcomplexHomotopyMap T vH eH
        (subcomplexDiskProjection (graphSubcomplex T) ⟨0,c,z.1⟩,z.2)) =
        fun z : Disk 0 × unitInterval => vH v z.2 := by
      funext z
      have hz : z.1 = z₀ := Subsingleton.elim _ _
      rcases z with ⟨z,s⟩
      dsimp only at hz
      subst z
      exact graphSubcomplexHomotopyMap_vertex T vH eH v _ s
    rw [hh]
    exact (vH v).continuous.comp continuous_snd
  | succ n =>
    cases n with
    | zero =>
      have he : c.val ∈ T := c.property
      have hh : (fun z : Disk 1 × unitInterval => graphSubcomplexHomotopyMap T vH eH
          (subcomplexDiskProjection (graphSubcomplex T) ⟨1,c,z.1⟩,z.2)) =
          fun z : Disk 1 × unitInterval => eH ⟨c.val,he⟩ (z.2,edgeDiskParameter z.1) := by
        funext z
        exact graphSubcomplexHomotopyMap_characteristic T vH eH hleft hright ⟨c.val,he⟩ _ _ _
      rw [hh]
      exact (eH ⟨c.val,he⟩).continuous.comp
        (continuous_snd.prodMk (edgeDiskParameter_continuous.comp continuous_fst))
    | succ n => exact c.property.elim

def graphSubcomplexHomotopy (T : Set (Cell X 1))
    (vH : ∀ v : GraphVertex X, C(unitInterval, Y))
    (eH : ∀ e : T, C(unitInterval × unitInterval, Y))
    (hleft : ∀ (e : T) s, eH e (s,0) = vH ((graphEndpoints X).source e.val) s)
    (hright : ∀ (e : T) s, eH e (s,1) = vH ((graphEndpoints X).target e.val) s) :
    C((graphSubcomplex T) × unitInterval, Y) :=
  ⟨graphSubcomplexHomotopyMap T vH eH,
    graphSubcomplexHomotopyMap_continuous T vH eH hleft hright⟩


lemma graphSubcomplexHomotopy_vertex (T : Set (Cell X 1))
    (vH : ∀ v : GraphVertex X, C(unitInterval, Y))
    (eH : ∀ e : T, C(unitInterval × unitInterval, Y))
    (hleft : ∀ (e : T) s, eH e (s,0) = vH ((graphEndpoints X).source e.val) s)
    (hright : ∀ (e : T) s, eH e (s,1) = vH ((graphEndpoints X).target e.val) s)
    (v : GraphVertex X) (hv : v.val ∈ (graphSubcomplex T).carrier) (s : unitInterval) :
    graphSubcomplexHomotopy T vH eH hleft hright (⟨v.val,hv⟩,s) = vH v s :=
  graphSubcomplexHomotopyMap_vertex T vH eH v hv s

lemma graphSubcomplexHomotopy_edge (T : Set (Cell X 1))
    (vH : ∀ v : GraphVertex X, C(unitInterval, Y))
    (eH : ∀ e : T, C(unitInterval × unitInterval, Y))
    (hleft : ∀ (e : T) s, eH e (s,0) = vH ((graphEndpoints X).source e.val) s)
    (hright : ∀ (e : T) s, eH e (s,1) = vH ((graphEndpoints X).target e.val) s)
    (e : T) (t : unitInterval)
    (hx : graphEdgePath e.val t ∈ (graphSubcomplex T).carrier) (s : unitInterval) :
    graphSubcomplexHomotopy T vH eH hleft hright (⟨graphEdgePath e.val t,hx⟩,s) =
      eH e (s,t) := by
  have hh := graphSubcomplexHomotopyMap_characteristic T vH eH hleft hright
    e (edgeDiskPoint t) hx s
  change graphSubcomplexHomotopyMap T vH eH
    (⟨characteristic X 1 e.val (edgeDiskPoint t),hx⟩,s) = _
  rw [edgeDiskParameter_point] at hh
  exact hh

end P202.Topology

namespace P202.Topology
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

/-- A combinatorial spanning tree contracts in its actual CW subspace topology.
The proof uses compatible finite root paths and pastes their explicit squares;
it does not require finite valence or finitely many edges. -/
theorem graph_tree_contractible {T : Set (Cell X 1)}
    (hT : (graphEndpoints X).IsSpanningTree T) :
    ContractibleSpace ↥(graphTreeCarrier T) := by
  let r : GraphVertex X := Classical.choice hT.2.nonempty
  let vH : ∀ v : GraphVertex X, C(unitInterval,X) :=
    fun v => (treeVertexRootPath hT r v).toContinuousMap
  let eH : ∀ e : T, C(unitInterval × unitInterval,X) :=
    fun e => treeEdgeSquare hT r e.val
  have hl : ∀ (e : T) s, eH e (s,0) = vH ((graphEndpoints X).source e.val) s :=
    fun e s => treeEdgeSquare_left hT r e.val e.property s
  have hr : ∀ (e : T) s, eH e (s,1) = vH ((graphEndpoints X).target e.val) s :=
    fun e s => treeEdgeSquare_right hT r e.val e.property s
  let F := graphSubcomplexHomotopy T vH eH hl hr
  have hv (v : GraphVertex X) (hv : v.val ∈ (graphSubcomplex T).carrier) (s : unitInterval) :
      F (⟨v.val,hv⟩,s) = treeVertexRootPath hT r v s :=
    graphSubcomplexHomotopy_vertex T vH eH hl hr v hv s
  have he (e : Cell X 1) (he : e ∈ T) (t : unitInterval)
      (hx : graphEdgePath e t ∈ (graphSubcomplex T).carrier) (s : unitInterval) :
      F (⟨graphEdgePath e t,hx⟩,s) = treeEdgeSquare hT r e (s,t) :=
    graphSubcomplexHomotopy_edge T vH eH hl hr ⟨e,he⟩ t hx s
  have hmem (z : (graphSubcomplex T) × unitInterval) :
      F z ∈ (graphSubcomplex T).carrier := by
    rcases z with ⟨⟨x,hx⟩,s⟩
    have hx' : x ∈ graphTreeCarrier T := by rwa [← graphSubcomplex_carrier]
    apply (Iff.of_eq (congrArg (fun S : Set X => F (⟨x,hx⟩,s) ∈ S)
      (graphSubcomplex_carrier T))).mpr
    rcases graphTreeCarrier_point_cases hx' with ⟨v,rfl⟩ | ⟨e,he',t,rfl⟩
    · rw [hv]
      exact treeVertexRootPath_mem hT r v s
    · rw [he e he']
      exact treeEdgeSquare_mem hT r e he' _
  have hzero (x : graphSubcomplex T) : F (x,0) = x.val := by
    rcases x with ⟨x,hx⟩
    have hx' : x ∈ graphTreeCarrier T := by rwa [← graphSubcomplex_carrier]
    rcases graphTreeCarrier_point_cases hx' with ⟨v,rfl⟩ | ⟨e,he',t,rfl⟩
    · rw [hv]
      exact (treeVertexRootPath hT r v).source
    · rw [he e he', treeEdgeSquare_zero]
  have hone (x : graphSubcomplex T) : F (x,1) = r.val := by
    rcases x with ⟨x,hx⟩
    have hx' : x ∈ graphTreeCarrier T := by rwa [← graphSubcomplex_carrier]
    rcases graphTreeCarrier_point_cases hx' with ⟨v,rfl⟩ | ⟨e,he',t,rfl⟩
    · rw [hv]
      exact (treeVertexRootPath hT r v).target
    · rw [he e he', treeEdgeSquare_one]
  let rA : graphSubcomplex T := ⟨r.val, by
    rw [graphSubcomplex_carrier]
    exact Or.inl r.property⟩
  haveI : ContractibleSpace (graphSubcomplex T) := by
    apply (contractible_iff_id_nullhomotopic _).mpr
    refine ⟨rA, ⟨?_⟩⟩
    exact {
      toFun := fun z => ⟨F (z.2,z.1),hmem _⟩
      continuous_toFun := (F.continuous.comp continuous_swap).subtype_mk _
      map_zero_left := fun x => Subtype.ext (hzero x)
      map_one_left := fun x => Subtype.ext (hone x) }
  exact (Homeomorph.setCongr (graphSubcomplex_carrier T)).symm.contractibleSpace

/-- Full geometric tree lemma, with no finiteness or ambient dimension
restriction. -/
theorem treeContractibility : P202Specs.Topology.GraphFundamentalGroup.treeContractibility.{u} := by
  intro X _ _ T hT
  exact graph_tree_contractible hT
end P202.Topology

namespace P202.Topology

/-- All graph geometry and all passages to infinite graphs are proved. The
remaining finite-bouquet theorem alone suffices for the original target. -/
theorem graphFundamentalGroup_of_finiteBouquetFreeGroup
    (finiteBouquet : P202Specs.Topology.GraphFundamentalGroup.finiteBouquetFreeGroup.{u}) :
    P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u} :=
  graphFundamentalGroup_of_treeContractibility_of_finiteBouquetFreeGroup
    treeContractibility finiteBouquet

end P202.Topology

namespace P202.Topology.BouquetSingleton
open P202.Cellular P202Specs.Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev IntervalModel := ↥(Icc (0 : ℝ) (0 + 1))
abbrev CircleModel := Quot (AddCircle.EndpointIdent (1 : ℝ) 0)

def intervalHomeo : unitInterval ≃ₜ IntervalModel :=
  Homeomorph.setCongr (by simp)

@[simp] lemma intervalHomeo_val (t : unitInterval) : (intervalHomeo t).val = t.val := rfl
@[simp] lemma intervalHomeo_symm_val (t : IntervalModel) :
    (intervalHomeo.symm t).val = t.val := rfl

def quotientVertex : CircleModel :=
  Quot.mk (AddCircle.EndpointIdent (1 : ℝ) 0) (intervalHomeo 0)

/-- The oriented interval quotient loop. -/
def quotientLoop : Path quotientVertex quotientVertex where
  toFun t := Quot.mk _ (intervalHomeo t)
  continuous_toFun := continuous_quot_mk.comp intervalHomeo.continuous
  source' := rfl
  target' := by
    apply Eq.symm
    apply Quot.sound
    have h0 : intervalHomeo 0 = ⟨(0 : ℝ), by norm_num⟩ := Subtype.ext rfl
    have h1 : intervalHomeo 1 = ⟨(0 : ℝ) + 1, by norm_num⟩ :=
      Subtype.ext (by simp)
    rw [h0,h1]
    exact AddCircle.EndpointIdent.mk

def toQuotient (E : Type u) :
    PointedMap (WeakBouquet E) CircleModel (bouquetVertex E) quotientVertex :=
  Bouquet.desc quotientVertex (fun _ => quotientLoop)

@[simp] lemma toQuotient_vertex (E : Type u) :
    (toQuotient E).map (bouquetVertex E) = quotientVertex := rfl
@[simp] lemma toQuotient_loop {E : Type u} (e : E) (t : unitInterval) :
    (toQuotient E).map (bouquetLoop e t) = quotientLoop t := rfl

def fromQuotient (E : Type u) [Unique E] : C(CircleModel, WeakBouquet E) := by
  let raw : IntervalModel → WeakBouquet E := fun t => bouquetLoop (default : E) (intervalHomeo.symm t)
  have hr : ∀ a b, AddCircle.EndpointIdent (1 : ℝ) 0 a b → raw a = raw b := by
    intro a b h
    cases h
    have h0 : intervalHomeo.symm ⟨(0 : ℝ), by norm_num⟩ = 0 := Subtype.ext rfl
    have h1 : intervalHomeo.symm ⟨(0 : ℝ) + 1, by norm_num⟩ = 1 :=
      Subtype.ext (by simp)
    change bouquetLoop (default : E) _ = bouquetLoop (default : E) _
    rw [h0,h1]
    exact (bouquetLoop (default : E)).source.trans (bouquetLoop (default : E)).target.symm
  exact ⟨Quot.lift raw hr,
    continuous_quot_lift hr ((bouquetLoop (default : E)).continuous.comp intervalHomeo.symm.continuous)⟩

@[simp] lemma fromQuotient_loop (E : Type u) [Unique E] (t : unitInterval) :
    fromQuotient E (quotientLoop t) = bouquetLoop (default : E) t := by
  change bouquetLoop (default : E) (intervalHomeo.symm (intervalHomeo t)) = _
  rw [intervalHomeo.symm_apply_apply]

@[simp] lemma fromQuotient_vertex (E : Type u) [Unique E] :
    fromQuotient E quotientVertex = bouquetVertex E := by
  change fromQuotient E (quotientLoop 0) = _
  rw [fromQuotient_loop, Path.source]

/-- A one-edge weak bouquet is the actual quotient of an interval by its endpoints. -/
def quotientHomeo (E : Type u) [Unique E] : WeakBouquet E ≃ₜ CircleModel where
  toFun := (toQuotient E).map
  invFun := fromQuotient E
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h a =>
      rcases a with _ | ⟨e,t⟩
      · exact fromQuotient_vertex E
      · change fromQuotient E (quotientLoop t) = bouquetLoop e t
        rw [fromQuotient_loop, Unique.default_eq e]
  right_inv x := by
    induction x using Quot.ind with
    | _ t =>
      change quotientLoop (intervalHomeo.symm t) = Quot.mk _ t
      change Quot.mk _ (intervalHomeo (intervalHomeo.symm t)) = Quot.mk _ t
      rw [intervalHomeo.apply_symm_apply]
  continuous_toFun := (toQuotient E).map.continuous
  continuous_invFun := (fromQuotient E).continuous

/-- The unique edge is identified with the positively oriented additive circle. -/
def addCircleHomeo (E : Type u) [Unique E] : WeakBouquet E ≃ₜ AddCircle (1 : ℝ) :=
  (quotientHomeo E).trans (AddCircle.homeoIccQuot (1 : ℝ) 0).symm

@[simp] lemma addCircleHomeo_vertex (E : Type u) [Unique E] :
    addCircleHomeo E (bouquetVertex E) = 0 := rfl

@[simp] lemma addCircleHomeo_loop (E : Type u) [Unique E] (e : E) (t : unitInterval) :
    addCircleHomeo E (bouquetLoop e t) = (t.val : AddCircle (1 : ℝ)) := rfl

/-- Winding number in the positive characteristic-edge orientation. -/
def windingEquiv (E : Type u) [Unique E] :
    Pi1 (WeakBouquet E) (bouquetVertex E) ≃* Multiplicative ℤ :=
  (P202.Topology.pointedHomeomorphEquiv (addCircleHomeo E) (bouquetVertex E) 0
    (addCircleHomeo_vertex E)).trans
      ((oppositeEquiv (AddCircle.windingNumberIso (0 : AddCircle (1 : ℝ)))).trans
        MulOpposite.opMulEquiv.symm)

lemma windingEquiv_loop (E : Type u) [Unique E] (e : E) :
    windingEquiv E (loopClass (bouquetLoop e)) = Multiplicative.ofAdd (1 : ℤ) := by
  let H := addCircleHomeo E
  let f : PointedMap (WeakBouquet E) (AddCircle (1 : ℝ)) (bouquetVertex E) 0 :=
    ⟨⟨H,H.continuous⟩, addCircleHomeo_vertex E⟩
  let b : Path (0 : AddCircle (1 : ℝ)) 0 :=
    ((bouquetLoop e).map H.continuous).cast f.point.symm f.point.symm
  have hb : ((↑) : ℝ → AddCircle (1 : ℝ)) ∘
      (⟨Subtype.val,continuous_subtype_val⟩ : C(unitInterval,ℝ)) = b := by
    funext t
    exact (addCircleHomeo_loop E e t).symm
  have hw := AddCircle.windingNumber_eq_div b
    (⟨Subtype.val,continuous_subtype_val⟩ : C(unitInterval,ℝ)) hb
  change (windingEquiv E (loopClass (bouquetLoop e))).toAdd = (1 : ℤ)
  apply Int.cast_injective (α := ℝ)
  norm_num only [Int.cast_one]
  change (AddCircle.windingNumber ((f.induced (loopClass (bouquetLoop e))).unop) : ℝ) = 1
  rw [P202.Topology.inducedFormula]
  change (AddCircle.windingNumber (.of (.mk b)) : ℝ) = 1
  simpa using hw

/-- The unique oriented bouquet edge is the free group's positive generator. -/
theorem bouquetFreeGroup_unique (E : Type u) [Unique E] :
    ∃ Φ : FreeGroup E ≃* Pi1 (WeakBouquet E) (bouquetVertex E),
      ∀ e : E, Φ (FreeGroup.of e) = loopClass (bouquetLoop e) := by
  refine ⟨FreeGroup.mulEquivIntOfUnique.trans (windingEquiv E).symm,?_⟩
  intro e
  apply (windingEquiv E).injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, windingEquiv_loop]
  simp [FreeGroup.mulEquivIntOfUnique, FreeGroup.equivIntOfUnique]

end P202.Topology.BouquetSingleton

namespace P202.Topology

/-- A specified family satisfying the group universal property is an actual
free basis, with the given values on generators. -/
theorem freeGroup_equiv_of_unique_lift {E G : Type u} [Group G] (f : E → G)
    (h : ∀ (H : Type u) [Group H] (k : E → H),
      ∃! φ : G →* H, ∀ e, φ (f e) = k e) :
    ∃ Φ : FreeGroup E ≃* G, ∀ e, Φ (FreeGroup.of e) = f e := by
  let L : FreeGroup E →* G := FreeGroup.lift f
  obtain ⟨R, hR, _⟩ := h (FreeGroup E) FreeGroup.of
  have hRL : R.comp L = MonoidHom.id (FreeGroup E) := by
    apply FreeGroup.ext_hom
    intro e
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply, L,
      FreeGroup.lift_apply_of] using hR e
  have hLR : L.comp R = MonoidHom.id G := by
    obtain ⟨k, hk, hu⟩ := h G f
    apply (hu _ _).trans (hu _ (fun _ => rfl)).symm
    intro e
    simp only [MonoidHom.comp_apply, hR, L, FreeGroup.lift_apply_of]
  have hbij : Function.Bijective L := by
    constructor
    · intro a b hab
      have hh := congrArg R hab
      simpa only [← MonoidHom.comp_apply, hRL, MonoidHom.id_apply] using hh
    · intro g
      refine ⟨R g, ?_⟩
      exact DFunLike.congr_fun hLR g
  exact ⟨MulEquiv.ofBijective L hbij, fun _ => FreeGroup.lift_apply_of⟩

/-- A group coproduct of two groups with specified free bases is freely
generated by the disjoint union, with both inclusions recorded explicitly. -/
theorem freeGroup_sum_equiv_of_pushout {E F A B G : Type u}
    [Group A] [Group B] [Group G]
    (eA : FreeGroup E ≃* A) (eB : FreeGroup F ≃* B)
    (iA : A →* G) (iB : B →* G)
    (h : ∀ (H : Type u) [Group H] (f : A →* H) (g : B →* H),
      ∃! φ : G →* H, φ.comp iA = f ∧ φ.comp iB = g) :
    ∃ Φ : FreeGroup (E ⊕ F) ≃* G,
      (∀ e, Φ (FreeGroup.of (.inl e)) = iA (eA (FreeGroup.of e))) ∧
      (∀ f, Φ (FreeGroup.of (.inr f)) = iB (eB (FreeGroup.of f))) := by
  let j : E ⊕ F → G := Sum.elim (fun e => iA (eA (FreeGroup.of e)))
    (fun f => iB (eB (FreeGroup.of f)))
  have hup : ∀ (H : Type u) [Group H] (k : E ⊕ F → H),
      ∃! φ : G →* H, ∀ e, φ (j e) = k e := by
    intro H _ k
    let f : A →* H := (FreeGroup.lift (fun e => k (.inl e))).comp eA.symm.toMonoidHom
    let g : B →* H := (FreeGroup.lift (fun e => k (.inr e))).comp eB.symm.toMonoidHom
    obtain ⟨φ, ⟨hφA,hφB⟩, huniq⟩ := h H f g
    refine ⟨φ, ?_, ?_⟩
    · intro e
      cases e with
      | inl e =>
        change φ (iA (eA (FreeGroup.of e))) = _
        have hh := DFunLike.congr_fun hφA (eA (FreeGroup.of e))
        simpa only [MonoidHom.comp_apply, f, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply, FreeGroup.lift_apply_of] using hh
      | inr e =>
        change φ (iB (eB (FreeGroup.of e))) = _
        have hh := DFunLike.congr_fun hφB (eB (FreeGroup.of e))
        simpa only [MonoidHom.comp_apply, g, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply, FreeGroup.lift_apply_of] using hh
    · intro ψ hψ
      apply huniq ψ
      constructor
      · have hh : (ψ.comp iA).comp eA.toMonoidHom = f.comp eA.toMonoidHom := by
          apply FreeGroup.ext_hom
          intro e
          simpa only [MonoidHom.comp_apply, f, MulEquiv.coe_toMonoidHom,
            MulEquiv.symm_apply_apply, FreeGroup.lift_apply_of, j, Sum.elim_inl] using hψ (.inl e)
        ext a
        obtain ⟨w,rfl⟩ := eA.surjective a
        exact DFunLike.congr_fun hh w
      · have hh : (ψ.comp iB).comp eB.toMonoidHom = g.comp eB.toMonoidHom := by
          apply FreeGroup.ext_hom
          intro e
          simpa only [MonoidHom.comp_apply, g, MulEquiv.coe_toMonoidHom,
            MulEquiv.symm_apply_apply, FreeGroup.lift_apply_of, j, Sum.elim_inr] using hψ (.inr e)
        ext a
        obtain ⟨w,rfl⟩ := eB.surjective a
        exact DFunLike.congr_fun hh w
  obtain ⟨Φ,hΦ⟩ := freeGroup_equiv_of_unique_lift j hup
  exact ⟨Φ, fun e => hΦ (.inl e), fun f => hΦ (.inr f)⟩

end P202.Topology

namespace P202.Topology.BouquetReindex
open P202.Cellular P202Specs.Topology

/-- Relabeling a bouquet preserves the full weak topology. -/
def labelHomeo {E : Type u} {F : Type v} (e : E ≃ F) :
    WeakBouquet E ≃ₜ WeakBouquet F where
  toFun := (Bouquet.map e).map
  invFun := (Bouquet.map e.symm).map
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h a =>
      rcases a with _ | ⟨x,t⟩
      · rfl
      · change bouquetLoop (e.symm (e x)) t = bouquetLoop x t
        rw [e.symm_apply_apply]
  right_inv y := by
    induction y using Quotient.inductionOn with
    | h a =>
      rcases a with _ | ⟨y,t⟩
      · rfl
      · change bouquetLoop (e (e.symm y)) t = bouquetLoop y t
        rw [e.apply_symm_apply]
  continuous_toFun := (Bouquet.map e).map.continuous
  continuous_invFun := (Bouquet.map e.symm).map.continuous

@[simp] lemma labelHomeo_vertex {E : Type u} {F : Type v} (e : E ≃ F) :
    labelHomeo e (bouquetVertex E) = bouquetVertex F := rfl

@[simp] lemma labelHomeo_loop {E : Type u} {F : Type v} (e : E ≃ F)
    (x : E) (t : unitInterval) :
    labelHomeo e (bouquetLoop x t) = bouquetLoop (e x) t := rfl

/-- The actual induced isomorphism, with its vertex as specified basepoint. -/
def fundamentalGroupEquiv {E : Type u} {F : Type v} (e : E ≃ F) :
    Pi1 (WeakBouquet E) (bouquetVertex E) ≃*
      Pi1 (WeakBouquet F) (bouquetVertex F) :=
  pointedHomeomorphEquiv (labelHomeo e) _ _ (labelHomeo_vertex e)

@[simp] lemma fundamentalGroupEquiv_loop {E : Type u} {F : Type v} (e : E ≃ F) (x : E) :
    fundamentalGroupEquiv e (loopClass (bouquetLoop x)) = loopClass (bouquetLoop (e x)) := by
  change (Bouquet.map e).induced (loopClass (bouquetLoop x)) = _
  exact Bouquet.map_induced e x

/-- The required oriented basis assertion for a specified label type. -/
def HasBasis (E : Type u) : Prop :=
  ∃ Φ : FreeGroup E ≃* Pi1 (WeakBouquet E) (bouquetVertex E),
    ∀ e : E, Φ (FreeGroup.of e) = loopClass (bouquetLoop e)

/-- Generator-preserving bouquet bases transport along any equivalence of labels. -/
theorem basis_congr {E : Type u} {F : Type v} (e : E ≃ F) (hE : HasBasis E) : HasBasis F := by
  obtain ⟨Φ,hΦ⟩ := hE
  refine ⟨(FreeGroup.freeGroupCongr e.symm).trans (Φ.trans (fundamentalGroupEquiv e)),?_⟩
  intro y
  change fundamentalGroupEquiv e (Φ (FreeGroup.map e.symm (FreeGroup.of y))) = _
  rw [FreeGroup.map.of, hΦ, fundamentalGroupEquiv_loop, e.apply_symm_apply]

lemma basis_congr_iff {E : Type u} {F : Type v} (e : E ≃ F) : HasBasis E ↔ HasBasis F :=
  ⟨basis_congr e, basis_congr e.symm⟩

/-- The finite theorem reduces to adding one label, with no cardinality or
universe restriction hidden in the induction principle. -/
theorem finiteBasis_of_option
    (hoption : ∀ (E : Type u) [Finite E], HasBasis E → HasBasis (Option E)) :
    P202Specs.Topology.GraphFundamentalGroup.finiteBouquetFreeGroup.{u} := by
  intro E _
  apply Finite.induction_empty_option (P := HasBasis)
  · intro A B e hA
    exact basis_congr e hA
  · exact Bouquet.bouquetFreeGroup_empty PEmpty
  · intro A _ hA
    exact hoption A hA

/-- An arbitrary finite label type reduces to the empty bouquet and the
oriented sum step E ⊕ PUnit; the new summand has exactly one generator. -/
theorem finiteBasis_of_sum_singleton
    (hadd : ∀ (E : Type u) [Finite E],
      HasBasis E → HasBasis (E ⊕ PUnit.{u+1})) :
    P202Specs.Topology.GraphFundamentalGroup.finiteBouquetFreeGroup.{u} := by
  apply finiteBasis_of_option
  intro E _ hE
  exact basis_congr (Equiv.optionEquivSumPUnit E).symm (hadd E hE)

end P202.Topology.BouquetReindex

namespace P202.Topology.Bouquet
attribute [local instance] Classical.propDecidable

def midpoint : unitInterval := ⟨1/2,by norm_num⟩
lemma midpoint_ne_zero : midpoint ≠ 0 := by intro h; have := congrArg Subtype.val h; norm_num [midpoint] at this
lemma midpoint_ne_one : midpoint ≠ 1 := by intro h; have := congrArg Subtype.val h; norm_num [midpoint] at this

def collar {E : Type u} (S : Set E) : Set (WeakBouquet E) :=
  {x | ∀ e : E, e ∉ S → x ≠ bouquetLoop e midpoint}

lemma vertex_mem_collar {E : Type u} (S : Set E) : bouquetVertex E ∈ collar S := by
  intro e he hx
  exact ((loop_eq_vertex_iff e midpoint).mp hx.symm).elim midpoint_ne_zero midpoint_ne_one

lemma loop_mem_collar_iff {E : Type u} (S : Set E) (e : E) (t : unitInterval) :
    bouquetLoop e t ∈ collar S ↔ e ∈ S ∨ t ≠ midpoint := by
  constructor
  · intro h
    by_cases he : e ∈ S
    · exact Or.inl he
    · right
      intro ht
      exact h e he (congrArg (bouquetLoop e) ht)
  · intro h f hf hx
    have heq := (loop_eq_loop_iff f e midpoint t ⟨midpoint_ne_zero,midpoint_ne_one⟩).mp hx.symm
    rcases heq with ⟨rfl,rfl⟩
    exact h.elim hf (fun h => h rfl)

lemma collar_open {E : Type u} (S : Set E) : IsOpen (collar S) := by
  apply isClosed_compl_iff.mp
  apply closed_of_openEdge_subsingleton
  · exact fun h => h (vertex_mem_collar S)
  · intro e x hx y hy
    have hmid {z : WeakBouquet E} (hz : z ∈ (collar S)ᶜ ∩ openEdge e) :
        z = bouquetLoop e midpoint := by
      obtain ⟨t,ht,rfl⟩ := hz.2
      have hh : ¬(e ∈ S ∨ t ≠ midpoint) := by
        intro hh
        exact hz.1 ((loop_mem_collar_iff S e t).mpr hh)
      have htm : t = midpoint := not_not.mp (not_or.mp hh).2
      exact congrArg (bouquetLoop e) htm
    exact (hmid hx).trans (hmid hy).symm

def collarVertex {E : Type u} (S : Set E) : ↥(collar S) :=
  ⟨bouquetVertex E,vertex_mem_collar S⟩

lemma collar_inter {E : Type u} (S T : Set E) : collar S ∩ collar T = collar (S ∩ T) := by
  ext x
  constructor
  · rintro ⟨hS,hT⟩ e he
    by_cases hs : e ∈ S
    · exact hT e (fun ht => he ⟨hs,ht⟩)
    · exact hS e hs
  · intro h
    exact ⟨fun e he => h e (fun hh => he hh.1), fun e he => h e (fun hh => he hh.2)⟩

lemma collar_union_cover {E : Type u} (S T : Set E) (hST : S ∪ T = univ) :
    collar S ∪ collar T = univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hS : x ∈ collar S
  · exact Or.inl hS
  · right
    intro e he hx
    have heS : e ∈ S := by
      have hh : e ∈ S ∪ T := hST ▸ mem_univ e
      exact hh.resolve_right he
    apply hS
    intro f hf hxf
    have heq := (loop_eq_loop_iff e f midpoint midpoint
      ⟨midpoint_ne_zero,midpoint_ne_one⟩).mp (hx.symm.trans hxf)
    exact hf (heq.1 ▸ heS)

lemma map_subtype_mem_collar {E : Type u} (S : Set E) (x : WeakBouquet S) :
    (map (Subtype.val : S → E)).map x ∈ collar S := by
  induction x using Quotient.inductionOn with
  | h a =>
    rcases a with _ | ⟨e,t⟩
    · exact vertex_mem_collar S
    · change bouquetLoop e.val t ∈ collar S
      exact (loop_mem_collar_iff S e.val t).mpr (Or.inl e.property)

def collarInclusion {E : Type u} (S : Set E) :
    PointedMap (WeakBouquet S) ↥(collar S) (bouquetVertex S) (collarVertex S) :=
  ⟨⟨fun x => ⟨(map (Subtype.val : S → E)).map x,map_subtype_mem_collar S x⟩,
    (map (Subtype.val : S → E)).map.continuous.subtype_mk _⟩,rfl⟩

def collarRetraction {E : Type u} (S : Set E) :
    PointedMap ↥(collar S) (WeakBouquet S) (collarVertex S) (bouquetVertex S) :=
  ⟨⟨fun x => (retract S).map x.val,
    (retract S).map.continuous.comp continuous_subtype_val⟩,rfl⟩

@[simp] lemma collarInclusion_vertex {E : Type u} (S : Set E) :
    (collarInclusion S).map (bouquetVertex S) = collarVertex S := rfl
@[simp] lemma collarRetraction_vertex {E : Type u} (S : Set E) :
    (collarRetraction S).map (collarVertex S) = bouquetVertex S := rfl
@[simp] lemma collarInclusion_loop {E : Type u} (S : Set E) (e : S) (t : unitInterval) :
    ((collarInclusion S).map (bouquetLoop e t)).val = bouquetLoop e.val t := rfl
@[simp] lemma collarRetraction_inclusion {E : Type u} (S : Set E) (x : WeakBouquet S) :
    (collarRetraction S).map ((collarInclusion S).map x) = x := by
  exact congrArg (fun f : PointedMap (WeakBouquet S) (WeakBouquet S)
    (bouquetVertex S) (bouquetVertex S) => f.map x) (retract_map S)

end P202.Topology.Bouquet

namespace P202.Topology.Bouquet

abbrev CollarParameter {E : Type u} (S : Set E) (e : E) :=
  {t : unitInterval // e ∈ S ∨ t ≠ midpoint}

abbrev CollarPresentation {E : Type u} (S : Set E) :=
  Unit ⊕ Σ e : E, CollarParameter S e

lemma collarParameter_open {E : Type u} (S : Set E) (e : E) :
    IsOpen {t : unitInterval | e ∈ S ∨ t ≠ midpoint} := by
  classical
  by_cases he : e ∈ S
  · simp [he]
  · simpa only [he, false_or] using
      (isOpen_ne : IsOpen {t : unitInterval | t ≠ midpoint})

def collarProjection {E : Type u} (S : Set E) :
    C(CollarPresentation S,↥(collar S)) where
  toFun := Sum.elim (fun _ => collarVertex S)
    (fun p => ⟨bouquetLoop p.1 p.2.val,(loop_mem_collar_iff S p.1 p.2.val).mpr p.2.property⟩)
  continuous_toFun := continuous_sum_dom.mpr ⟨continuous_const,continuous_sigma fun e =>
    ((bouquetLoop e).continuous.comp continuous_subtype_val).subtype_mk _⟩

lemma collarProjection_surjective {E : Type u} (S : Set E) :
    Function.Surjective (collarProjection S) := by
  rintro ⟨x,hx⟩
  induction x using Quotient.inductionOn with
  | h a =>
    rcases a with _ | ⟨e,t⟩
    · exact ⟨.inl (),rfl⟩
    · refine ⟨.inr ⟨e,⟨t,(loop_mem_collar_iff S e t).mp hx⟩⟩,rfl⟩

/-- The punctured intervals give the actual open-collar subspace topology. -/
lemma collarProjection_quotient {E : Type u} (S : Set E) :
    IsQuotientMap (collarProjection S) := by
  rw [isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun U => ?_, collarProjection_surjective S⟩
  constructor
  · intro hU
    apply (collar_open S).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mpr
    apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
    apply isOpen_sum_iff.mpr
    constructor
    · exact isOpen_discrete _
    · apply isOpen_sigma_iff.mpr
      intro e
      have hchart : IsOpen ((fun t : CollarParameter S e =>
          collarProjection S (.inr ⟨e,t⟩)) ⁻¹' U) :=
        (isOpen_sigma_iff.mp (isOpen_sum_iff.mp hU).2) e
      have heq : (fun t : unitInterval => bouquetLoop e t) ⁻¹' (Subtype.val '' U) =
          Subtype.val '' ((fun t : CollarParameter S e =>
            collarProjection S (.inr ⟨e,t⟩)) ⁻¹' U) := by
        ext t
        constructor
        · rintro ⟨x,hx,hxt⟩
          have ht : e ∈ S ∨ t ≠ midpoint := (loop_mem_collar_iff S e t).mp
            (by
              have hx' : x.val ∈ collar S := x.property
              rw [hxt] at hx'
              exact hx')
          refine ⟨⟨t,ht⟩,?_,rfl⟩
          change collarProjection S (.inr ⟨e,⟨t,ht⟩⟩) ∈ U
          convert hx using 1
          exact Subtype.ext hxt.symm
        · rintro ⟨t,ht,rfl⟩
          exact ⟨collarProjection S (.inr ⟨e,t⟩),ht,rfl⟩
      change IsOpen ((fun t : unitInterval => bouquetLoop e t) ⁻¹' (Subtype.val '' U))
      rw [heq]
      exact (collarParameter_open S e).isOpenMap_subtype_val _ hchart
  · exact fun hU => hU.preimage (collarProjection S).continuous
end P202.Topology.Bouquet

namespace P202.Topology.Bouquet

attribute [local instance] Classical.propDecidable

/-- Shrink each side of the punctured interval toward its nearest endpoint. -/
def collarShrink (s t : unitInterval) : unitInterval :=
  if (t : ℝ) ≤ 1 / 2 then unitInterval.symm s * t
    else unitInterval.symm (unitInterval.symm s * unitInterval.symm t)

@[simp] lemma collarShrink_zero (t : unitInterval) : collarShrink 0 t = t := by
  unfold collarShrink
  split_ifs <;> simp

@[simp] lemma collarShrink_left (s : unitInterval) : collarShrink s 0 = 0 := by
  simp [collarShrink]

@[simp] lemma collarShrink_right (s : unitInterval) : collarShrink s 1 = 1 := by
  unfold collarShrink
  rw [ite_eq_right (by norm_num : ¬((1 : unitInterval) : ℝ) ≤ 1 / 2)]
  simp

lemma collarShrink_ne_midpoint (s t : unitInterval) (ht : t ≠ midpoint) :
    collarShrink s t ≠ midpoint := by
  have ht' : (t : ℝ) ≠ 1 / 2 := fun hh => ht (Subtype.ext hh)
  unfold collarShrink
  split_ifs with h
  · have hlt : (t : ℝ) < 1 / 2 := lt_of_le_of_ne h ht'
    have hle : ((unitInterval.symm s * t : unitInterval) : ℝ) ≤ (t : ℝ) :=
      mul_le_of_le_one_left t.property.1 (unitInterval.symm s).property.2
    intro hh
    have heq := congrArg Subtype.val hh
    change _ = (1 / 2 : ℝ) at heq
    linarith
  · have hlt : 1 / 2 < (t : ℝ) := lt_of_not_ge h
    have hle : ((unitInterval.symm s * unitInterval.symm t : unitInterval) : ℝ) ≤
        (unitInterval.symm t : ℝ) :=
      mul_le_of_le_one_left (unitInterval.symm t).property.1 (unitInterval.symm s).property.2
    intro hh
    have heq := congrArg Subtype.val hh
    change 1 - _ = (1 / 2 : ℝ) at heq
    change _ ≤ 1 - (t : ℝ) at hle
    linarith

/-- Joint continuity of shrinking on every punctured interval fiber. -/
def collarParameterHomotopy {E : Type u} (S : Set E) (e : E) :
    C(unitInterval × CollarParameter S e,CollarParameter S e) := by
  classical
  by_cases he : e ∈ S
  · exact ⟨fun z => z.2,continuous_snd⟩
  · refine ⟨fun z => ⟨collarShrink z.1 z.2.val,
      Or.inr (collarShrink_ne_midpoint _ _ (z.2.property.resolve_left he))⟩,?_⟩
    apply Continuous.subtype_mk
    unfold collarShrink
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const
    intro z hz
    exact ((z.2.property.resolve_left he) (Subtype.ext hz)).elim

lemma collarParameterHomotopy_val {E : Type u} (S : Set E) (e : E)
    (s : unitInterval) (t : CollarParameter S e) :
    (collarParameterHomotopy S e (s,t)).val =
      if e ∈ S then t.val else collarShrink s t.val := by
  classical
  unfold collarParameterHomotopy
  split_ifs <;> rfl

@[simp] lemma collarParameterHomotopy_zero {E : Type u} (S : Set E) (e : E)
    (t : CollarParameter S e) : collarParameterHomotopy S e (0,t) = t := by
  apply Subtype.ext
  rw [collarParameterHomotopy_val]
  split_ifs <;> simp
end P202.Topology.Bouquet

namespace P202.Topology.Bouquet
attribute [local instance] Classical.propDecidable

def collarShrinkRaw {E : Type u} (S : Set E) (s : unitInterval) :
    BouquetPresentation E → WeakBouquet E
  | .inl _ => bouquetVertex E
  | .inr ⟨e,t⟩ => if e ∈ S then bouquetLoop e t else bouquetLoop e (collarShrink s t)

lemma collarShrinkRaw_vertex {E : Type u} (S : Set E) (s : unitInterval)
    (p : BouquetPresentation E) (hp : bouquetVertexLocus p) :
    collarShrinkRaw S s p = bouquetVertex E := by
  rcases p with _ | ⟨e,t⟩
  · rfl
  · rcases hp with rfl | rfl <;>
      simp [collarShrinkRaw, (bouquetLoop e).source, (bouquetLoop e).target]

def collarShrinkMap {E : Type u} (S : Set E) (s : unitInterval) : WeakBouquet E → WeakBouquet E :=
  Quotient.lift (collarShrinkRaw S s) (by
    intro p q h
    rcases h with rfl | ⟨hp,hq⟩
    · rfl
    · exact (collarShrinkRaw_vertex S s p hp).trans (collarShrinkRaw_vertex S s q hq).symm)

@[simp] lemma collarShrinkMap_vertex {E : Type u} (S : Set E) (s : unitInterval) :
    collarShrinkMap S s (bouquetVertex E) = bouquetVertex E := rfl

@[simp] lemma collarShrinkMap_loop {E : Type u} (S : Set E) (s : unitInterval)
    (e : E) (t : unitInterval) :
    collarShrinkMap S s (bouquetLoop e t) =
      if e ∈ S then bouquetLoop e t else bouquetLoop e (collarShrink s t) := rfl

lemma collarShrinkMap_mem {E : Type u} (S : Set E) (s : unitInterval)
    (x : WeakBouquet E) (hx : x ∈ collar S) : collarShrinkMap S s x ∈ collar S := by
  induction x using Quotient.inductionOn with
  | h p =>
    rcases p with _ | ⟨e,t⟩
    · exact vertex_mem_collar S
    · change collarShrinkMap S s (bouquetLoop e t) ∈ collar S
      change bouquetLoop e t ∈ collar S at hx
      rw [collarShrinkMap_loop]
      split_ifs with he
      · exact hx
      · apply (loop_mem_collar_iff S e _).mpr
        exact Or.inr (collarShrink_ne_midpoint s t
          (((loop_mem_collar_iff S e t).mp hx).resolve_left he))

def collarHomotopyMap {E : Type u} (S : Set E) :
    ↥(collar S) × unitInterval → ↥(collar S) :=
  fun z => ⟨collarShrinkMap S z.2 z.1.val,collarShrinkMap_mem S z.2 z.1.val z.1.property⟩

@[simp] lemma collarHomotopyMap_vertex {E : Type u} (S : Set E) (s : unitInterval) :
    collarHomotopyMap S (collarVertex S,s) = collarVertex S := rfl

lemma collarHomotopyMap_loop {E : Type u} (S : Set E) (e : E) (t s : unitInterval)
    (ht : bouquetLoop e t ∈ collar S) :
    (collarHomotopyMap S (⟨bouquetLoop e t,ht⟩,s)).val =
      if e ∈ S then bouquetLoop e t else bouquetLoop e (collarShrink s t) := rfl

def collarEdgeHomotopy {E : Type u} (S : Set E) (e : E) :
    C(CollarParameter S e × unitInterval,↥(collar S)) :=
  (collarProjection S).comp ⟨fun z => .inr ⟨e,collarParameterHomotopy S e (z.2,z.1)⟩,
    continuous_inr.comp (continuous_sigmaMk.comp
      ((collarParameterHomotopy S e).continuous.comp continuous_swap))⟩

lemma collarHomotopyMap_edge {E : Type u} (S : Set E) (e : E)
    (t : CollarParameter S e) (s : unitInterval) :
    collarHomotopyMap S (collarProjection S (.inr ⟨e,t⟩),s) =
      collarEdgeHomotopy S e (t,s) := by
  apply Subtype.ext
  change (if e ∈ S then bouquetLoop e t.val else bouquetLoop e (collarShrink s t.val)) =
    bouquetLoop e (collarParameterHomotopy S e (s,t)).val
  rw [collarParameterHomotopy_val]
  split_ifs <;> rfl

/-- Joint continuity follows from the open collar's quotient by its punctured
intervals and the product-interval quotient theorem. -/
lemma collarHomotopyMap_continuous {E : Type u} (S : Set E) :
    Continuous (collarHomotopyMap S) := by
  apply (quotientProductInterval _ (collarProjection_quotient S)).continuous_iff.mpr
  let e := Homeomorph.sumProdDistrib
    (X := Unit) (Y := Σ e : E, CollarParameter S e) (Z := unitInterval)
  apply e.symm.isQuotientMap.continuous_iff.mpr
  apply continuous_sum_dom.mpr
  constructor
  · change Continuous (fun _ : Unit × unitInterval => collarVertex S)
    exact continuous_const
  · let e' := Homeomorph.sigmaProdDistrib
      (X := fun e : E => CollarParameter S e) (Y := unitInterval)
    apply e'.symm.isQuotientMap.continuous_iff.mpr
    apply continuous_sigma
    intro e
    change Continuous (fun z : CollarParameter S e × unitInterval =>
      collarHomotopyMap S (collarProjection S (.inr ⟨e,z.1⟩),z.2))
    have hh : (fun z : CollarParameter S e × unitInterval =>
        collarHomotopyMap S (collarProjection S (.inr ⟨e,z.1⟩),z.2)) =
        collarEdgeHomotopy S e := funext fun z => collarHomotopyMap_edge S e z.1 z.2
    rw [hh]
    exact (collarEdgeHomotopy S e).continuous
end P202.Topology.Bouquet

namespace P202.Topology.Bouquet
attribute [local instance] Classical.propDecidable

@[simp] lemma collarShrinkMap_zero {E : Type u} (S : Set E) (x : WeakBouquet E) :
    collarShrinkMap S 0 x = x := by
  induction x using Quotient.inductionOn with
  | h p =>
    rcases p with _ | ⟨e,t⟩
    · rfl
    · change (if e ∈ S then bouquetLoop e t else bouquetLoop e (collarShrink 0 t)) =
        bouquetLoop e t
      simp

lemma collarShrinkMap_one {E : Type u} (S : Set E) (x : WeakBouquet E) :
    collarShrinkMap S 1 x =
      (map (Subtype.val : S → E)).map ((retract S).map x) := by
  induction x using Quotient.inductionOn with
  | h p =>
    rcases p with _ | ⟨e,t⟩
    · rfl
    · change collarShrinkMap S 1 (bouquetLoop e t) =
        (map (Subtype.val : S → E)).map ((retract S).map (bouquetLoop e t))
      rw [collarShrinkMap_loop]
      by_cases he : e ∈ S
      · rw [ite_eq_left he, retract_loop S ⟨e,he⟩, map_loop]
      · rw [ite_eq_right he]
        have hretract : (retract S).map (bouquetLoop e t) = bouquetVertex S := by
          simp only [retract, desc_loop, dite_eq_right he, Path.refl_apply]
        rw [hretract,map_vertex]
        unfold collarShrink
        split_ifs <;> simp [(bouquetLoop e).source,(bouquetLoop e).target]

@[simp] lemma collarHomotopyMap_zero {E : Type u} (S : Set E) (x : ↥(collar S)) :
    collarHomotopyMap S (x,0) = x := by
  apply Subtype.ext
  exact collarShrinkMap_zero S x.val

lemma collarHomotopyMap_one {E : Type u} (S : Set E) (x : ↥(collar S)) :
    collarHomotopyMap S (x,1) =
      (collarInclusion S).map ((collarRetraction S).map x) := by
  apply Subtype.ext
  exact collarShrinkMap_one S x.val

lemma collarHomotopyMap_inclusion {E : Type u} (S : Set E)
    (x : WeakBouquet S) (s : unitInterval) :
    collarHomotopyMap S ((collarInclusion S).map x,s) = (collarInclusion S).map x := by
  apply Subtype.ext
  induction x using Quotient.inductionOn with
  | h p =>
    rcases p with _ | ⟨e,t⟩
    · rfl
    · change collarShrinkMap S s (bouquetLoop e.val t) = bouquetLoop e.val t
      rw [collarShrinkMap_loop,ite_eq_left e.property]

/-- A based strong deformation of the collar onto its selected circles. -/
def collarHomotopy {E : Type u} (S : Set E) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(collar S))
      ((collarInclusion S).map.comp (collarRetraction S).map) where
  toFun z := collarHomotopyMap S (z.2,z.1)
  continuous_toFun := (collarHomotopyMap_continuous S).comp continuous_swap
  map_zero_left := collarHomotopyMap_zero S
  map_one_left := collarHomotopyMap_one S

@[simp] lemma collarHomotopy_vertex {E : Type u} (S : Set E) (s : unitInterval) :
    collarHomotopy S (s,collarVertex S) = collarVertex S := rfl

/-- The inclusion of the selected weak bouquet into its open collar is a
homotopy equivalence, with the actual restriction of the global retraction. -/
def collarHomotopyEquiv {E : Type u} (S : Set E) : WeakBouquet S ≃ₕ ↥(collar S) where
  toFun := (collarInclusion S).map
  invFun := (collarRetraction S).map
  left_inv := by
    have hh : (collarRetraction S).map.comp (collarInclusion S).map =
        ContinuousMap.id (WeakBouquet S) := by
      ext x
      exact collarRetraction_inclusion S x
    rw [hh]
  right_inv := ⟨(collarHomotopy S).symm⟩

/-- The homomorphism here is induced by the actual geometric inclusion. -/
theorem collarInclusion_induced_bijective {E : Type u} (S : Set E) :
    Function.Bijective (collarInclusion S).induced := by
  exact P202.Topology.homotopyEquiv_induced_bijective (collarHomotopyEquiv S)
    (bouquetVertex S) (collarVertex S) rfl

/-- The collar of the empty subbouquet is the contractible star of punctured
edge halves used as the van Kampen intersection. -/
theorem collar_empty_contractible (E : Type u) : ContractibleSpace ↥(collar (∅ : Set E)) := by
  have hx (x : WeakBouquet (∅ : Set E)) : x = bouquetVertex (∅ : Set E) := by
    induction x using Quotient.inductionOn with
    | h p =>
      rcases p with _ | ⟨e,t⟩
      · rfl
      · exact e.property.elim
  letI : Nonempty (WeakBouquet (∅ : Set E)) := ⟨bouquetVertex _⟩
  letI : Subsingleton (WeakBouquet (∅ : Set E)) :=
    ⟨fun x y => (hx x).trans (hx y).symm⟩
  letI : ContractibleSpace (WeakBouquet (∅ : Set E)) := inferInstance
  exact (collarHomotopyEquiv (∅ : Set E)).symm.contractibleSpace
end P202.Topology.Bouquet

namespace P202.Topology.Bouquet
attribute [local instance] Classical.propDecidable

def initialLoopSegment {E : Type u} (e : E) (t : unitInterval) :
    Path (bouquetVertex E) (bouquetLoop e t) where
  toFun s := bouquetLoop e (s*t)
  continuous_toFun := (bouquetLoop e).continuous.comp (by fun_prop)
  source' := by simp
  target' := by simp

def finalLoopSegment {E : Type u} (e : E) (t : unitInterval) :
    Path (bouquetVertex E) (bouquetLoop e t) where
  toFun s := bouquetLoop e (unitInterval.symm (s * unitInterval.symm t))
  continuous_toFun := (bouquetLoop e).continuous.comp (by fun_prop)
  source' := by simp
  target' := by simp

lemma initialLoopSegment_mem_collar {E : Type u} (S : Set E) (e : E) (t : unitInterval)
    (ht : e ∈ S ∨ (t : ℝ) < 1/2) (s : unitInterval) :
    initialLoopSegment e t s ∈ collar S := by
  apply (loop_mem_collar_iff S e (s*t)).mpr
  rcases ht with he | ht
  · exact Or.inl he
  · right
    intro hh
    have hh' := congrArg Subtype.val hh
    change (s : ℝ) * (t : ℝ) = 1/2 at hh'
    have hle : (s : ℝ) * (t : ℝ) ≤ t := by nlinarith [s.property.2,t.property.1]
    linarith

lemma finalLoopSegment_mem_collar {E : Type u} (S : Set E) (e : E) (t : unitInterval)
    (ht : (1/2 : ℝ) < t) (s : unitInterval) :
    finalLoopSegment e t s ∈ collar S := by
  apply (loop_mem_collar_iff S e _).mpr
  right
  intro hh
  have hh' := congrArg Subtype.val hh
  change 1 - (s : ℝ)*(1-(t : ℝ)) = 1/2 at hh'
  have hle : (s : ℝ)*(1-(t : ℝ)) ≤ 1-(t : ℝ) := by
    nlinarith [s.property.2,t.property.2]
  linarith

private def pathInSet {Z : Type u} [TopologicalSpace Z] (A : Set Z)
    {x y : Z} (hx : x ∈ A) (hy : y ∈ A) (p : Path x y) (hp : ∀ t, p t ∈ A) :
    Path (⟨x,hx⟩ : A) ⟨y,hy⟩ where
  toFun t := ⟨p t,hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

lemma collar_joined_vertex {E : Type u} (S : Set E) (x : ↥(collar S)) :
    Joined (collarVertex S) x := by
  rcases x with ⟨x,hx⟩
  induction x using Quotient.inductionOn with
  | h a =>
    rcases a with _ | ⟨e,t⟩
    · exact ⟨Path.refl _⟩
    · have ht := (loop_mem_collar_iff S e t).mp hx
      rcases lt_trichotomy (t : ℝ) (1/2 : ℝ) with hlt | heq | hgt
      · exact ⟨pathInSet (collar S) (vertex_mem_collar S) hx
          (initialLoopSegment e t) (initialLoopSegment_mem_collar S e t (Or.inr hlt))⟩
      · have ht' : t = midpoint := Subtype.ext heq
        have he : e ∈ S := ht.resolve_right (not_not.mpr ht')
        exact ⟨pathInSet (collar S) (vertex_mem_collar S) hx
          (initialLoopSegment e t) (initialLoopSegment_mem_collar S e t (Or.inl he))⟩
      · exact ⟨pathInSet (collar S) (vertex_mem_collar S) hx
          (finalLoopSegment e t) (finalLoopSegment_mem_collar S e t hgt)⟩

theorem collar_pathConnectedSpace {E : Type u} (S : Set E) : PathConnectedSpace ↥(collar S) := by
  apply pathConnectedSpace_iff_eq.mpr
  exact ⟨collarVertex S, Set.eq_univ_of_forall (collar_joined_vertex S)⟩

end P202.Topology.Bouquet

namespace P202.Topology.Bouquet

def collarAmbientMap {E : Type u} (S : Set E) :
    PointedMap ↥(collar S) (WeakBouquet E) (collarVertex S) (bouquetVertex E) :=
  ⟨⟨Subtype.val,continuous_subtype_val⟩,rfl⟩

lemma collarAmbientMap_inclusion {E : Type u} (S : Set E) :
    (collarAmbientMap S).comp (collarInclusion S) = map (Subtype.val : S → E) := by
  apply pointedMap_ext
  rfl

lemma collarAmbientMap_inclusion_induced {E : Type u} (S : Set E) :
    (collarAmbientMap S).induced.comp (collarInclusion S).induced =
      (map (Subtype.val : S → E)).induced := by
  rw [← P202.Topology.induced_comp, collarAmbientMap_inclusion]

end P202.Topology.Bouquet

namespace P202.Topology.BouquetPartition
open P202.Cellular P202Specs.Topology BouquetReindex

/-- The original left labels, identified with their actual range in the sum. -/
def inlRangeEquiv (E : Type u) (F : Type v) :
    E ≃ ↥(Set.range (Sum.inl : E → E ⊕ F)) :=
  Equiv.ofInjective Sum.inl Sum.inl_injective

/-- The original right labels, identified with their actual range in the sum. -/
def inrRangeEquiv (E : Type u) (F : Type v) :
    F ≃ ↥(Set.range (Sum.inr : F → E ⊕ F)) :=
  Equiv.ofInjective Sum.inr Sum.inr_injective

@[simp] lemma inlRangeEquiv_apply (E : Type u) (F : Type v) (e : E) :
    inlRangeEquiv E F e = ⟨Sum.inl e,Set.mem_range_self e⟩ := rfl

@[simp] lemma inrRangeEquiv_apply (E : Type u) (F : Type v) (f : F) :
    inrRangeEquiv E F f = ⟨Sum.inr f,Set.mem_range_self f⟩ := rfl

lemma inl_inr_union (E : Type u) (F : Type v) :
    Set.range (Sum.inl : E → E ⊕ F) ∪ Set.range (Sum.inr : F → E ⊕ F) = Set.univ :=
  Set.range_inl_union_range_inr

lemma inl_inr_inter (E : Type u) (F : Type v) :
    Set.range (Sum.inl : E → E ⊕ F) ∩ Set.range (Sum.inr : F → E ⊕ F) = ∅ :=
  Set.range_inl_inter_range_inr

/-- A basis indexed by the original E labels on a bouquet whose labels are
the image of any injection; exact generator values include the subtype witness. -/
theorem basis_on_range {E : Type u} {L : Type v} (f : E → L)
    (hf : Function.Injective f) (hE : HasBasis E) :
    ∃ Φ : FreeGroup E ≃* Pi1 (WeakBouquet (Set.range f)) (bouquetVertex (Set.range f)),
      ∀ e : E, Φ (FreeGroup.of e) = loopClass (bouquetLoop ⟨f e,Set.mem_range_self e⟩) := by
  obtain ⟨Φ,hΦ⟩ := hE
  refine ⟨Φ.trans (fundamentalGroupEquiv (Equiv.ofInjective f hf)),?_⟩
  intro e
  change fundamentalGroupEquiv (Equiv.ofInjective f hf) (Φ (FreeGroup.of e)) = _
  rw [hΦ,fundamentalGroupEquiv_loop]
  rfl

/-- The left-range bouquet carries exactly the old oriented edge basis. -/
theorem basis_on_range_inl (E : Type u) (F : Type v) (hE : HasBasis E) :
    ∃ Φ : FreeGroup E ≃* Pi1
        (WeakBouquet (Set.range (Sum.inl : E → E ⊕ F)))
        (bouquetVertex (Set.range (Sum.inl : E → E ⊕ F))),
      ∀ e : E, Φ (FreeGroup.of e) =
        loopClass (bouquetLoop ⟨Sum.inl e,Set.mem_range_self e⟩) :=
  basis_on_range Sum.inl Sum.inl_injective hE

/-- The right-range bouquet carries exactly the new oriented edge basis. -/
theorem basis_on_range_inr (E : Type u) (F : Type v) (hF : HasBasis F) :
    ∃ Φ : FreeGroup F ≃* Pi1
        (WeakBouquet (Set.range (Sum.inr : F → E ⊕ F)))
        (bouquetVertex (Set.range (Sum.inr : F → E ⊕ F))),
      ∀ f : F, Φ (FreeGroup.of f) =
        loopClass (bouquetLoop ⟨Sum.inr f,Set.mem_range_self f⟩) :=
  basis_on_range Sum.inr Sum.inr_injective hF

/-- Ambient inclusion sends an image-subtype generator to its original whole
edge loop. This is the generator formula needed after a collar equivalence. -/
lemma basis_on_range_ambient {E : Type u} {L : Type v} (f : E → L)
    (Φ : FreeGroup E ≃* Pi1 (WeakBouquet (Set.range f)) (bouquetVertex (Set.range f)))
    (hΦ : ∀ e : E, Φ (FreeGroup.of e) =
      loopClass (bouquetLoop ⟨f e,Set.mem_range_self e⟩)) (e : E) :
    (Bouquet.map (Subtype.val : Set.range f → L)).induced (Φ (FreeGroup.of e)) =
      loopClass (bouquetLoop (f e)) := by
  rw [hΦ,Bouquet.map_induced]

end P202.Topology.BouquetPartition

namespace P202.Topology
open P202Specs.Topology.VanKampen

theorem vanKampen_coproduct {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (pU : IsPathConnected U) (pV : IsPathConnected V) (pUV : IsPathConnected (U ∩ V))
    (x : X) (hx : x ∈ U ∩ V)
    [Subsingleton (Pi1 ↥(U ∩ V) ⟨x,hx⟩)] :
    ∀ (H : Type u) [Group H]
      (f : Pi1 U ⟨x,hx.1⟩ →* H) (g : Pi1 V ⟨x,hx.2⟩ →* H),
      ∃! φ : Pi1 X x →* H,
        φ.comp (ambientMap U x hx.1).induced = f ∧
        φ.comp (ambientMap V x hx.2).induced = g := by
  intro H _ f g
  apply (vanKampen X U V hU hV hUV pU pV pUV x hx).2 H f g
  ext a
  rw [Subsingleton.elim a 1]
  simp
end P202.Topology

namespace P202.Topology.BouquetPartition
open Bouquet BouquetReindex P202Specs.Topology.VanKampen
variable {E F : Type u}

theorem basis_sum_of_collar
    (hE : HasBasis E) (hF : HasBasis F)
    (cS : Pi1 (WeakBouquet (range (Sum.inl : E → E ⊕ F))) (bouquetVertex _) ≃*
      Pi1 ↥(collar (range (Sum.inl : E → E ⊕ F))) (collarVertex _))
    (hcS : ∀ b, cS b = (collarInclusion (range (Sum.inl : E → E ⊕ F))).induced b)
    (cT : Pi1 (WeakBouquet (range (Sum.inr : F → E ⊕ F))) (bouquetVertex _) ≃*
      Pi1 ↥(collar (range (Sum.inr : F → E ⊕ F))) (collarVertex _))
    (hcT : ∀ b, cT b = (collarInclusion (range (Sum.inr : F → E ⊕ F))).induced b)
    (hempty : ContractibleSpace ↥(collar (∅ : Set (E ⊕ F)))) : HasBasis (E ⊕ F) := by
  let S : Set (E ⊕ F) := range Sum.inl
  let T : Set (E ⊕ F) := range Sum.inr
  let x : WeakBouquet (E ⊕ F) := bouquetVertex _
  have hx : x ∈ collar S ∧ x ∈ collar T := ⟨vertex_mem_collar S,vertex_mem_collar T⟩
  have hST : collar S ∩ collar T = collar (∅ : Set (E ⊕ F)) := by
    rw [collar_inter]
    exact congrArg collar (inl_inr_inter E F)
  letI : ContractibleSpace ↥(collar S ∩ collar T) :=
    @Homeomorph.contractibleSpace _ _ _ _ hempty (Homeomorph.setCongr hST)
  letI := collar_pathConnectedSpace S
  letI := collar_pathConnectedSpace T
  obtain ⟨ΦS,hΦS⟩ := basis_on_range_inl E F hE
  obtain ⟨ΦT,hΦT⟩ := basis_on_range_inr E F hF
  let iS := (collarAmbientMap S).induced
  let iT := (collarAmbientMap T).induced
  have hup := vanKampen_coproduct (collar S) (collar T) (collar_open S) (collar_open T)
    (collar_union_cover S T (inl_inr_union E F))
    (isPathConnected_iff_pathConnectedSpace.mpr inferInstance)
    (isPathConnected_iff_pathConnectedSpace.mpr inferInstance)
    (isPathConnected_iff_pathConnectedSpace.mpr inferInstance) x hx
  obtain ⟨Φ,hΦl,hΦr⟩ := freeGroup_sum_equiv_of_pushout
    (ΦS.trans cS) (ΦT.trans cT) iS iT hup
  refine ⟨Φ,?_⟩
  intro z
  cases z with
  | inl e =>
    rw [hΦl]
    change iS (cS (ΦS (FreeGroup.of e))) = _
    rw [hcS]
    change (collarAmbientMap S).induced
      ((collarInclusion S).induced (ΦS (FreeGroup.of e))) = _
    rw [← MonoidHom.comp_apply, collarAmbientMap_inclusion_induced]
    exact basis_on_range_ambient Sum.inl ΦS hΦS e
  | inr f =>
    rw [hΦr]
    change iT (cT (ΦT (FreeGroup.of f))) = _
    rw [hcT]
    change (collarAmbientMap T).induced
      ((collarInclusion T).induced (ΦT (FreeGroup.of f))) = _
    rw [← MonoidHom.comp_apply, collarAmbientMap_inclusion_induced]
    exact basis_on_range_ambient Sum.inr ΦT hΦT f

end P202.Topology.BouquetPartition

namespace P202.Topology.BouquetPartition
open Bouquet BouquetReindex

/-- The weak bouquet on a disjoint union has the two original oriented bases. -/
theorem basis_sum {E F : Type u} (hE : HasBasis E) (hF : HasBasis F) :
    HasBasis (E ⊕ F) :=
  basis_sum_of_collar hE hF
    (MulEquiv.ofBijective (collarInclusion _).induced (collarInclusion_induced_bijective _))
    (fun _ => rfl)
    (MulEquiv.ofBijective (collarInclusion _).induced (collarInclusion_induced_bijective _))
    (fun _ => rfl) (collar_empty_contractible (E ⊕ F))

end P202.Topology.BouquetPartition

namespace P202.Topology

/-- Finite bouquets have precisely their positively oriented edge basis.
The induction uses actual open collars, their deformation equivalences, and
the group pushout furnished by van Kampen. -/
theorem finiteBouquetFreeGroup :
    P202Specs.Topology.GraphFundamentalGroup.finiteBouquetFreeGroup.{u} := by
  apply BouquetReindex.finiteBasis_of_sum_singleton
  intro E _ hE
  exact BouquetPartition.basis_sum hE
    (BouquetSingleton.bouquetFreeGroup_unique PUnit.{u+1})

/-- The edge basis theorem for arbitrary weak bouquets, including empty and
infinite generator types. -/
theorem bouquetFreeGroup : P202Specs.Topology.GraphFundamentalGroup.bouquetFreeGroup.{u} :=
  Bouquet.bouquetFreeGroup_of_finite finiteBouquetFreeGroup

/-- The graph conclusion of Theorem 2.5: a spanning maximal tree exists, and
the actual oriented edges outside it freely generate the fundamental group
at every basepoint, with no finiteness or local finiteness restriction. -/
theorem graphFundamentalGroup : P202Specs.Topology.GraphFundamentalGroup.graphFundamentalGroup.{u} :=
  graphFundamentalGroup_of_finiteBouquetFreeGroup finiteBouquetFreeGroup

end P202.Topology
