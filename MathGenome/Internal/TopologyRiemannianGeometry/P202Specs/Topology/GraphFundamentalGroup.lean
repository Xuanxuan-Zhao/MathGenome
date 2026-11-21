import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.FundamentalGroupoid
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! The graph assertion of paper.tex, Theorem 2.5, lines 674–707.
Graphs mean CW complexes with no cells of dimension at least two. Cell labels
remain the edge labels, so loops and parallel edges are retained. The support
simple graph is used only to characterize forests: a forest has no loop, no
parallel selected edges, and acyclic support. No finiteness is assumed.
The parametrization of each characteristic disk chooses one orientation of
each edge. The specified free generators follow that orientation.
-/
noncomputable section
open Set Topology
open scoped unitInterval
universe u v

namespace P202.Cellular

/-- An oriented multigraph, with no restrictions on loops or multiplicities. -/
structure EdgeEndpoints (V : Type u) (E : Type v) where
  source : E → V
  target : E → V

namespace EdgeEndpoints
variable {V : Type u} {E : Type v} (d : EdgeEndpoints V E)

/-- The unordered ends retain multiplicities as edge labels in the domain. -/
def ends (e : E) : Sym2 V := s(d.source e, d.target e)

/-- The simple support forgets multiplicity only here, never in the set of
free generators. Loops are explicitly excluded from this support. -/
def support (T : Set E) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e ∈ T,
    (d.source e = x ∧ d.target e = y) ∨ (d.source e = y ∧ d.target e = x)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _e he => ⟨he.1, he.2.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Acyclicity for a multigraph, including the length-one and length-two
cycles that would disappear on passing to the simple support. -/
def IsForest (T : Set E) : Prop :=
  (∀ e ∈ T, d.source e ≠ d.target e) ∧
  Set.InjOn d.ends T ∧ (d.support T).IsAcyclic

/-- All vertices are retained, including isolated vertices. -/
def IsSpanningTree (T : Set E) : Prop :=
  d.IsForest T ∧ (d.support T).Connected

end EdgeEndpoints

/-- Dimension at most one; a single vertex is allowed. -/
def IsGraph (X : Type u) [TopologicalSpace X] [CWStructure X] : Prop :=
  ∀ n : ℕ, 2 ≤ n → IsEmpty (Cell X n)

abbrev GraphVertex (X : Type u) [TopologicalSpace X] [CWStructure X] :=
  skeletonLT X 1

/-- The straight parametrization of the actual Euclidean one-disk. -/
def edgeDiskPoint (t : unitInterval) : Disk 1 :=
  ⟨EuclideanSpace.single 0 (2 * (t : ℝ) - 1), by
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖EuclideanSpace.single (0 : Fin 1) (2 * (t : ℝ) - 1)‖ ≤ 1
    rw [PiLp.norm_single, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [t.2.1, t.2.2]⟩

private theorem edgeDiskPoint_boundary (b : Bool) :
    (edgeDiskPoint (if b then 1 else 0)).val ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
  cases b <;>
    norm_num [edgeDiskPoint, Metric.mem_sphere, dist_zero_right, EuclideanSpace.single]

/-- The left and right endpoints as points of the actual zero-skeleton. -/
def graphEndpoint {X : Type u} [TopologicalSpace X] [CWStructure X]
    (e : Cell X 1) (b : Bool) : GraphVertex X :=
  ⟨characteristic X 1 e (edgeDiskPoint (if b then 1 else 0)), by
    exact CWStructure.boundary_lands 1 e
      (Set.mem_univ ⟨_, edgeDiskPoint_boundary b⟩)⟩

def graphEndpoints (X : Type u) [TopologicalSpace X] [CWStructure X] :
    EdgeEndpoints (GraphVertex X) (Cell X 1) :=
  ⟨fun e => graphEndpoint e false, fun e => graphEndpoint e true⟩

/-- One fixed orientation per geometric edge, from the negative to the positive
endpoint of its characteristic disk. -/
def graphEdgePath {X : Type u} [TopologicalSpace X] [CWStructure X]
    (e : Cell X 1) :
    Path ((graphEndpoints X).source e).val ((graphEndpoints X).target e).val where
  toFun t := characteristic X 1 e (edgeDiskPoint t)
  continuous_toFun := (characteristic X 1 e).continuous.comp (by
    apply Continuous.subtype_mk
    change Continuous (fun t : unitInterval => EuclideanSpace.single (0 : Fin 1)
      (2 * (t : ℝ) - 1))
    change Continuous (fun t : unitInterval => WithLp.toLp 2
      (Pi.single (M := fun _ : Fin 1 => ℝ) (0 : Fin 1) (2 * (t : ℝ) - 1)))
    apply (PiLp.continuous_toLp _ _).comp
    apply continuous_pi
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simpa using (show Continuous (fun t : unitInterval => 2 * (t : ℝ) - 1) by fun_prop))
  source' := rfl
  target' := rfl

/-- The spanning subgraph with every vertex and the selected open edges. -/
def graphTreeCarrier {X : Type u} [TopologicalSpace X] [CWStructure X]
    (T : Set (Cell X 1)) : Set X :=
  skeletonLT X 1 ∪ ⋃ e ∈ T, openCell X 1 e

/-- A point and a topological disjoint union of oriented intervals. The extra
point includes the bouquet on the empty generator type. -/
abbrev BouquetPresentation (E : Type u) := Unit ⊕ (Σ _ : E, unitInterval)

/-- The points identified to the vertex of a weak bouquet. -/
def bouquetVertexLocus {E : Type u} : BouquetPresentation E → Prop
  | .inl _ => True
  | .inr ⟨_, t⟩ => t = 0 ∨ t = 1

/-- Identify all interval endpoints and the distinguished point, and make no
other identifications. -/
def bouquetSetoid (E : Type u) : Setoid (BouquetPresentation E) where
  r a b := a = b ∨ (bouquetVertexLocus a ∧ bouquetVertexLocus b)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    trans := by
      intro a b c h k
      rcases h with rfl | ⟨ha, hb⟩
      · exact k
      rcases k with rfl | ⟨_, hc⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hc⟩ }

/-- The weak bouquet, with the quotient of the disjoint-union topology.
This includes infinite bouquets and does not give them a metric topology. -/
abbrev WeakBouquet (E : Type u) := Quotient (bouquetSetoid E)

def bouquetVertex (E : Type u) : WeakBouquet E := Quotient.mk _ (.inl ())

/-- One whole oriented edge loop in the quotient bouquet. -/
def bouquetLoop {E : Type u} (e : E) : Path (bouquetVertex E) (bouquetVertex E) where
  toFun t := Quotient.mk _ (.inr ⟨e, t⟩)
  continuous_toFun := continuous_quotient_mk'.comp
    (continuous_inr.comp continuous_sigmaMk)
  source' := Quotient.sound (Or.inr ⟨Or.inl rfl, trivial⟩)
  target' := Quotient.sound (Or.inr ⟨Or.inr rfl, trivial⟩)

end P202.Cellular

namespace P202Specs.Topology.GraphFundamentalGroup
open P202.Cellular P202Specs.Topology

/-- The geometric tree lemma used in the graph-group proof. It concerns the
actual subspace topology, including trees with infinitely many edges. -/
def treeContractibility : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X]
    (T : Set (Cell X 1)), (graphEndpoints X).IsSpanningTree T →
      ContractibleSpace ↥(graphTreeCarrier T)

/-- The finite-bouquet calculation, including the empty generator type and
large-universe finite types. The implementation proves the arbitrary-generator
statement from this finite one using actual continuous retractions and compact
support in the quotient topology. -/
def finiteBouquetFreeGroup : Prop :=
  ∀ (E : Type u) [Finite E],
    ∃ Φ : FreeGroup E ≃* Pi1 (WeakBouquet E) (bouquetVertex E),
      ∀ e : E, Φ (FreeGroup.of e) = loopClass (bouquetLoop e)

/-- The edge basis for the weak bouquet on an arbitrary generator type. -/
def bouquetFreeGroup : Prop :=
  ∀ E : Type u, ∃ Φ : FreeGroup E ≃* Pi1 (WeakBouquet E) (bouquetVertex E),
    ∀ e : E, Φ (FreeGroup.of e) = loopClass (bouquetLoop e)

/-- Full graph group assertion. The tree and complementary generator type may
both be infinite. The isomorphism records the actual oriented edge generators,
joined to a root by paths in the tree and transported to any basepoint.
The maximality predicate ranges over all subsets of the original edge labels.
-/
def graphFundamentalGroup : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X],
    IsGraph X → ConnectedSpace X → ∀ x : X,
    ∃ T : Set (Cell X 1),
      (graphEndpoints X).IsSpanningTree T ∧
      Maximal (graphEndpoints X).IsForest T ∧
      ∃ (r : GraphVertex X) (d : Path x r.val)
        (p : ∀ v : GraphVertex X, Path r.val v.val),
        (∀ v t, p v t ∈ graphTreeCarrier T) ∧
        ∃ Φ : FreeGroup {e : Cell X 1 // e ∉ T} ≃* Pi1 X x,
          ∀ e : {e : Cell X 1 // e ∉ T},
            Φ (FreeGroup.of e) = loopClass
              (((d.trans (p ((graphEndpoints X).source e.val))).trans
                (graphEdgePath e.val)).trans
                ((p ((graphEndpoints X).target e.val)).symm.trans d.symm))

end P202Specs.Topology.GraphFundamentalGroup
