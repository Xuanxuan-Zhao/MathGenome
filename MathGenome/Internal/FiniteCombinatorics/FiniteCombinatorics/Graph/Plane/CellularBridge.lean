import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.CellularBridge
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.Incidence
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Plane.RealizationGeometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.CellularDegrees
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.CellularComparison
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

universe u
noncomputable section

namespace FiniteCombinatorics.Graph.Plane.CellularBridge
open FiniteCombinatorics.Graph.Trees
open Specs.FiniteCombinatorics.Graph.Plane.CellularBridge

theorem transpose_apply : transpose_applyType := by
  intro V _ G o f e
  classical
  have hne := (orientation_endpoints G o e).2.1
  simp only [transposeIncidenceMap, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply,
    Specs.FiniteCombinatorics.Graph.Trees.Incidence.incidenceValue]
  simp only [ite_mul, one_mul, neg_one_mul, zero_mul]
  have hterm (x : V) :
      (if x = o.head e then f x else if x = o.tail e then -f x else 0) =
      (if x = o.head e then f x else 0) - (if x = o.tail e then f x else 0) := by
    by_cases hh : x = o.head e <;> by_cases ht : x = o.tail e <;> simp_all
  simp_rw [hterm]
  simp [Finset.sum_sub_distrib]

private theorem walk_constant {V : Type u} {G : SimpleGraph V} {f : V → ℚ}
    (h : ∀ a b, G.Adj a b → f a = f b) {a b : V} (p : G.Walk a b) : f a = f b := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih => exact (h a b hab).trans ih

theorem transpose_kernel : transpose_kernelType := by
  intro V _ G o f
  classical
  constructor
  · intro hf a b hab
    have hedge (e : G.edgeSet) : f (o.head e) = f (o.tail e) := by
      have he := congrFun hf e
      rw [transpose_apply] at he
      exact sub_eq_zero.mp he
    have hadj (a b : V) (hab : G.Adj a b) : f a = f b := by
      let e : G.edgeSet := ⟨s(a,b), hab⟩
      have he : s(o.tail e, o.head e) = s(a,b) := o.edge_eq e
      rcases Sym2.eq_iff.mp he with h | h
      · exact (h.1 ▸ h.2 ▸ hedge e).symm
      · exact h.1 ▸ h.2 ▸ hedge e
    obtain ⟨p⟩ := hab
    exact walk_constant hadj p
  · intro hf
    apply funext
    intro e
    rw [transpose_apply]
    exact sub_eq_zero.mpr (hf _ _ (orientation_endpoints G o e).1.reachable.symm)

theorem transpose_kernel_equiv : transpose_kernel_equivType := by
  intro V _ G o
  classical
  let forward : (G.ConnectedComponent → ℚ) →ₗ[ℚ]
      LinearMap.ker (transposeIncidenceMap G o) :=
    { toFun := fun f => ⟨fun v => f (G.connectedComponentMk v),
        (transpose_kernel G o _).mpr (fun a b hab => congrArg f
          (SimpleGraph.ConnectedComponent.sound hab))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofBijective forward ⟨?_, ?_⟩, ?_⟩
  · intro f g h
    ext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact congrFun (congrArg Subtype.val h) v
  · intro f
    let lift : G.ConnectedComponent → ℚ := SimpleGraph.ConnectedComponent.lift f.val
      (fun a b p _ => (transpose_kernel G o f.val).mp f.property a b ⟨p⟩)
    exact ⟨lift, rfl⟩
  · intro f v
    rfl

theorem transpose_kernel_finrank : transpose_kernel_finrankType := by
  intro V _ G o
  classical
  let := Fintype.ofFinite G.ConnectedComponent
  obtain ⟨E, _⟩ := transpose_kernel_equiv G o
  rw [← E.finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

theorem incidence_rank : incidence_rankType := by
  intro V _ G _ o
  have h := (transposeIncidenceMap G o).finrank_range_add_finrank_ker
  rw [transpose_kernel_finrank, Module.finrank_pi, ← Nat.card_eq_fintype_card] at h
  have hr : Module.finrank ℚ (LinearMap.range (transposeIncidenceMap G o)) =
      Module.finrank ℚ (LinearMap.range (incidenceMap G o)) := by
    exact Matrix.rank_transpose _
  rw [hr] at h
  omega

theorem incidence_nullity : incidence_nullityType := by
  intro V _ G _ o
  have h := (incidenceMap G o).finrank_range_add_finrank_ker
  have ht := (transposeIncidenceMap G o).finrank_range_add_finrank_ker
  rw [transpose_kernel_finrank, Module.finrank_pi, ← Nat.card_eq_fintype_card] at ht
  have hr : Module.finrank ℚ (LinearMap.range (transposeIncidenceMap G o)) =
      Module.finrank ℚ (LinearMap.range (incidenceMap G o)) := Matrix.rank_transpose _
  rw [hr] at ht
  rw [Module.finrank_pi, ← Nat.card_eq_fintype_card] at h
  omega

theorem incidence_kernel_dual_finrank : incidence_kernel_dual_finrankType := by
  intro V _ G _ o
  rw [Subspace.dual_finrank_eq, incidence_nullity]

open P202Specs.UniversalCoefficientsCohomology

/-- Over a field, functionals on cycles extend to the whole chain group.
Functionals vanishing on cycles are exactly coboundaries. -/
theorem rational_quotient_evaluation : rational_quotient_evaluationType := by
  intro C n
  classical
  let D := dualChain ℚ ℚ C
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    obtain ⟨a, rfl⟩ := (Algebraic.cycleBoundaries D n).mkQ_surjective a
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    have hann : a.val ∈ (Algebraic.cycles C n).dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro z hz
      have h := congrArg (fun f => f (Algebraic.homologyClass C n ⟨z, hz⟩)) ha
      exact h
    change a.val ∈ (LinearMap.ker (C.d n ((ComplexShape.down ℤ).next n)).hom).dualAnnihilator at hann
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
    obtain ⟨b, hb⟩ := hann
    exact ⟨b, hb⟩
  · intro f
    obtain ⟨g, hg⟩ := (f.comp (Algebraic.homologyClass C n)).exists_extend
    have hgc : g ∈ Algebraic.cycles D n := by
      apply LinearMap.ext
      intro b
      change g ((C.d ((ComplexShape.down ℤ).prev n) n).hom b) = 0
      let z : Algebraic.cycles C n :=
        ⟨_, P103.Specs.Ch10.Complexes.boundaryInclusion C n ⟨b, rfl⟩⟩
      have hz : z ∈ Algebraic.cycleBoundaries C n := ⟨b, rfl⟩
      have h := LinearMap.congr_fun hg z
      change g z.val = f (Algebraic.homologyClass C n z) at h
      rw [show Algebraic.homologyClass C n z = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero] at h
      exact h
    refine ⟨Algebraic.homologyClass D n ⟨g, hgc⟩, ?_⟩
    apply (Algebraic.cycleBoundaries C n).quot_hom_ext
    intro z
    exact LinearMap.congr_fun hg z

theorem rational_evaluation : rational_evaluationType := by
  intro C n
  have hq := rational_quotient_evaluation C n
  have hdom := (quotientHomologyEquiv ℚ (dualChain ℚ ℚ C) n).bijective
  let E : (Algebraic.Homology C n →ₗ[ℚ] ℚ) ≃ₗ[ℚ] (C.homology n →ₗ[ℚ] ℚ) :=
    LinearEquiv.arrowCongr (quotientHomologyEquiv ℚ C n).symm (LinearEquiv.refl ℚ ℚ)
  exact E.bijective.comp (hq.comp hdom)

theorem realization_universal_coefficients : realization_universal_coefficientsType := by
  intro V _ G D
  exact ⟨LinearEquiv.ofBijective _ (rational_evaluation _ 1), fun _ => rfl⟩

end FiniteCombinatorics.Graph.Plane.CellularBridge


namespace FiniteCombinatorics.Graph.Plane.CellularBridge
open P202.Cellular Topology Set
open P202Specs.CellularDegrees
open Specs.FiniteCombinatorics.Graph.Plane.Foundations
open Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry

/-- The oriented disk coordinate, from the chosen genuine interval chart. -/
def diskInterval (h : IntervalParametrization) : Disk 1 ≃ₜ unitInterval :=
  h.homeomorph.symm.trans Convexity.StdSimplex.homeomorphI

lemma diskInterval_boundary (h : IntervalParametrization) (x : Disk 1) :
    ‖x.val‖ = 1 ↔ diskInterval h x = 0 ∨ diskInterval h x = 1 := by
  let s := h.homeomorph.symm x
  have hs : s.weights 0 + s.weights 1 = 1 := by
    have ht := s.total
    rw [Finsupp.sum_fintype _ _ (by simp)] at ht
    simpa only [Nat.reduceAdd, Fin.sum_univ_two] using ht
  have hb := h.boundary s
  rw [Homeomorph.apply_symm_apply] at hb
  rw [← hb]
  have ht : (diskInterval h x).val = s.weights 1 :=
    Convexity.StdSimplex.homeomorphI_apply_coe s
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · right; apply Subtype.ext; change (diskInterval h x).val = 1
      rw [ht]; change s.weights 0 = 0 at hi; linarith
    · left; apply Subtype.ext; exact ht.trans hi
  · rintro (h0 | h1)
    · exact ⟨1, by simpa [h0] using ht.symm⟩
    · exact ⟨0, by have hh := congrArg Subtype.val h1; rw [ht] at hh; change s.weights 1 = 1 at hh; linarith⟩

lemma diskInterval_interior (h : IntervalParametrization) (x : Disk 1) :
    ‖x.val‖ < 1 ↔ diskInterval h x ≠ 0 ∧ diskInterval h x ≠ 1 := by
  have hx : ‖x.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  rw [← not_or, ← diskInterval_boundary]
  exact ⟨ne_of_lt, fun hn => lt_of_le_of_ne hx hn⟩

section EmbeddedCharts
variable {V : Type u} [Finite V] {G : SimpleGraph V}
variable (D : Drawing G) (o : FiniteCombinatorics.Graph.Trees.EdgeOrientation G)

private lemma oriented_arc (e : G.edgeSet) :
    IsSimplePolygonalArc (D.point (o.tail e)) (D.point (o.head e)) (D.edge e) := by
  have ha := (FiniteCombinatorics.Graph.Trees.orientation_endpoints G o e).1
  have he : (⟨s(o.tail e, o.head e), ha⟩ : G.edgeSet) = e := Subtype.ext (o.edge_eq e)
  simpa only [he] using D.edge_arc _ _ ha

/-- The given arc with its orientation, with no restriction on traversal speed. -/
def orientedPath (e : G.edgeSet) : _root_.Path (D.point (o.tail e)) (D.point (o.head e)) :=
  Classical.choose (oriented_arc D o e).2

lemma orientedPath_injective (e : G.edgeSet) : Function.Injective (orientedPath D o e) :=
  (Classical.choose_spec (oriented_arc D o e).2).1

lemma orientedPath_range (e : G.edgeSet) : range (orientedPath D o e) = D.edge e :=
  (Classical.choose_spec (oriented_arc D o e).2).2

/-- An edge parametrized in the actual sphere subspace. -/
def realizationEdge (e : G.edgeSet) : C(unitInterval, Realization D) where
  toFun t := ⟨OnePoint.some (orientedPath D o e t), _,
    Or.inr (mem_iUnion.mpr ⟨e, orientedPath_range D o e ▸ mem_range_self t⟩), rfl⟩
  continuous_toFun := (OnePoint.continuous_coe.comp (orientedPath D o e).continuous).subtype_mk _

lemma realizationEdge_injective (e : G.edgeSet) : Function.Injective (realizationEdge D o e) := by
  intro s t he
  exact orientedPath_injective D o e (OnePoint.coe_injective (congrArg Subtype.val he))

@[simp] lemma realizationEdge_zero (e : G.edgeSet) :
    realizationEdge D o e 0 = realizationVertex D (o.tail e) := by
  apply Subtype.ext
  exact congrArg OnePoint.some (orientedPath D o e).source

@[simp] lemma realizationEdge_one (e : G.edgeSet) :
    realizationEdge D o e 1 = realizationVertex D (o.head e) := by
  apply Subtype.ext
  exact congrArg OnePoint.some (orientedPath D o e).target

lemma realizationVertex_injective : Function.Injective (realizationVertex D) := by
  intro a b he
  exact D.point_injective (OnePoint.coe_injective (congrArg Subtype.val he))

/-- No vertex occurs in an open edge, including isolated vertices elsewhere. -/
lemma realizationEdge_eq_vertex (e : G.edgeSet) (t : unitInterval) (v : V)
    (he : realizationEdge D o e t = realizationVertex D v) : t = 0 ∨ t = 1 := by
  have hp : orientedPath D o e t = D.point v :=
    OnePoint.coe_injective (congrArg Subtype.val he)
  have hv : v ∈ e.val := (D.vertex_edge e v).mp
    (hp ▸ (orientedPath_range D o e ▸ mem_range_self t))
  rcases (FiniteCombinatorics.Graph.Trees.orientation_endpoints G o e).2.2 v |>.mp hv with hv | hv
  · right
    apply realizationEdge_injective D o e
    rw [realizationEdge_one, he, hv]
  · left
    apply realizationEdge_injective D o e
    rw [realizationEdge_zero, he, hv]


lemma realizationEdge_intersection (e f : G.edgeSet) (s t : unitInterval)
    (hef : e ≠ f) (heq : realizationEdge D o e s = realizationEdge D o f t) :
    s = 0 ∨ s = 1 := by
  have hp : orientedPath D o e s = orientedPath D o f t :=
    OnePoint.coe_injective (congrArg Subtype.val heq)
  have hx : orientedPath D o e s ∈ D.edge e ∩ D.edge f :=
    ⟨orientedPath_range D o e ▸ mem_range_self s,
      hp ▸ (orientedPath_range D o f ▸ mem_range_self t)⟩
  rw [D.edge_intersection e f hef] at hx
  obtain ⟨v, _, hv⟩ := hx
  exact realizationEdge_eq_vertex D o e s v (Subtype.ext (congrArg OnePoint.some hv.symm))

end EmbeddedCharts

/-- The finite cell family has no cells in dimension at least two. -/
def GraphCell (v e : ℕ) : ℕ → Type
  | 0 => Fin v
  | 1 => Fin e
  | _ + 2 => PEmpty

def graphCellEquiv (v e : ℕ) : (Σ n, GraphCell v e n) ≃ (Fin v ⊕ Fin e) where
  toFun c := match c with
    | ⟨0, a⟩ => Sum.inl a
    | ⟨1, b⟩ => Sum.inr b
    | ⟨_+2, c⟩ => c.elim
  invFun := Sum.elim (fun a => ⟨0,a⟩) (fun b => ⟨1,b⟩)
  left_inv c := by rcases c with ⟨_ | _ | n, c⟩ <;> first | rfl | exact c.elim
  right_inv c := by cases c <;> rfl

instance (v e : ℕ) : Finite (Σ n, GraphCell v e n) :=
  Finite.of_equiv (Fin v ⊕ Fin e) (graphCellEquiv v e).symm

/-- Finitely many compact characteristic disks give the actual weak topology. -/
lemma finite_cells_weak_topology {X : Type*} [TopologicalSpace X] [T2Space X]
    [CellStructure X] [Finite (Σ n, Cell X n)]
    (hc : ⋃ (n : ℕ) (c : Cell X n), openCell X n c = univ) (A : Set X) :
    IsClosed A ↔ ∀ n (c : Cell X n), IsClosed (characteristic X n c ⁻¹' A) := by
  constructor
  · intro h n c; exact h.preimage (characteristic X n c).continuous
  · intro h
    have heq : A = ⋃ c : Σ n, Cell X n,
        characteristic X c.1 c.2 '' (characteristic X c.1 c.2 ⁻¹' A) := by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := hc ▸ mem_univ x
        obtain ⟨n, c, t, ht⟩ := (show ∃ n c t, interiorMap X n c t = x by
          simpa only [mem_iUnion, openCell, mem_range] using hx')
        exact mem_iUnion.mpr ⟨⟨n,c⟩, interiorInclusion n t, (by change interiorMap X n c t ∈ A; rw [ht]; exact hx), ht⟩
      · intro hx
        obtain ⟨c, t, ht, rfl⟩ := (show ∃ c : Σ n, Cell X n,
          ∃ t, t ∈ characteristic X c.1 c.2 ⁻¹' A ∧ characteristic X c.1 c.2 t = x by
            simpa only [mem_iUnion, mem_image] using hx)
        exact ht
    rw [heq]
    exact isClosed_iUnion_of_finite (fun c => ((h c.1 c.2).isCompact.image
      (characteristic X c.1 c.2).continuous).isClosed)

section EmbeddedCells
variable {V : Type u} [Finite V] {G : SimpleGraph V}
variable (D : Drawing G) (o : FiniteCombinatorics.Graph.Trees.EdgeOrientation G)
variable (h : IntervalParametrization)

/-- Universe-small labels, equivalent to the original graph's vertices and edges. -/
def vertexLabel : Fin (Nat.card V) ≃ V := (Finite.equivFin V).symm
def edgeLabel : Fin (Nat.card G.edgeSet) ≃ G.edgeSet := (Finite.equivFin G.edgeSet).symm

/-- Closed edge disks are embedded by the original arcs. -/
def edgeCharacteristic (e : G.edgeSet) : C(Disk 1, Realization D) :=
  (realizationEdge D o e).comp ⟨diskInterval h, (diskInterval h).continuous⟩

lemma edgeCharacteristic_embedding (e : G.edgeSet) :
    IsEmbedding (edgeCharacteristic D o h e) := by
  exact ((edgeCharacteristic D o h e).continuous.isClosedEmbedding
    ((realizationEdge_injective D o e).comp (diskInterval h).injective)).isEmbedding

/-- Cells on the given sphere subspace, rather than on a combinatorial replacement. -/
@[instance_reducible] def embeddedCellStructure : CellStructure (Realization D) where
  Cell := GraphCell (Nat.card V) (Nat.card G.edgeSet)
  characteristic n := match n with
    | 0 => fun a => ContinuousMap.const _ (realizationVertex D (vertexLabel a))
    | 1 => fun b => edgeCharacteristic D o h (edgeLabel b)
    | _+2 => PEmpty.elim

local notation "EC" => embeddedCellStructure D o h

@[simp] lemma embedded_zero (a : Fin (Nat.card V)) (x : Disk 0) :
    letI := EC
    characteristic (Realization D) 0 a x = realizationVertex D (vertexLabel a) := rfl

@[simp] lemma embedded_one (b : Fin (Nat.card G.edgeSet)) (x : Disk 1) :
    letI := EC
    characteristic (Realization D) 1 b x = realizationEdge D o (edgeLabel b) (diskInterval h x) := rfl

lemma embedded_zero_cell (a : Fin (Nat.card V)) :
    letI := EC
    openCell (Realization D) 0 a = {realizationVertex D (vertexLabel a)} := by
  letI := EC
  ext x
  constructor
  · rintro ⟨t, rfl⟩; rfl
  · intro hx
    exact ⟨⟨0, by simp⟩, hx.symm⟩

lemma embedded_interior_embedding : letI := EC; ∀ n (c : Cell (Realization D) n),
    IsEmbedding (interiorMap (Realization D) n c) := by
  letI := EC
  rintro (_ | _ | n) c
  · exact IsEmbedding.of_subsingleton _
  · exact (edgeCharacteristic_embedding D o h (edgeLabel c)).comp
      (IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.subtypeVal)
  · exact c.elim

lemma embedded_cover : letI := EC; ⋃ (n : ℕ) (c : Cell (Realization D) n), openCell (Realization D) n c = univ := by
  letI := EC
  apply eq_univ_of_forall
  intro x
  obtain ⟨y, hy, hxy⟩ := x.property
  have heq : x.val = OnePoint.some y := hxy.symm
  by_cases hv : y ∈ range D.point
  · obtain ⟨v, hv⟩ := hv
    refine mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨(vertexLabel (V := V)).symm v, ?_⟩⟩
    rw [embedded_zero_cell D o h]
    apply Subtype.ext
    change x.val = OnePoint.some (D.point (vertexLabel ((vertexLabel (V := V)).symm v)))
    rw [Equiv.apply_symm_apply]
    exact heq.trans (congrArg OnePoint.some hv.symm)
  · obtain ⟨e, he⟩ := mem_iUnion.mp (hy.resolve_left hv)
    have he' : ∃ t, orientedPath D o e t = y := by
      rw [← orientedPath_range D o e] at he
      exact he
    obtain ⟨t, ht⟩ := he'
    have ht0 : t ≠ 0 := by
      intro ht0; apply hv; refine ⟨o.tail e, ?_⟩
      simpa only [ht0, (orientedPath D o e).source] using ht
    have ht1 : t ≠ 1 := by
      intro ht1; apply hv; refine ⟨o.head e, ?_⟩
      simpa only [ht1, (orientedPath D o e).target] using ht
    let d := (diskInterval h).symm t
    have hd : ‖d.val‖ < 1 := (diskInterval_interior h d).mpr (by simpa [d] using And.intro ht0 ht1)
    refine mem_iUnion.mpr ⟨1, mem_iUnion.mpr ⟨(edgeLabel (G := G)).symm e, ?_⟩⟩
    refine ⟨⟨d.val, by simpa only [Metric.mem_ball, dist_zero_right] using hd⟩, ?_⟩
    apply Subtype.ext
    change OnePoint.some (orientedPath D o _ _) = x.val
    change OnePoint.some (orientedPath D o (edgeLabel ((edgeLabel (G := G)).symm e))
      (diskInterval h ((diskInterval h).symm t))) = x.val
    rw [Equiv.apply_symm_apply, Homeomorph.apply_symm_apply, ht]
    exact heq.symm


lemma embedded_one_nonvertex (b : Fin (Nat.card G.edgeSet))
    (x : Realization D) (hx : letI := EC; x ∈ openCell (Realization D) 1 b) :
    x ∉ range (realizationVertex D) := by
  letI := EC
  obtain ⟨t, rfl⟩ := hx
  rintro ⟨v, hv⟩
  have ht : ‖t.val‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using t.property
  have hn := (diskInterval_interior h (interiorInclusion 1 t)).mp ht
  have he := realizationEdge_eq_vertex D o (edgeLabel b)
    (diskInterval h (interiorInclusion 1 t)) v hv.symm
  exact he.elim hn.1 hn.2

lemma embedded_one_disjoint (a b : Fin (Nat.card G.edgeSet)) (hab : a ≠ b) :
    letI := EC; Disjoint (openCell (Realization D) 1 a) (openCell (Realization D) 1 b) := by
  letI := EC
  apply disjoint_left.mpr
  rintro x ⟨s, rfl⟩ ⟨t, ht⟩
  have hs : ‖s.val‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using s.property
  have hn := (diskInterval_interior h (interiorInclusion 1 s)).mp hs
  have he := realizationEdge_intersection D o (edgeLabel a) (edgeLabel b)
    (diskInterval h (interiorInclusion 1 s)) (diskInterval h (interiorInclusion 1 t))
    (fun he => hab ((edgeLabel (G := G)).injective he)) ht.symm
  exact he.elim hn.1 hn.2

lemma embedded_disjoint : letI := EC;
    (univ : Set (Σ n, Cell (Realization D) n)).PairwiseDisjoint
      (fun c => openCell (Realization D) c.1 c.2) := by
  letI := EC
  rintro ⟨(_ | _ | n), a⟩ _ ⟨(_ | _ | m), b⟩ _ hne
  all_goals dsimp only [Function.onFun]
  · rw [embedded_zero_cell D o h a, embedded_zero_cell D o h b]
    apply disjoint_singleton.mpr
    intro he
    apply hne
    have hab := (vertexLabel (V := V)).injective (realizationVertex_injective D he)
    exact congrArg (Sigma.mk 0) hab
  · apply disjoint_left.mpr
    intro x hx hy
    rw [embedded_zero_cell D o h a] at hx
    exact embedded_one_nonvertex D o h b x hy (hx ▸ mem_range_self _)
  · exact b.elim
  · apply Disjoint.symm
    apply disjoint_left.mpr
    intro x hx hy
    rw [embedded_zero_cell D o h b] at hx
    exact embedded_one_nonvertex D o h a x hy (hx ▸ mem_range_self _)
  · exact embedded_one_disjoint D o h a b (fun he => hne (congrArg (Sigma.mk 1) he))
  · exact b.elim
  · exact a.elim
  · exact a.elim
  · exact a.elim

lemma embedded_boundary_lands : letI := EC;
    ∀ n (c : Cell (Realization D) n),
      MapsTo (boundaryMap (Realization D) n c) univ (skeletonLT (Realization D) n) := by
  letI := EC
  rintro (_ | _ | n) c x _
  · have hx : ‖x.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have hz : x.val = 0 := Subsingleton.elim _ _
    simp [hz] at hx
  · have hx : ‖x.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have ht := (diskInterval_boundary h (boundaryInclusion 1 x)).mp hx
    rcases ht with ht | ht
    · refine mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨by omega,
        mem_iUnion.mpr ⟨(vertexLabel (V := V)).symm (o.tail (edgeLabel c)), ?_⟩⟩⟩
      rw [embedded_zero_cell D o h]
      change realizationEdge D o (edgeLabel c) (diskInterval h (boundaryInclusion 1 x)) = _
      rw [ht, realizationEdge_zero, Equiv.apply_symm_apply]
    · refine mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨by omega,
        mem_iUnion.mpr ⟨(vertexLabel (V := V)).symm (o.head (edgeLabel c)), ?_⟩⟩⟩
      rw [embedded_zero_cell D o h]
      change realizationEdge D o (edgeLabel c) (diskInterval h (boundaryInclusion 1 x)) = _
      rw [ht, realizationEdge_one, Equiv.apply_symm_apply]
  · exact c.elim

lemma embedded_closure_finite : letI := EC;
    ∀ n (c : Cell (Realization D) n), ∃ F : Finset (Σ m, Cell (Realization D) m),
      closedCell (Realization D) n c ⊆ ⋃ d ∈ F, openCell (Realization D) d.1 d.2 := by
  letI := EC
  classical
  letI : Finite (Σ n, Cell (Realization D) n) :=
    (inferInstance : Finite (Σ n, GraphCell (Nat.card V) (Nat.card G.edgeSet) n))
  letI : Fintype (Σ n, Cell (Realization D) n) := Fintype.ofFinite _
  intro n c
  refine ⟨Finset.univ, ?_⟩
  intro x _
  have hx : x ∈ ⋃ (m : ℕ) (d : Cell (Realization D) m), openCell (Realization D) m d :=
    embedded_cover D o h ▸ mem_univ x
  obtain ⟨m, d, hd⟩ := (show ∃ m d, x ∈ openCell (Realization D) m d by
    simpa only [mem_iUnion] using hx)
  exact mem_iUnion.mpr ⟨⟨m,d⟩, mem_iUnion.mpr ⟨Finset.mem_univ _, hd⟩⟩

/-- The actual finite embedded graph is a one-dimensional CW space. All diskwise
and attachment topology axioms are proved on its original subspace topology. -/
@[instance_reducible] def embeddedCWStructure : CWStructure (Realization D) := by
  letI := EC
  letI : Finite (Σ n, Cell (Realization D) n) :=
    (inferInstance : Finite (Σ n, GraphCell (Nat.card V) (Nat.card G.edgeSet) n))
  exact P202.Topology.cwStructureOfWeak
    (embedded_interior_embedding D o h) (embedded_disjoint D o h)
    (embedded_cover D o h) (embedded_boundary_lands D o h)
    (embedded_closure_finite D o h)
    (finite_cells_weak_topology (embedded_cover D o h))


lemma diskInterval_endpoint_zero (h : IntervalParametrization) :
    diskInterval h (h.endpoint.{0} 0).val.down = 1 := by
  change Convexity.StdSimplex.homeomorphI
    (h.homeomorph.symm (h.homeomorph
      (P202Specs.SingularChains.faceInclusion 0 (Convexity.StdSimplex.single 0)))) = 1
  rw [Homeomorph.symm_apply_apply]
  apply Subtype.ext
  rw [Convexity.StdSimplex.homeomorphI_apply_coe]
  rw [P202.SingularChains.faceInclusion_vertex]
  norm_num [Convexity.StdSimplex.single]

lemma diskInterval_endpoint_one (h : IntervalParametrization) :
    diskInterval h (h.endpoint.{0} 1).val.down = 0 := by
  change Convexity.StdSimplex.homeomorphI
    (h.homeomorph.symm (h.homeomorph
      (P202Specs.SingularChains.faceInclusion 1 (Convexity.StdSimplex.single 0)))) = 0
  rw [Homeomorph.symm_apply_apply]
  apply Subtype.ext
  rw [Convexity.StdSimplex.homeomorphI_apply_coe]
  rw [P202.SingularChains.faceInclusion_vertex]
  norm_num [Convexity.StdSimplex.single]

lemma edgeCharacteristic_image (e : G.edgeSet) :
    Subtype.val '' range (edgeCharacteristic D o h e) = OnePoint.some '' D.edge e := by
  ext z
  constructor
  · rintro ⟨x, ⟨d, rfl⟩, rfl⟩
    exact ⟨_, orientedPath_range D o e ▸ mem_range_self _, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [← orientedPath_range D o e] at hy
    obtain ⟨t, rfl⟩ := hy
    refine ⟨edgeCharacteristic D o h e ((diskInterval h).symm t), mem_range_self _, ?_⟩
    change OnePoint.some (orientedPath D o e (diskInterval h ((diskInterval h).symm t))) = _
    rw [Homeomorph.apply_symm_apply]

end EmbeddedCells

/-- The CW axioms, geometric cell images and signed endpoints are simultaneous,
including the graph with no vertices and graphs with isolated vertices. -/
theorem embedded_cw : Specs.FiniteCombinatorics.Graph.Plane.CellularBridge.embedded_cwType := by
  intro V _ G D o
  obtain ⟨h⟩ := P202.Homology.CellularDegrees.intervalParametrization_nonempty
  refine ⟨embeddedCWStructure D o h, h, vertexLabel, edgeLabel, ?_, ?_, ?_, ?_, ?_⟩
  · exact (inferInstance : Finite (Σ n, GraphCell (Nat.card V) (Nat.card G.edgeSet) n))
  · intro n; exact PEmpty.instIsEmpty
  · intro c x; rfl
  · intro c; exact edgeCharacteristic_image D o h (edgeLabel c)
  · intro c
    change realizationEdge D o (edgeLabel c) (diskInterval h (h.endpoint 0).val.down) = _ ∧
      realizationEdge D o (edgeLabel c) (diskInterval h (h.endpoint 1).val.down) = _
    rw [diskInterval_endpoint_zero, diskInterval_endpoint_one, realizationEdge_one, realizationEdge_zero]
    exact ⟨rfl,rfl⟩


set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open P202Specs.CellularChains
open Specs.FiniteCombinatorics.Graph.Plane.CellularBridge

open Classical in
lemma incidence_single {V : Type u} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (o : FiniteCombinatorics.Graph.Trees.EdgeOrientation G) (e : G.edgeSet) (m : ℚ) :
    incidenceMap G o (Pi.single e m) = Pi.single (o.head e) m - Pi.single (o.tail e) m := by
  classical
  have hne := (FiniteCombinatorics.Graph.Trees.orientation_endpoints G o e).2.1
  ext v
  simp only [incidenceMap, Matrix.mulVecLin_apply, Matrix.mulVec_single,
    op_smul_eq_smul, Pi.smul_apply, Matrix.col_apply,
    Specs.FiniteCombinatorics.Graph.Trees.Incidence.incidenceValue,
    Pi.sub_apply, smul_eq_mul, Pi.single_apply]
  by_cases hh : v = o.head e <;> by_cases ht : v = o.tail e <;> simp_all

/-- Coordinates for the actual skeletal relative groups, with the chosen
orientation on every original edge. -/
theorem embedded_coordinates {V : Type u} [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (D : Drawing G)
    (o : FiniteCombinatorics.Graph.Trees.EdgeOrientation G) (h : IntervalParametrization) :
    letI := embeddedCWStructure D o h
    ∃ (E0 : chainGroup (Realization D) ℚ ℚ 0 ≃ₗ[ℚ] (V → ℚ))
      (E1 : chainGroup (Realization D) ℚ ℚ 1 ≃ₗ[ℚ] (G.edgeSet → ℚ)),
      CharacteristicCoordinates (Realization D) G o h vertexLabel edgeLabel E0 E1 := by
  letI := embeddedCWStructure D o h
  classical
  let X := Realization D
  obtain ⟨g, e, hz, he, hg, hc⟩ := P202.Homology.CellularDegrees.intervalCellBoundary X ℚ ℚ h
  obtain ⟨f, hf⟩ := P202.Homology.cellularOrientedCoordinates X ℚ ℚ 1 g
  let R0 : (Cell X 0 →₀ ℚ) ≃ₗ[ℚ] (V → ℚ) :=
    (Finsupp.domLCongr (vertexLabel (V := V))).trans (Finsupp.linearEquivFunOnFinite ℚ ℚ V)
  let R1 : (Cell X 1 →₀ ℚ) ≃ₗ[ℚ] (G.edgeSet → ℚ) :=
    (Finsupp.domLCongr (edgeLabel (G := G))).trans (Finsupp.linearEquivFunOnFinite ℚ ℚ G.edgeSet)
  have R0_single (c : Cell X 0) (m : ℚ) : R0 (Finsupp.single c m) = Pi.single (vertexLabel c) m := by
    exact (congrArg (Finsupp.linearEquivFunOnFinite ℚ ℚ V)
      (Finsupp.domLCongr_single (R := ℚ) (vertexLabel (V := V)) c m)).trans
      (Finsupp.linearEquivFunOnFinite_single ℚ ℚ V (vertexLabel c) m)
  have R1_single (c : Cell X 1) (m : ℚ) : R1 (Finsupp.single c m) = Pi.single (edgeLabel c) m := by
    exact (congrArg (Finsupp.linearEquivFunOnFinite ℚ ℚ G.edgeSet)
      (Finsupp.domLCongr_single (R := ℚ) (edgeLabel (G := G)) c m)).trans
      (Finsupp.linearEquivFunOnFinite_single ℚ ℚ G.edgeSet (edgeLabel c) m)
  let E0 := e.trans R0
  let E1 := f.trans R1
  have hcol (c : Cell X 1) (m : ℚ) :
      E0 (differential X ℚ ℚ 0 (f.symm (Finsupp.single c m))) =
        incidenceMap G o (R1 (Finsupp.single c m)) := by
    obtain ⟨a, b, ha, hb, hd⟩ := hc c
    have hap := congrArg Subtype.val ha
    have hbp := congrArg Subtype.val hb
    change realizationEdge D o (edgeLabel c) (diskInterval h (h.endpoint 0).val.down) =
      realizationVertex D (vertexLabel a) at hap
    change realizationEdge D o (edgeLabel c) (diskInterval h (h.endpoint 1).val.down) =
      realizationVertex D (vertexLabel b) at hbp
    rw [diskInterval_endpoint_zero, realizationEdge_one] at hap
    rw [diskInterval_endpoint_one, realizationEdge_zero] at hbp
    have hla := realizationVertex_injective D hap.symm
    have hlb := realizationVertex_injective D hbp.symm
    have hfc : f.symm (Finsupp.single c m) = cellClass X ℚ ℚ 1 c (g m) :=
      f.symm_apply_eq.mpr (hf c m).symm
    rw [hfc]
    change R0 (e (differential X ℚ ℚ 0 (cellClass X ℚ ℚ 1 c (g m)))) = _
    rw [hd m]
    rw [map_sub, R0_single, R0_single, R1_single, hla, hlb, incidence_single]
  let L := E0.toLinearMap.comp ((differential X ℚ ℚ 0).hom.comp f.symm.toLinearMap)
  let R := (incidenceMap G o).comp R1.toLinearMap
  have hLR : L = R := Finsupp.lhom_ext hcol
  refine ⟨E0, E1, ?_, ?_, g, hz, hg, ?_⟩
  · intro z
    have hz := LinearMap.congr_fun hLR (f z)
    simpa only [L, R, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, E1, LinearEquiv.trans_apply] using hz
  · intro c m
    exact (congrArg R0 (he c m)).trans (R0_single c m)
  · intro c m
    exact (congrArg R1 (hf c m)).trans (R1_single c m)

/-- In these characteristic coordinates, the actual connecting-map
cellular differential is the signed graph incidence map. -/
theorem embedded_differential {V : Type u} [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (D : Drawing G)
    (o : FiniteCombinatorics.Graph.Trees.EdgeOrientation G) (h : IntervalParametrization) :
    letI := embeddedCWStructure D o h
    ∃ (E0 : chainGroup (Realization D) ℚ ℚ 0 ≃ₗ[ℚ] (V → ℚ))
      (E1 : chainGroup (Realization D) ℚ ℚ 1 ≃ₗ[ℚ] (G.edgeSet → ℚ)),
      ∀ z, E0 (differential (Realization D) ℚ ℚ 0 z) = incidenceMap G o (E1 z) := by
  letI := embeddedCWStructure D o h
  obtain ⟨E0, E1, hE⟩ := embedded_coordinates D o h
  exact ⟨E0, E1, hE.1⟩

lemma embedded_chain_two_zero {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Drawing G) (o : FiniteCombinatorics.Graph.Trees.EdgeOrientation G)
    (h : IntervalParametrization) : letI := embeddedCWStructure D o h
      Subsingleton (chainGroup (Realization D) ℚ ℚ 2) := by
  letI := embeddedCWStructure D o h
  letI : IsEmpty (Cell (Realization D) 2) := PEmpty.instIsEmpty
  obtain ⟨E⟩ := P202.Homology.cellularCellGroups (Realization D) ℚ ℚ 2
  exact E.injective.subsingleton

open CategoryTheory HomologicalComplex

/-- If there is no incoming differential, homology is the kernel of the
outgoing differential, with the actual categorical homology objects. -/
def homologyOneKernelEquiv (C : ChainComplex (ModuleCat.{v} ℚ) ℕ)
    (hd : C.d 2 1 = 0) : C.homology 1 ≃ₗ[ℚ] LinearMap.ker (C.d 1 0).hom := by
  let S := C.sc' 2 1 0
  have hf : S.f = 0 := hd
  exact ((C.homologyIsoSc' 2 1 0 (by simp) (by simp)) ≪≫
    (S.asIsoHomologyπ hf).symm ≪≫ S.moduleCatCyclesIso).toLinearEquiv

/-- Transport a kernel through commuting linear coordinates. -/
def kernelCoordinates {A : Type u} {B : Type v} {A' : Type w} {B' : Type*}
    [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    [AddCommGroup A'] [Module ℚ A'] [AddCommGroup B'] [Module ℚ B']
    (d : A →ₗ[ℚ] B) (d' : A' →ₗ[ℚ] B')
    (E : A ≃ₗ[ℚ] A') (F : B ≃ₗ[ℚ] B') (h : ∀ x, F (d x) = d' (E x)) :
    LinearMap.ker d ≃ₗ[ℚ] LinearMap.ker d' where
  toFun x := ⟨E x, by rw [LinearMap.mem_ker, ← h, x.property, map_zero]⟩
  invFun x := ⟨E.symm x, by
    apply F.injective
    rw [map_zero, h, E.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext (E.symm_apply_apply x)
  right_inv x := Subtype.ext (E.apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add E (x : A) (y : A))
  map_smul' r x := Subtype.ext (map_smul E r (x : A))

/-- Ordinary singular H₁ of the original drawing realization, identified with
its oriented incidence kernel using the genuine cellular comparison theorem. -/
theorem realization_homology_of_interval {V : Type u} [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (D : Drawing G)
    (o : FiniteCombinatorics.Graph.Trees.EdgeOrientation G) (h : IntervalParametrization) :
    Nonempty (P202Specs.SingularChains.homology ℚ ℚ (TopCat.of (Realization D)) 1 ≃ₗ[ℚ]
      LinearMap.ker (incidenceMap G o)) := by
  letI := embeddedCWStructure D o h
  let X := Realization D
  let C := cellularComplex X ℚ ℚ
  letI : Subsingleton (C.X 2) := by
    change Subsingleton (chainGroup X ℚ ℚ 2)
    exact embedded_chain_two_zero D o h
  have hd : C.d 2 1 = 0 := by
    ext x
    exact (congrArg (C.d 2 1) (Subsingleton.elim x 0)).trans (map_zero _)
  obtain ⟨E0, E1, hE⟩ := embedded_differential D o h
  let K : LinearMap.ker (C.d 1 0).hom ≃ₗ[ℚ] LinearMap.ker (incidenceMap G o) :=
    kernelCoordinates (differential X ℚ ℚ 0).hom (incidenceMap G o) E1 E0 hE
  exact ⟨(P202.Homology.CellularComparison.comparisonIso X ℚ ℚ 1).symm.toLinearEquiv.trans
    ((homologyOneKernelEquiv C hd).trans K)⟩

/-- The actual H₁ comparison, with no extra interval-chart hypothesis. -/
theorem realization_homology : realization_homologyType := by
  intro V _ G _ D o
  obtain ⟨h⟩ := P202.Homology.CellularDegrees.intervalParametrization_nonempty
  exact realization_homology_of_interval D o h


/-- The geometric cells and their characteristic coordinates belong to one
actual finite CW structure on the original realization. -/
theorem cellular_model : cellular_modelType := by
  intro V _ G _ D o
  obtain ⟨h⟩ := P202.Homology.CellularDegrees.intervalParametrization_nonempty
  refine ⟨embeddedCWStructure D o h, h, vertexLabel, edgeLabel, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (inferInstance : Finite (Σ n, GraphCell (Nat.card V) (Nat.card G.edgeSet) n))
  · intro n; exact PEmpty.instIsEmpty
  · intro c x; rfl
  · intro c; exact edgeCharacteristic_image D o h (edgeLabel c)
  · intro c
    change realizationEdge D o (edgeLabel c) (diskInterval h (h.endpoint 0).val.down) = _ ∧
      realizationEdge D o (edgeLabel c) (diskInterval h (h.endpoint 1).val.down) = _
    rw [diskInterval_endpoint_zero, diskInterval_endpoint_one, realizationEdge_one, realizationEdge_zero]
    exact ⟨rfl,rfl⟩
  · exact embedded_coordinates D o h

/-- Evaluation followed by the dual of the cellular/singular identification. -/
theorem realization_cohomology : realization_cohomologyType := by
  intro V _ G _ D o
  obtain ⟨E⟩ := realization_homology D o
  obtain ⟨U, hU⟩ := realization_universal_coefficients D
  let F := U.trans (LinearEquiv.arrowCongr E (LinearEquiv.refl ℚ ℚ))
  refine ⟨E, F, ?_⟩
  intro a z
  change U a (E.symm z) = _
  rw [hU]

/-- The numerical dimension comes from the finite incidence kernel, after
identifying the actual singular homology. -/
theorem realization_homology_finrank : realization_homology_finrankType := by
  intro V _ G D
  classical
  letI := Fintype.ofFinite V
  letI := Fintype.ofFinite G.edgeSet
  obtain ⟨o⟩ := FiniteCombinatorics.Graph.Trees.orientation_exists G
  obtain ⟨E⟩ := realization_homology D o
  exact ⟨E.symm.finiteDimensional, E.finrank_eq.trans (incidence_nullity G o)⟩

/-- The full rational dual has the same finite dimension. -/
theorem realization_cohomology_finrank : realization_cohomology_finrankType := by
  intro V _ G D
  classical
  letI := Fintype.ofFinite V
  letI := Fintype.ofFinite G.edgeSet
  obtain ⟨o⟩ := FiniteCombinatorics.Graph.Trees.orientation_exists G
  obtain ⟨_, F, _⟩ := realization_cohomology D o
  exact ⟨F.symm.finiteDimensional, F.finrank_eq.trans (incidence_kernel_dual_finrank G o)⟩



/-- An empty vertex type has an empty actual embedded realization. -/
lemma empty_realization {V : Type u} [Finite V] [IsEmpty V] {G : SimpleGraph V}
    (D : Drawing G) : IsEmpty (Realization D) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨v⟩ := (FiniteCombinatorics.Graph.Plane.realization_nonempty_iff D).mp ⟨x⟩
  exact isEmptyElim v

/-- Singular homology of the empty realization vanishes in every degree. -/
lemma empty_realization_homology {V : Type u} [Finite V] [IsEmpty V]
    {G : SimpleGraph V} (D : Drawing G) (n : ℤ) :
    Subsingleton (P202Specs.SingularChains.homology ℚ ℚ (TopCat.of (Realization D)) n) := by
  letI := empty_realization D
  exact ModuleCat.subsingleton_of_isZero
    (P202.SingularDegreeZero.emptyOrdinary ℚ ℚ (TopCat.of (Realization D)) n)

/-- Ordinary rational degree-one homology and cohomology vanish for the empty graph. -/
lemma empty_realization_degree_one {V : Type u} [Finite V] [IsEmpty V]
    {G : SimpleGraph V} (D : Drawing G) :
    Subsingleton (P202Specs.SingularChains.homology ℚ ℚ (TopCat.of (Realization D)) 1) ∧
    Subsingleton (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ (TopCat.of (Realization D)) 1) ∧
    Module.finrank ℚ (P202Specs.SingularChains.homology ℚ ℚ (TopCat.of (Realization D)) 1) = 0 ∧
    Module.finrank ℚ (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ (TopCat.of (Realization D)) 1) = 0 := by
  letI := empty_realization_homology D 1
  obtain ⟨E, _⟩ := realization_universal_coefficients D
  letI : Subsingleton (Module.Dual ℚ
      (P202Specs.SingularChains.homology ℚ ℚ (TopCat.of (Realization D)) 1)) := by
    refine ⟨fun f g => ?_⟩
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp only [hx, map_zero]
  letI : Subsingleton (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ
      (TopCat.of (Realization D)) 1) := E.injective.subsingleton
  exact ⟨inferInstance, inferInstance, Module.finrank_zero_of_subsingleton,
    Module.finrank_zero_of_subsingleton⟩

/-- The empty-graph case, on the actual realization and ordinary singular theories. -/
theorem realization_empty {V : Type u} [Finite V] [IsEmpty V]
    {G : SimpleGraph V} (D : Drawing G) :
    IsEmpty (Realization D) ∧
    Subsingleton (P202Specs.SingularChains.homology ℚ ℚ (TopCat.of (Realization D)) 1) ∧
    Subsingleton (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ (TopCat.of (Realization D)) 1) ∧
    Module.finrank ℚ (P202Specs.SingularChains.homology ℚ ℚ (TopCat.of (Realization D)) 1) = 0 ∧
    Module.finrank ℚ (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ (TopCat.of (Realization D)) 1) = 0 :=
  ⟨empty_realization D, empty_realization_degree_one D⟩

end FiniteCombinatorics.Graph.Plane.CellularBridge
