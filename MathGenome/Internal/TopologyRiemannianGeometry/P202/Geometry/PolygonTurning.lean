import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolygonTurning
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Join
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.DenselyOrdered
import Mathlib.Data.Fintype.Lattice
import Mathlib.LinearAlgebra.AffineSpace.Ordered

/-!
The discrete polygon stage of paper.tex 4885–4916.
A finite grid of actual secants reduces the signed exterior-angle sum to
one short angle at a projection-minimal vertex. Common open half-plane
charts give exact real angle cancellation, including reflex and straight
vertices. The bounded-side-on-left hypothesis fixes the positive sign.
The earlier strip decomposition and triangle-counting helpers are retained.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology
universe u

namespace P202.PolygonTurning
open P202Specs.PolygonTurning

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [Fact (Module.finrank ℝ V = 2)]
variable {n : ℕ} (o : Orientation ℝ V (Fin 2))

omit [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] in
theorem edgeVector_ne_zero {p : Polygon V n} (h : p.HasNondegenerateEdges)
    (i : Fin n) : edgeVector p i ≠ 0 :=
  sub_ne_zero.mpr (h i).symm

/-- Explicit bridge between the source's directed unit tangents and the
angle API's exclusion of its π branch cut. -/
theorem oangle_ne_pi_of_noncuspidal {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (hc : Noncuspidal p) (i : Fin n) :
    o.oangle (incomingVector p i) (edgeVector p i) ≠ (Real.pi : Real.Angle) := by
  intro h
  have hs := (o.oangle_eq_pi_iff_sameRay_neg.mp h).2.2
  have hi := edgeVector_ne_zero he ((finRotate n).symm i)
  have ho := edgeVector_ne_zero he i
  have hn := hs.inv_norm_smul_eq hi (neg_ne_zero.mpr ho)
  exact hc i (by simpa only [NormedSpace.normalize, incomingVector, norm_neg, smul_neg]
    using hn)

theorem exteriorAngle_bounds {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (hc : Noncuspidal p) (i : Fin n) :
    -Real.pi < exteriorAngle o p i ∧ exteriorAngle o p i < Real.pi := by
  refine ⟨Real.Angle.neg_pi_lt_toReal _, ?_⟩
  exact (Real.Angle.toReal_le_pi _).lt_of_ne
    (fun h => oangle_ne_pi_of_noncuspidal o he hc i (Real.Angle.toReal_eq_pi_iff.mp h))

/-- A straight continuation contributes zero; it is not excluded as an
affinely degenerate triple of vertices. -/
theorem exteriorAngle_eq_zero_of_sameRay {p : Polygon V n} (i : Fin n)
    (h : SameRay ℝ (incomingVector p i) (edgeVector p i)) :
    exteriorAngle o p i = 0 := by
  simp [exteriorAngle, o.oangle_eq_zero_iff_sameRay.mpr h]

/-- The smaller unsigned angle at a polygon vertex and the magnitude of its
signed exterior angle are supplementary.  This includes straight continuation. -/
theorem vertexAngle_add_abs_exteriorAngle {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (i : Fin n) :
    InnerProductGeometry.angle (-incomingVector p i) (edgeVector p i) +
      |exteriorAngle o p i| = Real.pi := by
  have hi : incomingVector p i ≠ 0 :=
    sub_ne_zero.mpr (he ((finRotate n).symm i)).symm
  have ho : edgeVector p i ≠ 0 := sub_ne_zero.mpr (he i).symm
  rw [InnerProductGeometry.angle_neg_left, o.angle_eq_abs_oangle_toReal hi ho]
  change Real.pi - |exteriorAngle o p i| + |exteriorAngle o p i| = Real.pi
  exact sub_add_cancel _ _

/-- At a nonnegative turn, the interior sector on the left is the smaller
unsigned angle between the backwards incoming ray and the outgoing ray. -/
theorem exteriorAngle_eq_pi_sub_vertexAngle_of_nonneg {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (i : Fin n)
    (hs : 0 ≤ exteriorAngle o p i) :
    exteriorAngle o p i = Real.pi -
      InnerProductGeometry.angle (-incomingVector p i) (edgeVector p i) := by
  have h := vertexAngle_add_abs_exteriorAngle o he i
  rw [abs_of_nonneg hs] at h
  linarith

/-- At a nonpositive turn, the turn is the smaller unsigned angle minus π;
thus its left-hand interior sector is the complementary reflex sector. -/
theorem exteriorAngle_eq_vertexAngle_sub_pi_of_nonpos {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (i : Fin n)
    (hs : exteriorAngle o p i ≤ 0) :
    exteriorAngle o p i =
      InnerProductGeometry.angle (-incomingVector p i) (edgeVector p i) - Real.pi := by
  have h := vertexAngle_add_abs_exteriorAngle o he i
  rw [abs_of_nonpos hs] at h
  linarith

/-- Positive angular sign gives the convex vertex formula. -/
theorem exteriorAngle_eq_pi_sub_vertexAngle_of_sign_eq_one {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (i : Fin n)
    (hs : (o.oangle (incomingVector p i) (edgeVector p i)).sign = 1) :
    exteriorAngle o p i = Real.pi -
      InnerProductGeometry.angle (-incomingVector p i) (edgeVector p i) := by
  apply exteriorAngle_eq_pi_sub_vertexAngle_of_nonneg o he i
  exact (Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr hs).1.le

/-- Negative angular sign gives the reflex vertex formula, with the full
left-hand angle `2π - angle` rather than the smaller unsigned angle. -/
theorem exteriorAngle_add_reflexVertexAngle_of_sign_eq_neg_one {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (i : Fin n)
    (hs : (o.oangle (incomingVector p i) (edgeVector p i)).sign = -1) :
    exteriorAngle o p i + (2 * Real.pi -
      InnerProductGeometry.angle (-incomingVector p i) (edgeVector p i)) = Real.pi := by
  have h := exteriorAngle_eq_vertexAngle_sub_pi_of_nonpos o he i
    (Real.Angle.toReal_neg_iff_sign_neg.mpr hs).le
  linarith

/-- The convex/reflex formula assembled into a single algebraic identity.
Identifying this sector with the region's actual local interior still requires
its local sidedness and incidence argument. -/
theorem exteriorAngle_add_vertexSector_eq_pi {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (i : Fin n) :
    exteriorAngle o p i +
      (if 0 ≤ exteriorAngle o p i then
        InnerProductGeometry.angle (-incomingVector p i) (edgeVector p i)
       else 2 * Real.pi -
        InnerProductGeometry.angle (-incomingVector p i) (edgeVector p i)) = Real.pi := by
  split_ifs with hs
  · have h := exteriorAngle_eq_pi_sub_vertexAngle_of_nonneg o he i hs
    linarith
  · have h := exteriorAngle_eq_vertexAngle_sub_pi_of_nonpos o he i (le_of_not_ge hs)
    linarith

/-- The same sign test used by the oriented angle API selects a straight
continuation exactly when the turn is zero; the π branch is excluded by
noncuspidality. -/
theorem exteriorAngle_eq_zero_iff_sign_eq_zero {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (hc : Noncuspidal p) (i : Fin n) :
    exteriorAngle o p i = 0 ↔
      (o.oangle (incomingVector p i) (edgeVector p i)).sign = 0 := by
  constructor
  · intro h
    have h' := Real.Angle.toReal_eq_zero_iff.mp h
    simp [h']
  · intro h
    rcases Real.Angle.sign_eq_zero_iff.mp h with h | h
    · simp [exteriorAngle, h]
    · exact (oangle_ne_pi_of_noncuspidal o he hc i h).elim

/-- Straight continuation has unsigned vertex angle π. -/
theorem vertexAngle_eq_pi_of_exteriorAngle_eq_zero {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (i : Fin n) (hs : exteriorAngle o p i = 0) :
    InnerProductGeometry.angle (-incomingVector p i) (edgeVector p i) = Real.pi := by
  simpa [hs] using vertexAngle_add_abs_exteriorAngle o he i

/-- At a noncuspidal vertex the sector selected by the signed turn has the
same strict angle range as the paper's interior-angle convention. -/
theorem vertexSector_mem_Ioo {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (hc : Noncuspidal p) (i : Fin n) :
    (if 0 ≤ exteriorAngle o p i then
        InnerProductGeometry.angle (-incomingVector p i) (edgeVector p i)
       else 2 * Real.pi -
        InnerProductGeometry.angle (-incomingVector p i) (edgeVector p i)) ∈
      Ioo (0 : ℝ) (2 * Real.pi) := by
  have h := exteriorAngle_add_vertexSector_eq_pi o he i
  obtain ⟨hl, hu⟩ := exteriorAngle_bounds o he hc i
  constructor <;> linarith


omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] in
theorem reverse_reverse (p : Polygon V n) : reverse (reverse p) = p := by
  cases p
  simp [reverse, Function.comp_def]

theorem rev_finRotate (i : Fin n) :
    (finRotate n i).rev = (finRotate n).symm i.rev := by
  have := i.neZero
  simp [Fin.rev_add]

theorem rev_finRotate_symm (i : Fin n) :
    ((finRotate n).symm i).rev = finRotate n i.rev := by
  have := i.neZero
  simp [Fin.rev_sub]

omit [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] in
theorem edgeVector_reverse (p : Polygon V n) (i : Fin n) :
    edgeVector (reverse p) i = -incomingVector p i.rev := by
  change p ((finRotate n i).rev) - p i.rev =
    -(p (finRotate n ((finRotate n).symm i.rev)) - p ((finRotate n).symm i.rev))
  rw [rev_finRotate, Equiv.apply_symm_apply, neg_sub]

omit [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] in
theorem incomingVector_reverse (p : Polygon V n) (i : Fin n) :
    incomingVector (reverse p) i = -edgeVector p i.rev := by
  simp only [incomingVector, edgeVector_reverse, rev_finRotate_symm,
    Equiv.symm_apply_apply]

theorem exteriorAngle_reverse {p : Polygon V n} (he : p.HasNondegenerateEdges)
    (hc : Noncuspidal p) (i : Fin n) :
    exteriorAngle o (reverse p) i = -exteriorAngle o p i.rev := by
  unfold exteriorAngle
  rw [incomingVector_reverse, edgeVector_reverse, o.oangle_neg_neg, o.oangle_rev]
  exact Real.Angle.toReal_neg_eq_neg_toReal_iff.mpr
    (oangle_ne_pi_of_noncuspidal o he hc i.rev)

theorem totalTurning_reverse {p : Polygon V n} (he : p.HasNondegenerateEdges)
    (hc : Noncuspidal p) : totalTurning o (reverse p) = -totalTurning o p := by
  simp only [totalTurning, exteriorAngle_reverse o he hc, Finset.sum_neg_distrib]
  congr 1
  exact Equiv.sum_comp (Fin.revPerm : Fin n ≃ Fin n) (exteriorAngle o p)

/-- The direction loop closes modulo 2π for any nondegenerate closed
polygon, without requiring simplicity. Simplicity will be needed to show
that the resulting integer is exactly +1, not an arbitrary integer. -/
theorem sum_oangle_eq_zero (d : Fin n → V) (hd : ∀ i, d i ≠ 0) :
    ∑ i, o.oangle (d ((finRotate n).symm i)) (d i) = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  have : NeZero n := ⟨hn⟩
  have hdiff (i : Fin n) :
      o.oangle (d ((finRotate n).symm i)) (d i) =
        o.oangle (d 0) (d i) - o.oangle (d 0) (d ((finRotate n).symm i)) :=
    (o.oangle_sub_left (hd 0) (hd _) (hd _)).symm
  simp_rw [hdiff]
  rw [Finset.sum_sub_distrib,
    Equiv.sum_comp ((finRotate n).symm : Fin n ≃ Fin n) (fun i => o.oangle (d 0) (d i))]
  exact sub_self _

theorem totalTurning_coe_eq_zero {p : Polygon V n}
    (he : p.HasNondegenerateEdges) : (totalTurning o p : Real.Angle) = 0 := by
  change Real.Angle.coeHom (∑ i, exteriorAngle o p i) = 0
  rw [map_sum]
  simpa only [Real.Angle.coe_coeHom, exteriorAngle, Real.Angle.coe_toReal,
    incomingVector] using sum_oangle_eq_zero o (edgeVector p) (edgeVector_ne_zero he)

/-- An actual integer witness for the total turning, before the geometric
simple-polygon argument that must determine its value. -/
theorem totalTurning_eq_int_mul_two_pi {p : Polygon V n}
    (he : p.HasNondegenerateEdges) :
    ∃ k : ℤ, totalTurning o p = (k : ℝ) * (2 * Real.pi) := by
  obtain ⟨k, hk⟩ := Real.Angle.coe_eq_zero_iff.mp (totalTurning_coe_eq_zero o he)
  exact ⟨k, by simpa only [zsmul_eq_mul] using hk.symm⟩

section CyclicReindexing
variable [NeZero n]

def rotate (p : Polygon V n) (j : Fin n) : Polygon V n := ⟨fun k => p (k + j)⟩

theorem finRotate_add (i j : Fin n) : finRotate n (i+j) = finRotate n i+j := by
  simp only [finRotate_apply]
  abel

theorem finRotate_symm_add (i j : Fin n) :
    (finRotate n).symm (i+j) = (finRotate n).symm i+j := by
  simp only [finRotate_symm_apply]
  abel

theorem edgeVector_rotate (p : Polygon V n) (j i : Fin n) :
    edgeVector (rotate p j) i = edgeVector p (i+j) := by
  simp only [edgeVector, rotate, finRotate_add]

theorem incomingVector_rotate (p : Polygon V n) (j i : Fin n) :
    incomingVector (rotate p j) i = incomingVector p (i+j) := by
  simp only [incomingVector, edgeVector_rotate, finRotate_symm_add]

theorem exteriorAngle_rotate (o : Orientation ℝ V (Fin 2))
    (p : Polygon V n) (j i : Fin n) :
    exteriorAngle o (rotate p j) i = exteriorAngle o p (i+j) := by
  simp only [exteriorAngle, incomingVector_rotate, edgeVector_rotate]

theorem totalTurning_rotate (o : Orientation ℝ V (Fin 2))
    (p : Polygon V n) (j : Fin n) :
    totalTurning o (rotate p j) = totalTurning o p := by
  simp only [totalTurning, exteriorAngle_rotate]
  exact Equiv.sum_comp (Equiv.addRight j) (exteriorAngle o p)

theorem edgeSet_rotate (p : Polygon V n) (j i : Fin n) :
    (rotate p j).edgeSet ℝ i = p.edgeSet ℝ (i+j) := by
  simp only [Polygon.edgeSet, rotate, finRotate_add]

theorem edgePath_rotate (p : Polygon V n) (j i : Fin n) :
    (rotate p j).edgePath ℝ i = p.edgePath ℝ (i+j) := by
  simp only [Polygon.edgePath, rotate, finRotate_add]

theorem boundary_rotate (p : Polygon V n) (j : Fin n) :
    (rotate p j).boundary ℝ = p.boundary ℝ := by
  simp only [Polygon.boundary, edgeSet_rotate]
  exact (Equiv.addRight j).surjective.iUnion_comp (fun i => p.edgeSet ℝ i)

theorem isSimple_rotate {p : Polygon V n} (hp : IsSimple p) (j : Fin n) :
    IsSimple (rotate p j) := by
  refine ⟨hp.1, hp.2.1.comp (Equiv.addRight j).injective, ?_, ?_⟩
  · intro i
    simpa only [rotate, finRotate_add] using hp.2.2.1 (i+j)
  · intro i k hik
    rw [edgeSet_rotate]
    change Disjoint (openSegment ℝ (p (i+j)) (p (finRotate n i+j))) _
    rw [← finRotate_add]
    exact hp.2.2.2 (i+j) (k+j) (fun h => hik (add_right_cancel h))

theorem noncuspidal_rotate {p : Polygon V n} (hp : Noncuspidal p) (j : Fin n) :
    Noncuspidal (rotate p j) := by
  intro i
  simpa only [incomingVector_rotate, edgeVector_rotate] using hp (i+j)

theorem isBoundedSide_rotate {p : Polygon V n} {U : Set V}
    (hU : IsBoundedSide p U) (j : Fin n) : IsBoundedSide (rotate p j) U := by
  exact ⟨hU.1, hU.2.1, hU.2.2.1, (boundary_rotate p j).symm ▸ hU.2.2.2⟩

theorem hasBoundedSideOnLeft_rotate (o : Orientation ℝ V (Fin 2))
    {p : Polygon V n} {U : Set V} (hp : HasBoundedSideOnLeft o p U) (j : Fin n) :
    HasBoundedSideOnLeft o (rotate p j) U := by
  intro i t ht
  simpa only [edgePath_rotate, edgeVector_rotate] using hp (i+j) t ht


end CyclicReindexing

section EdgeIntersections
omit [Fact (Module.finrank ℝ V = 2)]

/-- A relative-interior point of one edge cannot lie on any other closed edge. -/
theorem edgePath_ne_of_interior {p : Polygon V n} (hp : IsSimple p)
    {i j : Fin n} (hij : i ≠ j) {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    p.edgePath ℝ i t ≠ p.edgePath ℝ j u := by
  intro heq
  have hi : p.edgePath ℝ i t ∈ openSegment ℝ (p i) (p (finRotate n i)) :=
    lineMap_mem_openSegment ℝ _ _ ht
  have hj : p.edgePath ℝ j u ∈ p.edgeSet ℝ j := ⟨u, hu, rfl⟩
  exact Set.disjoint_left.mp (hp.2.2.2 i j hij) hi (heq.symm ▸ hj)

/-- Every point of a straight closed edge is an endpoint or a relative-interior point. -/
theorem edgeSet_mem_cases (p : Polygon V n) (i : Fin n) {z : V}
    (hz : z ∈ p.edgeSet ℝ i) :
    z = p i ∨ z = p (finRotate n i) ∨
      z ∈ openSegment ℝ (p i) (p (finRotate n i)) := by
  rcases hz with ⟨t, ht, rfl⟩
  by_cases h0 : t = 0
  · left
    simp [h0]
  by_cases h1 : t = 1
  · right; left
    simp [h1]
  right; right
  exact lineMap_mem_openSegment ℝ _ _
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩

/-- Intersections of two distinct closed polygon edges can contain only
endpoints of each edge. -/
theorem endpoints_of_mem_distinct_edges {p : Polygon V n} (hp : IsSimple p)
    {i j : Fin n} (hij : i ≠ j) {z : V}
    (hi : z ∈ p.edgeSet ℝ i) (hj : z ∈ p.edgeSet ℝ j) :
    (z = p i ∨ z = p (finRotate n i)) ∧
      (z = p j ∨ z = p (finRotate n j)) := by
  constructor
  · rcases edgeSet_mem_cases p i hi with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (Set.disjoint_left.mp (hp.2.2.2 i j hij) h hj).elim
  · rcases edgeSet_mem_cases p j hj with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (Set.disjoint_left.mp (hp.2.2.2 j i hij.symm) h hi).elim

theorem edgeSet_left_mem (p : Polygon V n) (i : Fin n) : p i ∈ p.edgeSet ℝ i := by
  exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩

theorem edgeSet_right_mem (p : Polygon V n) (i : Fin n) :
    p (finRotate n i) ∈ p.edgeSet ℝ i := by
  exact ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩

/-- Complete geometric classification: distinct closed edges meet precisely
at their cyclically shared endpoints, and nowhere else. -/
theorem edgeSet_inter_mem_iff {p : Polygon V n} (hp : IsSimple p)
    {i j : Fin n} (hij : i ≠ j) (z : V) :
    z ∈ p.edgeSet ℝ i ∩ p.edgeSet ℝ j ↔
      (finRotate n i = j ∧ z = p j) ∨
      (finRotate n j = i ∧ z = p i) := by
  constructor
  · intro hz
    obtain ⟨hi, hj⟩ := endpoints_of_mem_distinct_edges hp hij hz.1 hz.2
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact (hij (hp.2.1 (hi.symm.trans hj))).elim
    · exact Or.inr ⟨(hp.2.1 (hi.symm.trans hj)).symm, hi⟩
    · exact Or.inl ⟨hp.2.1 (hi.symm.trans hj), hj⟩
    · exact (hij ((finRotate n).injective (hp.2.1 (hi.symm.trans hj)))).elim
  · rintro (⟨hij', rfl⟩ | ⟨hji', rfl⟩)
    · exact ⟨hij' ▸ edgeSet_right_mem p i, edgeSet_left_mem p j⟩
    · exact ⟨edgeSet_left_mem p i, hji' ▸ edgeSet_right_mem p j⟩


/-- A polygon vertex belongs to a closed edge exactly when it is one of its endpoints. -/
theorem vertex_mem_edgeSet_iff {p : Polygon V n} (hp : IsSimple p)
    (i k : Fin n) : p k ∈ p.edgeSet ℝ i ↔ k = i ∨ k = finRotate n i := by
  constructor
  · intro hk
    by_cases hik : i = k
    · exact Or.inl hik.symm
    obtain ⟨hi, _⟩ := endpoints_of_mem_distinct_edges hp hik hk (edgeSet_left_mem p k)
    exact hi.imp (fun h => hp.2.1 h) (fun h => hp.2.1 h)
  · rintro (h | h)
    · rw [h]; exact edgeSet_left_mem p i
    · rw [h]; exact edgeSet_right_mem p i

/-- Nonadjacent closed edges of a simple polygon are disjoint. -/
theorem disjoint_edgeSets_of_nonadjacent {p : Polygon V n} (hp : IsSimple p)
    {i j : Fin n} (hij : i ≠ j) (hnext : finRotate n i ≠ j)
    (hprev : finRotate n j ≠ i) :
    Disjoint (p.edgeSet ℝ i) (p.edgeSet ℝ j) := by
  apply Set.disjoint_left.mpr
  intro z hi hj
  rcases (edgeSet_inter_mem_iff hp hij z).mp ⟨hi, hj⟩ with h | h
  · exact hnext h.1
  · exact hprev h.1

/-- All collisions of closed-edge parametrizations are the identical
parameter on the same edge or the two representations of one shared endpoint. -/
theorem edgePath_eq_iff {p : Polygon V n} (hp : IsSimple p)
    (i j : Fin n) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    p.edgePath ℝ i t = p.edgePath ℝ j u ↔
      (i = j ∧ t = u) ∨
      (finRotate n i = j ∧ t = 1 ∧ u = 0) ∨
      (finRotate n j = i ∧ t = 0 ∧ u = 1) := by
  constructor
  · intro heq
    by_cases hij : i = j
    · left
      refine ⟨hij, ?_⟩
      subst j
      exact AffineMap.lineMap_injective ℝ (hp.2.2.1 i) heq
    right
    have hm : p.edgePath ℝ i t ∈ p.edgeSet ℝ i ∩ p.edgeSet ℝ j :=
      ⟨⟨t, ht, rfl⟩, heq.symm ▸ (show p.edgePath ℝ j u ∈ p.edgeSet ℝ j from ⟨u, hu, rfl⟩)⟩
    rcases (edgeSet_inter_mem_iff hp hij _).mp hm with ⟨hn, hz⟩ | ⟨hn, hz⟩
    · left
      refine ⟨hn, ?_, ?_⟩
      · apply (AffineMap.lineMap_eq_right_iff.mp ?_).resolve_left (hp.2.2.1 i)
        simpa only [Polygon.edgePath, hn] using hz
      · apply (AffineMap.lineMap_eq_left_iff.mp ?_).resolve_left (hp.2.2.1 j)
        simpa only [Polygon.edgePath] using heq.symm.trans hz
    · right
      refine ⟨hn, ?_, ?_⟩
      · apply (AffineMap.lineMap_eq_left_iff.mp ?_).resolve_left (hp.2.2.1 i)
        exact hz
      · apply (AffineMap.lineMap_eq_right_iff.mp ?_).resolve_left (hp.2.2.1 j)
        simpa only [Polygon.edgePath, hn] using heq.symm.trans hz
  · rintro (⟨rfl, rfl⟩ | ⟨hn, rfl, rfl⟩ | ⟨hn, rfl, rfl⟩)
    · rfl
    · simp [Polygon.edgePath, hn]
    · simp [Polygon.edgePath, hn]

end EdgeIntersections

section Projection

omit [Fact (Module.finrank ℝ V = 2)] in
/-- A finite set of distinct vertices admits a separating Euclidean
projection. This also permits collinear successive triples: the forbidden
directions come only from differences of distinct vertices. -/
theorem exists_separating_direction (p : Polygon V n)
    (hp : Function.Injective p.vertices) :
    ∃ v : V, Function.Injective (fun i : Fin n => inner ℝ v (p i)) := by
  classical
  let I := {ij : Fin n × Fin n // ij.1 ≠ ij.2}
  let f : I → Module.Dual ℝ V := fun ij =>
    (innerSL ℝ (p ij.val.1 - p ij.val.2)).toLinearMap
  have hf (ij : I) : ∃ v, f ij v ≠ 0 := by
    refine ⟨p ij.val.1 - p ij.val.2, ?_⟩
    exact inner_self_ne_zero.mpr (sub_ne_zero.mpr (hp.ne ij.property))
  obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  refine ⟨v, fun i j hij => ?_⟩
  by_contra hne
  have h := hv ⟨(i, j), hne⟩
  change inner ℝ (p i - p j) v ≠ 0 at h
  exact h (by simpa only [real_inner_comm, inner_sub_right] using sub_eq_zero.mpr hij)

omit [Fact (Module.finrank ℝ V = 2)] in
/-- The separating projection as a continuous linear map, for use with
actual edge paths and connected strip cells. -/
theorem exists_separatingProjection (p : Polygon V n)
    (hp : Function.Injective p.vertices) :
    ∃ x : V →L[ℝ] ℝ, Function.Injective (x ∘ p.vertices) := by
  obtain ⟨v, hv⟩ := exists_separating_direction p hp
  exact ⟨innerSL ℝ v, hv⟩

/-- The intersection of the supporting line of an edge with the line whose
first coordinate is `s`. When the edge is nonvertical, this is the unique
point of that supporting line at that coordinate. -/
def edgeAtCoordinate (x : V →L[ℝ] ℝ) (p : Polygon V n) (i : Fin n) (s : ℝ) : V :=
  p.edgePath ℝ i ((s - x (p i)) / (x (p (finRotate n i)) - x (p i)))

omit [Fact (Module.finrank ℝ V = 2)] in
theorem projection_edgePath (x : V →L[ℝ] ℝ) (p : Polygon V n)
    (i : Fin n) (t : ℝ) :
    x (p.edgePath ℝ i t) =
      t * (x (p (finRotate n i)) - x (p i)) + x (p i) := by
  simp [Polygon.edgePath, AffineMap.lineMap_apply_module', map_add, map_smul, map_sub]

omit [Fact (Module.finrank ℝ V = 2)] in
theorem projection_edgeAtCoordinate (x : V →L[ℝ] ℝ) (p : Polygon V n)
    (i : Fin n) (hi : x (p (finRotate n i)) ≠ x (p i)) (s : ℝ) :
    x (edgeAtCoordinate x p i s) = s := by
  rw [edgeAtCoordinate, projection_edgePath]
  field_simp
  ring

omit [Fact (Module.finrank ℝ V = 2)] in
theorem edgeAtCoordinate_projection_edgePath (x : V →L[ℝ] ℝ) (p : Polygon V n)
    (i : Fin n) (hi : x (p (finRotate n i)) ≠ x (p i)) (t : ℝ) :
    edgeAtCoordinate x p i (x (p.edgePath ℝ i t)) = p.edgePath ℝ i t := by
  unfold edgeAtCoordinate
  rw [projection_edgePath]
  congr 1
  field_simp
  ring

omit [Fact (Module.finrank ℝ V = 2)] in
theorem continuous_edgeAtCoordinate (x : V →L[ℝ] ℝ) (p : Polygon V n) (i : Fin n) :
    Continuous (edgeAtCoordinate x p i) := by
  unfold edgeAtCoordinate Polygon.edgePath
  simp only [AffineMap.lineMap_apply_module']
  fun_prop

omit [Fact (Module.finrank ℝ V = 2)] in
/-- A coordinate strictly between the endpoint coordinates corresponds to
an edge parameter strictly between zero and one, in either edge direction. -/
theorem lineParameter_mem_Ioo {a b s : ℝ} (hs : s ∈ uIoo a b) :
    (s - a) / (b - a) ∈ Ioo (0 : ℝ) 1 := by
  rcases le_total a b with hab | hab
  · rw [uIoo_of_le hab] at hs
    have hd : 0 < b - a := by linarith [hs.1, hs.2]
    exact ⟨div_pos (by linarith [hs.1]) hd,
      (div_lt_one hd).mpr (by linarith [hs.2])⟩
  · rw [uIoo_of_ge hab] at hs
    have hd : b - a < 0 := by linarith [hs.1, hs.2]
    exact ⟨div_pos_of_neg_of_neg (by linarith [hs.2]) hd,
      (div_lt_one_of_neg hd).mpr (by linarith [hs.1])⟩

omit [Fact (Module.finrank ℝ V = 2)] in
theorem edgeAtCoordinate_mem_openSegment (x : V →L[ℝ] ℝ) (p : Polygon V n)
    (i : Fin n) {s : ℝ} (hs : s ∈ uIoo (x (p i)) (x (p (finRotate n i)))) :
    edgeAtCoordinate x p i s ∈ openSegment ℝ (p i) (p (finRotate n i)) :=
  lineMap_mem_openSegment ℝ _ _ (lineParameter_mem_Ioo hs)

omit [Fact (Module.finrank ℝ V = 2)] in
theorem edgeAtCoordinate_mem_edgeSet (x : V →L[ℝ] ℝ) (p : Polygon V n)
    (i : Fin n) {s : ℝ} (hs : s ∈ uIoo (x (p i)) (x (p (finRotate n i)))) :
    edgeAtCoordinate x p i s ∈ p.edgeSet ℝ i := by
  rw [Polygon.edgeSet, affineSegment_eq_segment]
  exact openSegment_subset_segment ℝ _ _ (edgeAtCoordinate_mem_openSegment x p i hs)

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Two active edges of a simple polygon have distinct points on every
vertical line in the common open range. This uses the actual geometric
simplicity hypothesis rather than an assumed order of the edges. -/
theorem edgeAtCoordinate_ne (x : V →L[ℝ] ℝ) {p : Polygon V n}
    (hp : IsSimple p) {i j : Fin n} (hij : i ≠ j) {s : ℝ}
    (hi : s ∈ uIoo (x (p i)) (x (p (finRotate n i))))
    (hj : s ∈ uIoo (x (p j)) (x (p (finRotate n j)))) :
    edgeAtCoordinate x p i s ≠ edgeAtCoordinate x p j s := by
  intro heq
  exact Set.disjoint_left.mp (hp.2.2.2 i j hij)
    (edgeAtCoordinate_mem_openSegment x p i hi)
    (heq ▸ edgeAtCoordinate_mem_edgeSet x p j hj)

/-- Inner products with a nonzero direction and its positive quarter turn
are genuine plane coordinates. -/
theorem inner_coordinates_injective (v : V) (hv : v ≠ 0) :
    Function.Injective (fun z : V =>
      (inner ℝ v z, inner ℝ (o.rightAngleRotation v) z)) := by
  intro z w h
  have h₀ : inner ℝ v (z - w) = 0 := by
    rw [inner_sub_right, (Prod.mk.inj h).1, sub_self]
  have h₁ : inner ℝ (o.rightAngleRotation v) (z - w) = 0 := by
    rw [inner_sub_right, (Prod.mk.inj h).2, sub_self]
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  let B := o.basisRightAngleRotation v hv
  have hrepr := congrArg (fun a => inner ℝ a (z - w)) (B.sum_repr (z - w))
  simp only [Fin.sum_univ_two, inner_add_left, real_inner_smul_left,
    B, Orientation.coe_basisRightAngleRotation, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, h₀, h₁, mul_zero, add_zero] at hrepr
  exact hrepr.symm

/-- A genuine two-coordinate system with no vertical polygon edge. The
first coordinate separates every pair of vertices, not only neighbors. -/
theorem exists_separatingCoordinates (o : Orientation ℝ V (Fin 2)) {p : Polygon V n} (hp : IsSimple p) :
    ∃ x y : V →L[ℝ] ℝ,
      Function.Injective (fun z : V => (x z, y z)) ∧
      Function.Injective (x ∘ p.vertices) := by
  obtain ⟨v, hv⟩ := exists_separating_direction p hp.2.1
  have hn : 2 < n := hp.1
  have hv₀ : v ≠ 0 := by
    intro hzero
    have h : (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ :=
      hv (by simp [hzero])
    have hval : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  exact ⟨innerSL ℝ v, innerSL ℝ (o.rightAngleRotation v),
    inner_coordinates_injective o v hv₀, hv⟩

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Active edge graphs cannot exchange vertical order within a connected
strip. `x` and `y` are actual plane coordinates; simplicity supplies the
nonintersection needed by the intermediate value argument. -/
theorem edgeHeight_lt_on_strip (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p) {i j : Fin n} (hij : i ≠ j)
    (hxi : x (p (finRotate n i)) ≠ x (p i))
    (hxj : x (p (finRotate n j)) ≠ x (p j))
    {S : Set ℝ} (hS : IsPreconnected S)
    (hi : S ⊆ uIoo (x (p i)) (x (p (finRotate n i))))
    (hj : S ⊆ uIoo (x (p j)) (x (p (finRotate n j))))
    {s₀ : ℝ} (hs₀ : s₀ ∈ S)
    (hlt : y (edgeAtCoordinate x p i s₀) < y (edgeAtCoordinate x p j s₀)) :
    ∀ s ∈ S, y (edgeAtCoordinate x p i s) < y (edgeAtCoordinate x p j s) := by
  have hne (s : ℝ) (hs : s ∈ S) :
      y (edgeAtCoordinate x p j s) - y (edgeAtCoordinate x p i s) ≠ 0 := by
    intro h
    apply edgeAtCoordinate_ne x hp hij (hi hs) (hj hs)
    apply hxy
    apply Prod.ext
    · dsimp
      rw [projection_edgeAtCoordinate x p i hxi, projection_edgeAtCoordinate x p j hxj]
    · exact (sub_eq_zero.mp h).symm
  have hc : Continuous (fun s =>
      y (edgeAtCoordinate x p j s) - y (edgeAtCoordinate x p i s)) :=
    (y.continuous.comp (continuous_edgeAtCoordinate x p j)).sub
      (y.continuous.comp (continuous_edgeAtCoordinate x p i))
  intro s hs
  exact sub_pos.mp (hS.lt_of_ne hc.continuousOn hne ⟨s₀, hs₀, sub_pos.mpr hlt⟩ hs)

omit [Fact (Module.finrank ℝ V = 2)] in
/-- A connected strip cell missing the polygon boundary cannot partly lie
in the domain and partly outside it. The frontier equality is the original
geometric input, with no Jordan or triangulation certificate assumed. -/
theorem subset_or_disjoint_of_avoids_boundary {p : Polygon V n} {U C : Set V}
    (hU : IsBoundedSide p U) (hC : IsPreconnected C)
    (hboundary : Disjoint C (p.boundary ℝ)) : C ⊆ U ∨ Disjoint C U := by
  by_cases h : (C ∩ U).Nonempty
  · left
    apply hC.subset_of_closure_inter_subset hU.1 h
    intro z hz
    by_contra hzU
    have hzfr : z ∈ frontier U := by
      rw [frontier, hU.1.interior_eq]
      exact ⟨hz.1, hzU⟩
    exact Set.disjoint_left.mp hboundary hz.2 (hU.2.2.2 ▸ hzfr)
  · right
    exact Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Once a strip contains no endpoint coordinate, an edge crossing one
vertical line of the strip crosses all of them. -/
theorem Ioo_subset_uIoo_of_no_endpoints {a b c d s : ℝ}
    (hs : s ∈ Ioo a b) (hcd : s ∈ uIoo c d)
    (hc : c ∉ Ioo a b) (hd : d ∉ Ioo a b) : Ioo a b ⊆ uIoo c d := by
  rcases le_total c d with h | h
  · rw [uIoo_of_le h] at hcd ⊢
    have hca : c ≤ a := le_of_not_gt (fun hac => hc ⟨hac, hcd.1.trans hs.2⟩)
    have hbd : b ≤ d := le_of_not_gt (fun hdb => hd ⟨hs.1.trans hcd.2, hdb⟩)
    exact fun _ ht => ⟨hca.trans_lt ht.1, ht.2.trans_le hbd⟩
  · rw [uIoo_of_ge h] at hcd ⊢
    have hda : d ≤ a := le_of_not_gt (fun had => hd ⟨had, hcd.1.trans hs.2⟩)
    have hbc : b ≤ c := le_of_not_gt (fun hcb => hc ⟨hs.1.trans hcd.2, hcb⟩)
    exact fun _ ht => ⟨hda.trans_lt ht.1, ht.2.trans_le hbc⟩

omit [Fact (Module.finrank ℝ V = 2)] in
/-- In a strip containing no polygon vertex, its active edge set is
constant. No condition on collinearity of vertices is needed. -/
theorem edgeActive_on_strip (x : V →L[ℝ] ℝ) (p : Polygon V n) {a b : ℝ}
    (hvertices : ∀ k : Fin n, x (p k) ∉ Ioo a b) (i : Fin n)
    {s : ℝ} (hs : s ∈ Ioo a b)
    (hi : s ∈ uIoo (x (p i)) (x (p (finRotate n i)))) :
    Ioo a b ⊆ uIoo (x (p i)) (x (p (finRotate n i))) :=
  Ioo_subset_uIoo_of_no_endpoints hs hi (hvertices i) (hvertices _)

/-- The second coordinate of the edge intersection, as a genuine affine
function of the first coordinate. -/
def edgeHeight (x y : V →L[ℝ] ℝ) (p : Polygon V n) (i : Fin n) : ℝ →ᵃ[ℝ] ℝ :=
  let m := (x (p (finRotate n i)) - x (p i))⁻¹ *
    (y (p (finRotate n i)) - y (p i))
  m • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ (y (p i) - m * x (p i))

omit [Fact (Module.finrank ℝ V = 2)] in
theorem edgeHeight_eq (x y : V →L[ℝ] ℝ) (p : Polygon V n) (i : Fin n) (s : ℝ) :
    edgeHeight x y p i s = y (edgeAtCoordinate x p i s) := by
  simp [edgeHeight, edgeAtCoordinate, projection_edgePath, div_eq_mul_inv]
  ring

omit [Fact (Module.finrank ℝ V = 2)] in
theorem edgeAtCoordinate_eq_of_mem_edgeSet (x : V →L[ℝ] ℝ) (p : Polygon V n)
    (i : Fin n) (hi : x (p (finRotate n i)) ≠ x (p i)) {z : V}
    (hz : z ∈ p.edgeSet ℝ i) : edgeAtCoordinate x p i (x z) = z := by
  rcases hz with ⟨t, ht, rfl⟩
  exact edgeAtCoordinate_projection_edgePath x p i hi t

/-- A vertical band between two affine edge graphs, within an open strip. -/
def stripBand (x y : V →L[ℝ] ℝ) (a b : ℝ) (lower upper : ℝ →ᵃ[ℝ] ℝ) : Set V :=
  {z | x z ∈ Ioo a b ∧ lower (x z) < y z ∧ y z < upper (x z)}

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Strip cells are convex even when their closures degenerate to a
triangle on one cut line or contain extra collinear boundary vertices. -/
theorem convex_stripBand (x y : V →L[ℝ] ℝ) (a b : ℝ)
    (lower upper : ℝ →ᵃ[ℝ] ℝ) : Convex ℝ (stripBand x y a b lower upper) := by
  let X := x.toLinearMap.toAffineMap
  let Y := y.toLinearMap.toAffineMap
  have h₀ := (convex_Ioo a b).linear_preimage x.toLinearMap
  have h₁ := (convex_Ioi (0 : ℝ)).affine_preimage (Y - lower.comp X)
  have h₂ := (convex_Ioi (0 : ℝ)).affine_preimage (upper.comp X - Y)
  convert h₀.inter (h₁.inter h₂) using 1
  ext z
  simp [stripBand, X, Y, sub_pos]

omit [Fact (Module.finrank ℝ V = 2)] in
theorem isOpen_stripBand (x y : V →L[ℝ] ℝ) (a b : ℝ)
    (lower upper : ℝ →ᵃ[ℝ] ℝ) : IsOpen (stripBand x y a b lower upper) :=
  (isOpen_Ioo.preimage x.continuous).inter
    ((isOpen_lt (lower.continuous_of_finiteDimensional.comp x.continuous) y.continuous).inter
      (isOpen_lt y.continuous (upper.continuous_of_finiteDimensional.comp x.continuous)))

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Distinct active edges have distinct heights in actual plane coordinates. -/
theorem edgeHeight_ne (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p) {i j : Fin n} (hij : i ≠ j)
    (hxi : x (p (finRotate n i)) ≠ x (p i))
    (hxj : x (p (finRotate n j)) ≠ x (p j)) {s : ℝ}
    (hi : s ∈ uIoo (x (p i)) (x (p (finRotate n i))))
    (hj : s ∈ uIoo (x (p j)) (x (p (finRotate n j)))) :
    edgeHeight x y p i s ≠ edgeHeight x y p j s := by
  intro h
  apply edgeAtCoordinate_ne x hp hij hi hj
  apply hxy
  apply Prod.ext
  · dsimp
    rw [projection_edgeAtCoordinate x p i hxi, projection_edgeAtCoordinate x p j hxj]
  · simpa only [edgeHeight_eq] using h

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Adjacency in the sorted active-edge order can be tested on just one
vertical line. No edge can enter the gap elsewhere in the strip. -/
theorem stripGap_on_strip (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i)) {a b : ℝ}
    (hvertices : ∀ k : Fin n, x (p k) ∉ Ioo a b)
    {i j : Fin n} {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo a b)
    (hi₀ : s₀ ∈ uIoo (x (p i)) (x (p (finRotate n i))))
    (hj₀ : s₀ ∈ uIoo (x (p j)) (x (p (finRotate n j))))
    (hgap₀ : ∀ k : Fin n, s₀ ∈ uIoo (x (p k)) (x (p (finRotate n k))) →
      edgeHeight x y p k s₀ ≤ edgeHeight x y p i s₀ ∨
        edgeHeight x y p j s₀ ≤ edgeHeight x y p k s₀) :
    ∀ s ∈ Ioo a b, ∀ k : Fin n, s ∈ uIoo (x (p k)) (x (p (finRotate n k))) →
      edgeHeight x y p k s ≤ edgeHeight x y p i s ∨
        edgeHeight x y p j s ≤ edgeHeight x y p k s := by
  have hi := edgeActive_on_strip x p hvertices i hs₀ hi₀
  have hj := edgeActive_on_strip x p hvertices j hs₀ hj₀
  intro s hs k hks
  have hk := edgeActive_on_strip x p hvertices k hs hks
  rcases hgap₀ k (hk hs₀) with hki | hjk
  · left
    by_cases h : k = i
    · subst k
      exact le_rfl
    have hlt : edgeHeight x y p k s₀ < edgeHeight x y p i s₀ :=
      hki.lt_of_ne (edgeHeight_ne x y hxy hp h (hx k) (hx i) (hk hs₀) hi₀)
    have horder := edgeHeight_lt_on_strip x y hxy hp h (hx k) (hx i)
      isPreconnected_Ioo hk hi hs₀ (by simpa only [edgeHeight_eq] using hlt) s hs
    simpa only [edgeHeight_eq] using horder.le
  · right
    by_cases h : j = k
    · subst k
      exact le_rfl
    have hlt : edgeHeight x y p j s₀ < edgeHeight x y p k s₀ :=
      hjk.lt_of_ne (edgeHeight_ne x y hxy hp h (hx j) (hx k) hj₀ (hk hs₀))
    have horder := edgeHeight_lt_on_strip x y hxy hp h (hx j) (hx k)
      isPreconnected_Ioo hj hk hs₀ (by simpa only [edgeHeight_eq] using hlt) s hs
    simpa only [edgeHeight_eq] using horder.le

omit [Fact (Module.finrank ℝ V = 2)] in
/-- A closed edge meeting a strip without vertices meets it in its open
edge, so its first coordinate is strictly between its endpoint coordinates. -/
theorem coordinate_mem_uIoo_of_mem_edgeSet (x : V →L[ℝ] ℝ) (p : Polygon V n)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i)) {a b : ℝ}
    (hvertices : ∀ i : Fin n, x (p i) ∉ Ioo a b) {z : V}
    (hz : x z ∈ Ioo a b) (i : Fin n) (hzi : z ∈ p.edgeSet ℝ i) :
    x z ∈ uIoo (x (p i)) (x (p (finRotate n i))) := by
  rcases hzi with ⟨t, ht, hzt⟩
  have ht₀ : t ≠ 0 := by
    intro htzero
    subst t
    have hzv : z = p i := by simpa [Polygon.edgePath] using hzt.symm
    exact hvertices i (hzv ▸ hz)
  have ht₁ : t ≠ 1 := by
    intro htone
    subst t
    have hzv : z = p (finRotate n i) := by simpa [Polygon.edgePath] using hzt.symm
    exact hvertices (finRotate n i) (hzv ▸ hz)
  rw [← hzt]
  change x (p.edgePath ℝ i t) ∈ _
  rw [projection_edgePath]
  rcases lt_or_gt_of_ne (hx i) with h | h
  · rw [uIoo_of_gt h]
    constructor <;> nlinarith [lt_of_le_of_ne ht.1 (Ne.symm ht₀), lt_of_le_of_ne ht.2 ht₁]
  · rw [uIoo_of_lt h]
    constructor <;> nlinarith [lt_of_le_of_ne ht.1 (Ne.symm ht₀), lt_of_le_of_ne ht.2 ht₁]

omit [Fact (Module.finrank ℝ V = 2)] in
/-- The adjacent-edge gap test implies that the entire open strip cell
misses the polygon boundary. The test quantifies over actual polygon edges. -/
theorem stripBand_disjoint_boundary (x y : V →L[ℝ] ℝ) (p : Polygon V n)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i)) {a b : ℝ}
    (hvertices : ∀ i : Fin n, x (p i) ∉ Ioo a b)
    (lower upper : ℝ →ᵃ[ℝ] ℝ)
    (hgap : ∀ s ∈ Ioo a b, ∀ i : Fin n,
      s ∈ uIoo (x (p i)) (x (p (finRotate n i))) →
        edgeHeight x y p i s ≤ lower s ∨ upper s ≤ edgeHeight x y p i s) :
    Disjoint (stripBand x y a b lower upper) (p.boundary ℝ) := by
  apply Set.disjoint_left.mpr
  intro z hz hzb
  rcases mem_iUnion.mp hzb with ⟨i, hi⟩
  have hzi := edgeAtCoordinate_eq_of_mem_edgeSet x p i (hx i) hi
  have heq : edgeHeight x y p i (x z) = y z := by rw [edgeHeight_eq, hzi]
  have hactive := coordinate_mem_uIoo_of_mem_edgeSet x p hx hvertices hz.1 i hi
  rcases hgap (x z) hz.1 i hactive with h | h
  · linarith [hz.2.1, heq]
  · linarith [hz.2.2, heq]

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Selecting a strip cell by a single point is justified by connectedness;
this statement uses the actual bounded domain and its exact frontier. -/
theorem stripBand_subset_or_disjoint (x y : V →L[ℝ] ℝ) {p : Polygon V n}
    {U : Set V} (hU : IsBoundedSide p U) (a b : ℝ) (lower upper : ℝ →ᵃ[ℝ] ℝ)
    (hboundary : Disjoint (stripBand x y a b lower upper) (p.boundary ℝ)) :
    stripBand x y a b lower upper ⊆ U ∨
      Disjoint (stripBand x y a b lower upper) U :=
  subset_or_disjoint_of_avoids_boundary hU
    (convex_stripBand x y a b lower upper).isPreconnected hboundary

omit [Fact (Module.finrank ℝ V = 2)] in
/-- The cell bounded by adjacent active edges is either wholly inside or
wholly outside the polygonal domain. Adjacency and activity are checked at
one strip coordinate; all geometric propagation is proved above. -/
theorem adjacent_stripBand_subset_or_disjoint (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i))
    {U : Set V} (hU : IsBoundedSide p U) {a b : ℝ}
    (hvertices : ∀ k : Fin n, x (p k) ∉ Ioo a b)
    {i j : Fin n} {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo a b)
    (hi₀ : s₀ ∈ uIoo (x (p i)) (x (p (finRotate n i))))
    (hj₀ : s₀ ∈ uIoo (x (p j)) (x (p (finRotate n j))))
    (hgap₀ : ∀ k : Fin n, s₀ ∈ uIoo (x (p k)) (x (p (finRotate n k))) →
      edgeHeight x y p k s₀ ≤ edgeHeight x y p i s₀ ∨
        edgeHeight x y p j s₀ ≤ edgeHeight x y p k s₀) :
    stripBand x y a b (edgeHeight x y p i) (edgeHeight x y p j) ⊆ U ∨
      Disjoint (stripBand x y a b (edgeHeight x y p i) (edgeHeight x y p j)) U := by
  apply stripBand_subset_or_disjoint x y hU
  exact stripBand_disjoint_boundary x y p hx hvertices _ _
    (stripGap_on_strip x y hxy hp hx hvertices hs₀ hi₀ hj₀ hgap₀)

/-- The coordinate system supplies an actual vector along a vertical line,
with unit increase in its second coordinate. -/
theorem exists_verticalDirection (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z))) :
    ∃ d : V, x d = 0 ∧ y d = 1 := by
  let f := x.toLinearMap.prod y.toLinearMap
  let e := LinearEquiv.ofInjectiveOfFinrankEq f hxy (by
    simp [Module.finrank_prod, Fact.out (p := Module.finrank ℝ V = 2)])
  refine ⟨e.symm (0, 1), ?_, ?_⟩
  · exact congrArg Prod.fst (e.apply_symm_apply (0, 1))
  · exact congrArg Prod.snd (e.apply_symm_apply (0, 1))

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Every positive ray from a point of the bounded domain meets its actual
boundary. The unboundedness is detected by a continuous linear coordinate. -/
theorem exists_boundary_on_ray {p : Polygon V n} {U : Set V}
    (hU : IsBoundedSide p U) {z : V} (hz : z ∈ U)
    (y : V →L[ℝ] ℝ) (d : V) (hd : y d = 1) :
    ∃ t : ℝ, 0 < t ∧ z + t • d ∈ p.boundary ℝ := by
  let C := (fun t : ℝ => z + t • d) '' Ici (0 : ℝ)
  have hC : IsPreconnected C := isPreconnected_Ici.image _ (by fun_prop)
  have hzC : z ∈ C := ⟨0, by simp, by simp⟩
  have hzfr : z ∉ p.boundary ℝ := by
    rw [← hU.2.2.2, frontier, hU.1.interior_eq]
    exact fun h => h.2 hz
  by_contra! h
  have hdisjoint : Disjoint C (p.boundary ℝ) := by
    apply Set.disjoint_left.mpr
    rintro w ⟨t, ht, rfl⟩ hw
    change 0 ≤ t at ht
    rcases eq_or_lt_of_le ht with ht | ht
    · exact hzfr (by simpa [← ht] using hw)
    · exact h t ht hw
  rcases subset_or_disjoint_of_avoids_boundary hU hC hdisjoint with hCU | hCU
  · obtain ⟨M, hM⟩ := (y.lipschitzWith.isBounded_image hU.2.2.1).bddAbove
    let t := max (0 : ℝ) (M - y z) + 1
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hM' := hM (show y (z + t • d) ∈ y '' U from
      ⟨z + t • d, hCU ⟨t, ht, rfl⟩, rfl⟩)
    simp only [map_add, map_smul, hd, smul_eq_mul, mul_one] at hM'
    have htM : M - y z < t := by dsimp [t]; linarith [le_max_right (0 : ℝ) (M - y z)]
    linarith
  · exact Set.disjoint_left.mp hCU hzC hz

omit [Fact (Module.finrank ℝ V = 2)] in
/-- There are genuine boundary intersections both below and above every
point of the domain on its vertical line. -/
theorem exists_boundary_below_above {p : Polygon V n} {U : Set V}
    (hU : IsBoundedSide p U) {z : V} (hz : z ∈ U)
    (x y : V →L[ℝ] ℝ) (d : V) (hxd : x d = 0) (hyd : y d = 1) :
    (∃ w ∈ p.boundary ℝ, x w = x z ∧ y w < y z) ∧
      (∃ w ∈ p.boundary ℝ, x w = x z ∧ y z < y w) := by
  obtain ⟨t, ht, htb⟩ := exists_boundary_on_ray hU hz y d hyd
  obtain ⟨s, hs, hsb⟩ := exists_boundary_on_ray hU hz (-y) (-d) (by simp [hyd])
  constructor
  · refine ⟨z + s • (-d), hsb, ?_, ?_⟩
    · simp [hxd]
    · simp only [map_add, map_smul, map_neg, hyd, smul_eq_mul, mul_neg, mul_one]
      linarith
  · refine ⟨z + t • d, htb, ?_, ?_⟩
    · simp [hxd]
    · simp [hyd, ht]

/-- Every point of the bounded domain in a vertex-free strip lies in an
actual adjacent-edge strip cell contained in that domain. -/
theorem exists_adjacent_stripBand_containing (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i))
    {U : Set V} (hU : IsBoundedSide p U) {a b : ℝ}
    (hvertices : ∀ k : Fin n, x (p k) ∉ Ioo a b)
    {z : V} (hz : z ∈ U) (hs : x z ∈ Ioo a b) :
    ∃ i j : Fin n,
      (∀ s ∈ Ioo a b, s ∈ uIoo (x (p i)) (x (p (finRotate n i)))) ∧
      (∀ s ∈ Ioo a b, s ∈ uIoo (x (p j)) (x (p (finRotate n j)))) ∧
      (∀ s ∈ Ioo a b, ∀ k : Fin n,
        s ∈ uIoo (x (p k)) (x (p (finRotate n k))) →
        edgeHeight x y p k s ≤ edgeHeight x y p i s ∨
          edgeHeight x y p j s ≤ edgeHeight x y p k s) ∧
      z ∈ stripBand x y a b (edgeHeight x y p i) (edgeHeight x y p j) ∧
      stripBand x y a b (edgeHeight x y p i) (edgeHeight x y p j) ⊆ U := by
  classical
  obtain ⟨d, hxd, hyd⟩ := exists_verticalDirection x y hxy
  obtain ⟨hbelow, habove⟩ := exists_boundary_below_above hU hz x y d hxd hyd
  let active : Fin n → Prop := fun k =>
    x z ∈ uIoo (x (p k)) (x (p (finRotate n k)))
  let lower : Finset (Fin n) := Finset.univ.filter fun k =>
    active k ∧ edgeHeight x y p k (x z) < y z
  let upper : Finset (Fin n) := Finset.univ.filter fun k =>
    active k ∧ y z < edgeHeight x y p k (x z)
  have hboundary_height {w : V} (hw : w ∈ p.boundary ℝ) (hwx : x w = x z) :
      ∃ k : Fin n, active k ∧ edgeHeight x y p k (x z) = y w := by
    obtain ⟨k, hk⟩ := mem_iUnion.mp hw
    refine ⟨k, ?_, ?_⟩
    · dsimp [active]
      rw [← hwx]
      exact coordinate_mem_uIoo_of_mem_edgeSet x p hx hvertices (hwx ▸ hs) k hk
    · rw [edgeHeight_eq, ← hwx, edgeAtCoordinate_eq_of_mem_edgeSet x p k (hx k) hk]
  have hlower : lower.Nonempty := by
    obtain ⟨w, hw, hwx, hwy⟩ := hbelow
    obtain ⟨k, hk, hkeq⟩ := hboundary_height hw hwx
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hkeq ▸ hwy⟩⟩
  have hupper : upper.Nonempty := by
    obtain ⟨w, hw, hwx, hwy⟩ := habove
    obtain ⟨k, hk, hkeq⟩ := hboundary_height hw hwx
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hkeq ▸ hwy⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image lower
    (fun k => edgeHeight x y p k (x z)) hlower
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image upper
    (fun k => edgeHeight x y p k (x z)) hupper
  have hi' : active i ∧ edgeHeight x y p i (x z) < y z :=
    (Finset.mem_filter.mp hi).2
  have hj' : active j ∧ y z < edgeHeight x y p j (x z) :=
    (Finset.mem_filter.mp hj).2
  have hzboundary : z ∉ p.boundary ℝ := by
    rw [← hU.2.2.2, frontier, hU.1.interior_eq]
    exact fun h => h.2 hz
  have hne (k : Fin n) (hk : active k) : edgeHeight x y p k (x z) ≠ y z := by
    intro heq
    have heqz : edgeAtCoordinate x p k (x z) = z := by
      apply hxy
      apply Prod.ext
      · exact projection_edgeAtCoordinate x p k (hx k) (x z)
      · exact (edgeHeight_eq x y p k (x z)).symm.trans heq
    apply hzboundary
    exact mem_iUnion.mpr ⟨k, heqz ▸ edgeAtCoordinate_mem_edgeSet x p k hk⟩
  have hgap : ∀ k : Fin n, active k →
      edgeHeight x y p k (x z) ≤ edgeHeight x y p i (x z) ∨
        edgeHeight x y p j (x z) ≤ edgeHeight x y p k (x z) := by
    intro k hk
    rcases lt_or_gt_of_ne (hne k hk) with hlt | hgt
    · exact Or.inl (hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hlt⟩))
    · exact Or.inr (hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hgt⟩))
  have hzband : z ∈ stripBand x y a b (edgeHeight x y p i) (edgeHeight x y p j) :=
    ⟨hs, hi'.2, hj'.2⟩
  refine ⟨i, j, edgeActive_on_strip x p hvertices i hs hi'.1,
    edgeActive_on_strip x p hvertices j hs hj'.1,
    stripGap_on_strip x y hxy hp hx hvertices hs hi'.1 hj'.1 hgap, hzband, ?_⟩
  rcases adjacent_stripBand_subset_or_disjoint x y hxy hp hx hU hvertices
      hs hi'.1 hj'.1 hgap with hsub | hdisjoint
  · exact hsub
  · exact False.elim (Set.disjoint_left.mp hdisjoint hzband hz)

omit [Fact (Module.finrank ℝ V = 2)] in
/-- In a vertex-free strip, two genuine adjacent-edge cells meeting at a
point have the same lower and upper edge. -/
theorem adjacent_stripBand_pair_unique (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i))
    {a b : ℝ} {i j k l : Fin n}
    (hi : Ioo a b ⊆ uIoo (x (p i)) (x (p (finRotate n i))))
    (hj : Ioo a b ⊆ uIoo (x (p j)) (x (p (finRotate n j))))
    (hk : Ioo a b ⊆ uIoo (x (p k)) (x (p (finRotate n k))))
    (hl : Ioo a b ⊆ uIoo (x (p l)) (x (p (finRotate n l))))
    (hgapij : ∀ s ∈ Ioo a b, ∀ r : Fin n,
      s ∈ uIoo (x (p r)) (x (p (finRotate n r))) →
      edgeHeight x y p r s ≤ edgeHeight x y p i s ∨
        edgeHeight x y p j s ≤ edgeHeight x y p r s)
    (hgapkl : ∀ s ∈ Ioo a b, ∀ r : Fin n,
      s ∈ uIoo (x (p r)) (x (p (finRotate n r))) →
      edgeHeight x y p r s ≤ edgeHeight x y p k s ∨
        edgeHeight x y p l s ≤ edgeHeight x y p r s)
    {z : V}
    (hzij : z ∈ stripBand x y a b (edgeHeight x y p i) (edgeHeight x y p j))
    (hzkl : z ∈ stripBand x y a b (edgeHeight x y p k) (edgeHeight x y p l)) :
    i = k ∧ j = l := by
  have hs := hzij.1
  have hki : edgeHeight x y p k (x z) ≤ edgeHeight x y p i (x z) := by
    rcases hgapij (x z) hs k (hk hs) with h | h
    · exact h
    · linarith [hzij.2.2, hzkl.2.1]
  have hik : edgeHeight x y p i (x z) ≤ edgeHeight x y p k (x z) := by
    rcases hgapkl (x z) hs i (hi hs) with h | h
    · exact h
    · linarith [hzij.2.1, hzkl.2.2]
  have hjl : edgeHeight x y p j (x z) ≤ edgeHeight x y p l (x z) := by
    rcases hgapij (x z) hs l (hl hs) with h | h
    · linarith [hzij.2.1, hzkl.2.2]
    · exact h
  have hlj : edgeHeight x y p l (x z) ≤ edgeHeight x y p j (x z) := by
    rcases hgapkl (x z) hs j (hj hs) with h | h
    · linarith [hzij.2.2, hzkl.2.1]
    · exact h
  constructor
  · by_contra hne
    exact edgeHeight_ne x y hxy hp hne (hx i) (hx k) (hi hs) (hk hs)
      (le_antisymm hik hki)
  · by_contra hne
    exact edgeHeight_ne x y hxy hp hne (hx j) (hx l) (hj hs) (hl hs)
      (le_antisymm hjl hlj)

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Distinct adjacent-edge cells have disjoint interiors. -/
theorem disjoint_adjacent_stripBands (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i))
    {a b : ℝ} {i j k l : Fin n}
    (hi : Ioo a b ⊆ uIoo (x (p i)) (x (p (finRotate n i))))
    (hj : Ioo a b ⊆ uIoo (x (p j)) (x (p (finRotate n j))))
    (hk : Ioo a b ⊆ uIoo (x (p k)) (x (p (finRotate n k))))
    (hl : Ioo a b ⊆ uIoo (x (p l)) (x (p (finRotate n l))))
    (hgapij : ∀ s ∈ Ioo a b, ∀ r : Fin n,
      s ∈ uIoo (x (p r)) (x (p (finRotate n r))) →
      edgeHeight x y p r s ≤ edgeHeight x y p i s ∨
        edgeHeight x y p j s ≤ edgeHeight x y p r s)
    (hgapkl : ∀ s ∈ Ioo a b, ∀ r : Fin n,
      s ∈ uIoo (x (p r)) (x (p (finRotate n r))) →
      edgeHeight x y p r s ≤ edgeHeight x y p k s ∨
        edgeHeight x y p l s ≤ edgeHeight x y p r s)

    (hne : (i, j) ≠ (k, l)) :
    Disjoint (stripBand x y a b (edgeHeight x y p i) (edgeHeight x y p j))
      (stripBand x y a b (edgeHeight x y p k) (edgeHeight x y p l)) := by
  apply Set.disjoint_left.mpr
  intro z hzij hzkl
  obtain ⟨hik, hjl⟩ := adjacent_stripBand_pair_unique x y hxy hp hx
    hi hj hk hl hgapij hgapkl hzij hzkl
  exact hne (Prod.ext hik hjl)


omit [Fact (Module.finrank ℝ V = 2)] in
/-- Every nonempty strip cell has the expected closed trapezoidal region
as its closure, allowing equality of its two boundary heights at a cut. -/
theorem closure_stripBand (x y : V →L[ℝ] ℝ) (a b : ℝ)
    (lower upper : ℝ →ᵃ[ℝ] ℝ)
    (hne : (stripBand x y a b lower upper).Nonempty) :
    closure (stripBand x y a b lower upper) =
      {z | x z ∈ Icc a b ∧ lower (x z) ≤ y z ∧ y z ≤ upper (x z)} := by
  have hclosed : IsClosed {z | x z ∈ Icc a b ∧ lower (x z) ≤ y z ∧
      y z ≤ upper (x z)} :=
    (isClosed_Icc.preimage x.continuous).inter
      ((isClosed_le (lower.continuous_of_finiteDimensional.comp x.continuous)
        y.continuous).inter
      (isClosed_le y.continuous (upper.continuous_of_finiteDimensional.comp x.continuous)))
  apply Subset.antisymm
  · apply closure_minimal ?_ hclosed
    intro z hz
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩
  · intro w hw
    obtain ⟨z, hz⟩ := hne
    have hseg : openSegment ℝ w z ⊆ stripBand x y a b lower upper := by
      rw [openSegment_eq_image_lineMap]
      rintro v ⟨t, ht, rfl⟩
      have hxl : x (AffineMap.lineMap w z t) = AffineMap.lineMap (x w) (x z) t :=
        x.toLinearMap.toAffineMap.apply_lineMap w z t
      have hyl : y (AffineMap.lineMap w z t) = AffineMap.lineMap (y w) (y z) t :=
        y.toLinearMap.toAffineMap.apply_lineMap w z t
      change x (AffineMap.lineMap w z t) ∈ Ioo a b ∧
        lower (x (AffineMap.lineMap w z t)) < y (AffineMap.lineMap w z t) ∧
        y (AffineMap.lineMap w z t) < upper (x (AffineMap.lineMap w z t))
      rw [hxl, hyl, lower.apply_lineMap, upper.apply_lineMap]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · calc
          a = AffineMap.lineMap a a t := (AffineMap.lineMap_same_apply a t).symm
          _ ≤ AffineMap.lineMap (x w) a t := lineMap_mono_left hw.1.1 ht.2.le
          _ < AffineMap.lineMap (x w) (x z) t :=
            lineMap_strict_mono_right hz.1.1 ht.1
      · calc
          AffineMap.lineMap (x w) (x z) t ≤ AffineMap.lineMap b (x z) t :=
            lineMap_mono_left hw.1.2 ht.2.le
          _ < AffineMap.lineMap b b t :=
            lineMap_strict_mono_right hz.1.2 ht.1
          _ = b := AffineMap.lineMap_same_apply b t
      · exact (lineMap_mono_left hw.2.1 ht.2.le).trans_lt
          (lineMap_strict_mono_right hz.2.1 ht.1)
      · exact (lineMap_mono_left hw.2.2 ht.2.le).trans_lt
          (lineMap_strict_mono_right hz.2.2 ht.1)
    exact closure_mono hseg (segment_subset_closure_openSegment (left_mem_segment ℝ w z))

/-- The boundary of a nonempty strip cell is carried by its two cut
lines and its two affine edge graphs. -/
theorem frontier_stripBand_subset (x y : V →L[ℝ] ℝ) (a b : ℝ)
    (lower upper : ℝ →ᵃ[ℝ] ℝ)
    (hne : (stripBand x y a b lower upper).Nonempty) :
    frontier (stripBand x y a b lower upper) ⊆
      {z | x z = a ∨ x z = b ∨ lower (x z) = y z ∨ y z = upper (x z)} := by
  intro z hz
  rw [frontier, (isOpen_stripBand x y a b lower upper).interior_eq,
    closure_stripBand x y a b lower upper hne] at hz
  by_contra h
  simp only [mem_ofPred_eq, not_or] at h
  apply hz.2
  exact ⟨⟨hz.1.1.1.lt_of_ne (Ne.symm h.1), hz.1.1.2.lt_of_ne h.2.1⟩,
    hz.1.2.1.lt_of_ne h.2.2.1, hz.1.2.2.lt_of_ne h.2.2.2⟩

/-- Actual plane coordinates make every closed strip cell compact. -/
theorem isCompact_closure_stripBand
    (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    (a b : ℝ) (lower upper : ℝ →ᵃ[ℝ] ℝ) :
    IsCompact (closure (stripBand x y a b lower upper)) := by
  let : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by
    rw [Fact.out (p := Module.finrank ℝ V = 2)]
    norm_num)
  by_cases hne : (stripBand x y a b lower upper).Nonempty
  · rw [closure_stripBand x y a b lower upper hne]
    obtain ⟨L, hL⟩ := (isCompact_Icc.image lower.continuous_of_finiteDimensional).bddBelow
    obtain ⟨H, hH⟩ := (isCompact_Icc.image upper.continuous_of_finiteDimensional).bddAbove
    let f := x.toLinearMap.prod y.toLinearMap
    let e := (LinearEquiv.ofInjectiveOfFinrankEq f hxy (by
      simp [Module.finrank_prod, Fact.out (p := Module.finrank ℝ V = 2)])).toContinuousLinearEquiv
    have hcompact : IsCompact (e ⁻¹' (Icc a b ×ˢ Icc L H)) :=
      e.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)
    apply hcompact.of_isClosed_subset
    · exact (isClosed_Icc.preimage x.continuous).inter
        ((isClosed_le (lower.continuous_of_finiteDimensional.comp x.continuous)
          y.continuous).inter
        (isClosed_le y.continuous (upper.continuous_of_finiteDimensional.comp x.continuous)))
    · intro z hz
      change x z ∈ Icc a b ∧ y z ∈ Icc L H
      exact ⟨hz.1, (hL ⟨x z, hz.1, rfl⟩).trans hz.2.1,
        hz.2.2.trans (hH ⟨x z, hz.1, rfl⟩)⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, closure_empty]
    exact isCompact_empty

/-- A cell with ordered boundary heights at its two cuts is the convex
hull of its four actual corner points. Coincident corners are permitted. -/
theorem closure_stripBand_eq_convexHull (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    (a b : ℝ) (lower upper : ℝ →ᵃ[ℝ] ℝ)
    (hne : (stripBand x y a b lower upper).Nonempty)
    (A B C D : V)
    (hA : x A = a ∧ y A = lower a) (hB : x B = b ∧ y B = lower b)
    (hC : x C = a ∧ y C = upper a) (hD : x D = b ∧ y D = upper b)
    (ha : lower a ≤ upper a) (hb : lower b ≤ upper b) :
    closure (stripBand x y a b lower upper) = convexHull ℝ {A, B, C, D} := by
  obtain ⟨z, hz⟩ := hne
  have hab : a ≤ b := hz.1.1.le.trans hz.1.2.le
  have hclosure := closure_stripBand x y a b lower upper ⟨z, hz⟩
  have hcorners : {A, B, C, D} ⊆ closure (stripBand x y a b lower upper) := by
    rw [hclosure]
    intro w hw
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · simpa only [mem_ofPred_eq, hA.1, hA.2, left_mem_Icc.mpr hab, true_and, le_refl] using ha
    · simpa only [mem_ofPred_eq, hB.1, hB.2, right_mem_Icc.mpr hab, true_and, le_refl] using hb
    · simpa only [mem_ofPred_eq, hC.1, hC.2, left_mem_Icc.mpr hab, true_and, le_refl, and_true] using ha
    · simpa only [mem_ofPred_eq, hD.1, hD.2, right_mem_Icc.mpr hab, true_and, le_refl, and_true] using hb
  apply Subset.antisymm
  · intro w hw
    rw [hclosure] at hw
    have hxseg : x w ∈ segment ℝ a b := (segment_eq_Icc hab).symm ▸ hw.1
    rw [segment_eq_image_lineMap] at hxseg
    obtain ⟨t, ht, htx⟩ := hxseg
    have hyseg : y w ∈ segment ℝ (lower (x w)) (upper (x w)) :=
      (segment_eq_Icc (hw.2.1.trans hw.2.2)).symm ▸ hw.2
    rw [segment_eq_image_lineMap] at hyseg
    obtain ⟨r, hr, hry⟩ := hyseg
    have hpoint : AffineMap.lineMap (AffineMap.lineMap A B t)
        (AffineMap.lineMap C D t) r = w := by
      apply hxy
      apply Prod.ext
      · change x.toLinearMap.toAffineMap _ = x w
        simp only [AffineMap.apply_lineMap]
        change AffineMap.lineMap (AffineMap.lineMap (x A) (x B) t)
          (AffineMap.lineMap (x C) (x D) t) r = x w
        rw [hA.1, hB.1, hC.1, hD.1, AffineMap.lineMap_same_apply]
        exact htx
      · change y.toLinearMap.toAffineMap _ = y w
        simp only [AffineMap.apply_lineMap]
        change AffineMap.lineMap (AffineMap.lineMap (y A) (y B) t)
          (AffineMap.lineMap (y C) (y D) t) r = y w
        rw [hA.2, hB.2, hC.2, hD.2,
          ← lower.apply_lineMap, ← upper.apply_lineMap, htx]
        exact hry
    rw [← hpoint]
    apply (convex_convexHull ℝ _).lineMap_mem _ _ hr
    · exact (convex_convexHull ℝ _).lineMap_mem
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) ht
    · exact (convex_convexHull ℝ _).lineMap_mem
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) ht
  · exact convexHull_min hcorners (convex_stripBand x y a b lower upper).closure


omit [Fact (Module.finrank ℝ V = 2)] in
/-- A point on a closed segment divides it into two closed segments,
including either endpoint and all degenerate cases. -/
theorem segment_eq_union_of_mem_segment {B C P : V} (hP : P ∈ segment ℝ B C) :
    segment ℝ B C = segment ℝ B P ∪ segment ℝ P C := by
  rw [segment_eq_image_lineMap] at hP
  obtain ⟨t, ht, rfl⟩ := hP
  have hs : segment ℝ (0 : ℝ) 1 = segment ℝ 0 t ∪ segment ℝ t 1 := by
    rw [segment_eq_Icc (zero_le_one : (0 : ℝ) ≤ 1), segment_eq_Icc ht.1,
      segment_eq_Icc ht.2, Icc_union_Icc_eq_Icc ht.1 ht.2]
  have h := congrArg (fun s : Set ℝ => (AffineMap.lineMap B C : ℝ →ᵃ[ℝ] V) '' s) hs
  simpa only [image_union, image_segment, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using h

/-- Splitting one side of a triangle and joining its split point to the
opposite vertex gives an exact union of the two smaller triangles.  No
nondegeneracy or affine independence is required. -/
theorem triangle_convexHull_split {A B C P : V} (hP : P ∈ segment ℝ B C) :
    convexHull ℝ ({A, B, C} : Set V) =
      convexHull ℝ ({A, B, P} : Set V) ∪ convexHull ℝ ({A, P, C} : Set V) := by
  rw [← convexJoin_singleton_segment, segment_eq_union_of_mem_segment hP,
    convexJoin_union_right, convexJoin_singleton_segment, convexJoin_singleton_segment]

/-- A finite monotone chain covers its endpoint interval by the intervals
between successive entries. -/
theorem Icc_eq_iUnion_adjacent {m : ℕ} (t : Fin (m + 2) → ℝ) (ht : Monotone t) :
    Icc (t 0) (t (Fin.last (m + 1))) =
      ⋃ i : Fin (m + 1), Icc (t i.castSucc) (t i.succ) := by
  induction m with
  | zero =>
    ext z
    simp only [mem_iUnion]
    constructor
    · exact fun hz => ⟨0, hz⟩
    · rintro ⟨i, hi⟩
      have hi0 : i = 0 := Fin.eq_zero i
      subst i
      exact hi
  | succ m ih =>
    let t' : Fin (m + 2) → ℝ := fun i => t i.castSucc
    have ht' : Monotone t' := ht.comp Fin.strictMono_castSucc.monotone
    have hh := ih t' ht'
    have hsplit := Icc_union_Icc_eq_Icc
      (ht (Fin.zero_le (Fin.last (m + 1)).castSucc))
      (ht (Fin.castSucc_le_succ (Fin.last (m + 1))))
    simp only [Fin.succ_last] at hsplit
    rw [← hsplit]
    rw [iUnion_fin_add_one_eq_iUnion_castSucc]
    simpa only [t', Function.comp_def, Fin.succ_castSucc, Fin.castSucc_zero, Fin.succ_last] using
      congrArg (fun s : Set ℝ => s ∪ Icc
        (t (Fin.last (m + 1)).castSucc) (t (Fin.last (m + 2)))) hh

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Subdivide a triangle's base by any finite monotone parameter sequence
including both endpoints, then join the apex to successive base points.
This is an exact cover by actual smaller triangles; degeneracies are allowed. -/
theorem triangle_convexHull_eq_iUnion_base_subdivision {m : ℕ}
    (A B C : V) (d : Fin (m + 1) → V) (t : Fin (m + 1) → ℝ)
    (hd : ∀ i, d i = AffineMap.lineMap B C (t i))
    (ht : Monotone t) (ht0 : t 0 = 0) (ht1 : t (Fin.last m) = 1) :
    convexHull ℝ ({A, B, C} : Set V) =
      ⋃ i : Fin m, convexHull ℝ ({A, d i.castSucc, d i.succ} : Set V) := by
  cases m with
  | zero =>
    have h : (0 : ℝ) = 1 := ht0.symm.trans ht1
    exact (zero_ne_one h).elim
  | succ m =>
    have hinterval : Icc (0 : ℝ) 1 =
        ⋃ i : Fin (m + 1), Icc (t i.castSucc) (t i.succ) := by
      simpa only [ht0, ht1] using Icc_eq_iUnion_adjacent t ht
    have hsegments : segment ℝ B C =
        ⋃ i : Fin (m + 1), segment ℝ (d i.castSucc) (d i.succ) := by
      rw [segment_eq_image_lineMap, hinterval, image_iUnion]
      apply iUnion_congr
      intro i
      rw [← segment_eq_Icc (ht (Fin.castSucc_le_succ i)), image_segment,
        ← hd i.castSucc, ← hd i.succ]
    rw [← convexJoin_singleton_segment, hsegments, convexJoin_iUnion_right]
    simp only [convexJoin_singleton_segment]


/-- A closed strip cell splits along one straight diagonal into two
closed triangle hulls. Either triangle is allowed to degenerate. -/
theorem closure_stripBand_eq_union_triangle_hulls (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    (a b : ℝ) (lower upper : ℝ →ᵃ[ℝ] ℝ)
    (hne : (stripBand x y a b lower upper).Nonempty)
    (A B C D : V)
    (hA : x A = a ∧ y A = lower a) (hB : x B = b ∧ y B = lower b)
    (hC : x C = a ∧ y C = upper a) (hD : x D = b ∧ y D = upper b)
    (ha : lower a ≤ upper a) (hb : lower b ≤ upper b) :
    closure (stripBand x y a b lower upper) =
      convexHull ℝ {A, B, D} ∪ convexHull ℝ {A, C, D} := by
  obtain ⟨z, hz⟩ := hne
  have hab : a ≤ b := hz.1.1.le.trans hz.1.2.le
  have hclosure := closure_stripBand x y a b lower upper ⟨z, hz⟩
  have hhull := closure_stripBand_eq_convexHull x y hxy a b lower upper
    ⟨z, hz⟩ A B C D hA hB hC hD ha hb
  have hxline (P Q : V) (t : ℝ) :
      x (AffineMap.lineMap P Q t) = AffineMap.lineMap (x P) (x Q) t :=
    x.toLinearMap.toAffineMap.apply_lineMap P Q t
  have hyline (P Q : V) (t : ℝ) :
      y (AffineMap.lineMap P Q t) = AffineMap.lineMap (y P) (y Q) t :=
    y.toLinearMap.toAffineMap.apply_lineMap P Q t
  apply Subset.antisymm
  · intro w hw
    rw [hclosure] at hw
    have hxseg : x w ∈ segment ℝ a b := (segment_eq_Icc hab).symm ▸ hw.1
    rw [segment_eq_image_lineMap] at hxseg
    obtain ⟨t, ht, htx⟩ := hxseg
    let L := AffineMap.lineMap A B t
    let E := AffineMap.lineMap A D t
    let R := AffineMap.lineMap C D t
    have hL : x L = x w ∧ y L = lower (x w) := by
      constructor
      · dsimp [L]
        rw [hxline, hA.1, hB.1]
        exact htx
      · dsimp [L]
        rw [hyline, hA.2, hB.2, ← lower.apply_lineMap, htx]
    have hE : x E = x w := by
      dsimp [E]
      rw [hxline, hA.1, hD.1]
      exact htx
    have hR : x R = x w ∧ y R = upper (x w) := by
      constructor
      · dsimp [R]
        rw [hxline, hC.1, hD.1]
        exact htx
      · dsimp [R]
        rw [hyline, hC.2, hD.2, ← upper.apply_lineMap, htx]
    by_cases hside : y w ≤ y E
    · left
      have hyseg : y w ∈ segment ℝ (y L) (y E) := by
        rw [segment_eq_Icc (by rw [hL.2]; exact hw.2.1.trans hside)]
        exact ⟨hL.2 ▸ hw.2.1, hside⟩
      rw [segment_eq_image_lineMap] at hyseg
      obtain ⟨r, hr, hry⟩ := hyseg
      have heq : AffineMap.lineMap L E r = w := by
        apply hxy
        apply Prod.ext
        · change x (AffineMap.lineMap L E r) = x w
          rw [hxline, hL.1, hE, AffineMap.lineMap_same_apply]
        · change y (AffineMap.lineMap L E r) = y w
          rw [hyline]
          exact hry
      rw [← heq]
      apply (convex_convexHull ℝ _).lineMap_mem _ _ hr
      · exact (convex_convexHull ℝ _).lineMap_mem
          (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) ht
      · exact (convex_convexHull ℝ _).lineMap_mem
          (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) ht
    · right
      have hside' : y E ≤ y w := le_of_not_ge hside
      have hyseg : y w ∈ segment ℝ (y E) (y R) := by
        rw [segment_eq_Icc (by rw [hR.2]; exact hside'.trans hw.2.2)]
        exact ⟨hside', hR.2 ▸ hw.2.2⟩
      rw [segment_eq_image_lineMap] at hyseg
      obtain ⟨r, hr, hry⟩ := hyseg
      have heq : AffineMap.lineMap E R r = w := by
        apply hxy
        apply Prod.ext
        · change x (AffineMap.lineMap E R r) = x w
          rw [hxline, hE, hR.1, AffineMap.lineMap_same_apply]
        · change y (AffineMap.lineMap E R r) = y w
          rw [hyline]
          exact hry
      rw [← heq]
      apply (convex_convexHull ℝ _).lineMap_mem _ _ hr
      · exact (convex_convexHull ℝ _).lineMap_mem
          (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) ht
      · exact (convex_convexHull ℝ _).lineMap_mem
          (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) ht
  · rw [hhull]
    apply union_subset
    · exact convexHull_mono (by intro w hw; simp_all only [mem_insert_iff, mem_singleton_iff]; tauto)
    · exact convexHull_mono (by intro w hw; simp_all only [mem_insert_iff, mem_singleton_iff]; tauto)


/-- The two local triangles in a strip cell meet exactly in the diagonal,
including when one triangle degenerates to that segment. -/
theorem triangle_hulls_inter_eq_diagonal (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    (a b : ℝ) (lower upper : ℝ →ᵃ[ℝ] ℝ)
    (hne : (stripBand x y a b lower upper).Nonempty)
    (A B C D : V)
    (hA : x A = a ∧ y A = lower a) (hB : x B = b ∧ y B = lower b)
    (hC : x C = a ∧ y C = upper a) (hD : x D = b ∧ y D = upper b)
    (ha : lower a ≤ upper a) (hb : lower b ≤ upper b) :
    convexHull ℝ {A, B, D} ∩ convexHull ℝ {A, C, D} = segment ℝ A D := by
  obtain ⟨z, hz⟩ := hne
  have hab : a < b := hz.1.1.trans hz.1.2
  let X := x.toLinearMap.toAffineMap
  let Y := y.toLinearMap.toAffineMap
  let q : V →ᵃ[ℝ] ℝ := (b - a) • (Y - AffineMap.const ℝ V (y A)) -
    (y D - y A) • (X - AffineMap.const ℝ V a)
  have hq (w : V) : q w = (b - a) * (y w - y A) - (y D - y A) * (x w - a) := by
    simp [q, X, Y]
  have hqA : q A = 0 := by rw [hq, hA.1]; ring
  have hqD : q D = 0 := by rw [hq, hD.1]; ring
  have hqB : q B ≤ 0 := by
    rw [hq, hB.1, hB.2, hD.2]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hab).le (sub_nonpos.mpr hb)]
  have hqC : 0 ≤ q C := by
    rw [hq, hC.1, hC.2, hA.2]
    nlinarith [mul_nonneg (sub_pos.mpr hab).le (sub_nonneg.mpr ha)]
  have hbelow : convexHull ℝ {A, B, D} ⊆ q ⁻¹' Iic 0 := by
    apply convexHull_min ?_ ((convex_Iic (0 : ℝ)).affine_preimage q)
    intro w hw
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact hqA.le
    · exact hqB
    · exact hqD.le
  have habove : convexHull ℝ {A, C, D} ⊆ q ⁻¹' Ici 0 := by
    apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage q)
    intro w hw
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact hqA.ge
    · exact hqC
    · exact hqD.ge
  apply Subset.antisymm
  · intro w hw
    have hqw : q w = 0 := le_antisymm (hbelow hw.1) (habove hw.2)
    have hhull := closure_stripBand_eq_convexHull x y hxy a b lower upper
      ⟨z, hz⟩ A B C D hA hB hC hD ha hb
    have hwclosure : w ∈ closure (stripBand x y a b lower upper) := by
      rw [hhull]
      exact convexHull_mono (by intro v hv; simp_all only [mem_insert_iff, mem_singleton_iff]; tauto) hw.1
    rw [closure_stripBand x y a b lower upper ⟨z, hz⟩] at hwclosure
    have hxseg : x w ∈ segment ℝ a b := (segment_eq_Icc hab.le).symm ▸ hwclosure.1
    rw [segment_eq_image_lineMap] at hxseg
    obtain ⟨t, ht, htx⟩ := hxseg
    have hxline : x (AffineMap.lineMap A D t) = x w := by
      change x.toLinearMap.toAffineMap (AffineMap.lineMap A D t) = x w
      rw [AffineMap.apply_lineMap]
      change AffineMap.lineMap (x A) (x D) t = x w
      rw [hA.1, hD.1]
      exact htx
    have hqline : q (AffineMap.lineMap A D t) = 0 := by
      rw [q.apply_lineMap, hqA, hqD, AffineMap.lineMap_same_apply]
    have heqy : y (AffineMap.lineMap A D t) = y w := by
      have hprod : (b - a) * (y (AffineMap.lineMap A D t) - y w) = 0 := by
        rw [hq, hxline] at hqline
        rw [hq] at hqw
        linear_combination hqline - hqw
      exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hab.ne'))
    have heq : AffineMap.lineMap A D t = w := hxy (Prod.ext hxline heqy)
    exact heq ▸ lineMap_mem_segment ℝ A D ht
  · apply subset_inter
    · exact (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
    · exact (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))


omit [Fact (Module.finrank ℝ V = 2)] in
/-- Strict order of active edge heights extends to weak order at the two
cut lines by continuity. -/
theorem edgeHeight_le_on_closed_strip (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p) {i j : Fin n} (hij : i ≠ j)
    (hxi : x (p (finRotate n i)) ≠ x (p i))
    (hxj : x (p (finRotate n j)) ≠ x (p j))
    {a b : ℝ}
    (hi : Ioo a b ⊆ uIoo (x (p i)) (x (p (finRotate n i))))
    (hj : Ioo a b ⊆ uIoo (x (p j)) (x (p (finRotate n j))))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo a b)
    (hlt : edgeHeight x y p i s₀ < edgeHeight x y p j s₀) :
    ∀ s ∈ Icc a b, edgeHeight x y p i s ≤ edgeHeight x y p j s := by
  have hsub : Ioo a b ⊆ {s | edgeHeight x y p i s ≤ edgeHeight x y p j s} := by
    intro s hs
    exact (show edgeHeight x y p i s < edgeHeight x y p j s by
      simpa only [edgeHeight_eq] using edgeHeight_lt_on_strip x y hxy hp hij
        hxi hxj isPreconnected_Ioo hi hj hs₀
        (by simpa only [edgeHeight_eq] using hlt) s hs).le
  have hclosed : IsClosed {s | edgeHeight x y p i s ≤ edgeHeight x y p j s} :=
    isClosed_le (edgeHeight x y p i).continuous_of_finiteDimensional
      (edgeHeight x y p j).continuous_of_finiteDimensional
  have hc := closure_minimal hsub hclosed
  rw [closure_Ioo (hs₀.1.trans hs₀.2).ne] at hc
  exact hc

/-- The closure of every nonempty actual active-edge cell is a finite
straight convex polygon with at most four vertices, computed on its cut lines. -/
theorem closure_edge_stripBand_eq_convexHull (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p) {i j : Fin n}
    (hxi : x (p (finRotate n i)) ≠ x (p i))
    (hxj : x (p (finRotate n j)) ≠ x (p j))
    {a b : ℝ}
    (hi : Ioo a b ⊆ uIoo (x (p i)) (x (p (finRotate n i))))
    (hj : Ioo a b ⊆ uIoo (x (p j)) (x (p (finRotate n j))))
    (hne : (stripBand x y a b (edgeHeight x y p i) (edgeHeight x y p j)).Nonempty) :
    closure (stripBand x y a b (edgeHeight x y p i) (edgeHeight x y p j)) =
      convexHull ℝ {edgeAtCoordinate x p i a, edgeAtCoordinate x p i b,
        edgeAtCoordinate x p j a, edgeAtCoordinate x p j b} := by
  obtain ⟨z, hz⟩ := hne
  have hij : i ≠ j := by
    intro h
    subst j
    exact (hz.2.1.trans hz.2.2).false
  have horder := edgeHeight_le_on_closed_strip x y hxy hp hij hxi hxj hi hj
    hz.1 (hz.2.1.trans hz.2.2)
  have hab : a ≤ b := hz.1.1.le.trans hz.1.2.le
  apply closure_stripBand_eq_convexHull x y hxy a b _ _ ⟨z, hz⟩
  · exact ⟨projection_edgeAtCoordinate x p i hxi a, (edgeHeight_eq x y p i a).symm⟩
  · exact ⟨projection_edgeAtCoordinate x p i hxi b, (edgeHeight_eq x y p i b).symm⟩
  · exact ⟨projection_edgeAtCoordinate x p j hxj a, (edgeHeight_eq x y p j a).symm⟩
  · exact ⟨projection_edgeAtCoordinate x p j hxj b, (edgeHeight_eq x y p j b).symm⟩
  · exact horder a (left_mem_Icc.mpr hab)
  · exact horder b (right_mem_Icc.mpr hab)


/-- The two actual straight triangles of an active-edge strip cell cover
its closure and meet in exactly their common diagonal. A zero-area triangle
is permitted when one cut side collapses; no global mesh is asserted here. -/
theorem edge_stripBand_triangle_decomposition (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p) {i j : Fin n}
    (hxi : x (p (finRotate n i)) ≠ x (p i))
    (hxj : x (p (finRotate n j)) ≠ x (p j)) {a b : ℝ}
    (hi : Ioo a b ⊆ uIoo (x (p i)) (x (p (finRotate n i))))
    (hj : Ioo a b ⊆ uIoo (x (p j)) (x (p (finRotate n j))))
    (hne : (stripBand x y a b (edgeHeight x y p i) (edgeHeight x y p j)).Nonempty) :
    let A := edgeAtCoordinate x p i a
    let B := edgeAtCoordinate x p i b
    let C := edgeAtCoordinate x p j a
    let D := edgeAtCoordinate x p j b
    (closure (stripBand x y a b (edgeHeight x y p i) (edgeHeight x y p j)) =
      convexHull ℝ {A, B, D} ∪ convexHull ℝ {A, C, D}) ∧
      convexHull ℝ {A, B, D} ∩ convexHull ℝ {A, C, D} = segment ℝ A D := by
  obtain ⟨z, hz⟩ := hne
  have hij : i ≠ j := by
    intro h
    subst j
    exact (hz.2.1.trans hz.2.2).false
  have horder := edgeHeight_le_on_closed_strip x y hxy hp hij hxi hxj hi hj
    hz.1 (hz.2.1.trans hz.2.2)
  have hab : a ≤ b := hz.1.1.le.trans hz.1.2.le
  have hA : x (edgeAtCoordinate x p i a) = a ∧
      y (edgeAtCoordinate x p i a) = edgeHeight x y p i a :=
    ⟨projection_edgeAtCoordinate x p i hxi a, (edgeHeight_eq x y p i a).symm⟩
  have hB : x (edgeAtCoordinate x p i b) = b ∧
      y (edgeAtCoordinate x p i b) = edgeHeight x y p i b :=
    ⟨projection_edgeAtCoordinate x p i hxi b, (edgeHeight_eq x y p i b).symm⟩
  have hC : x (edgeAtCoordinate x p j a) = a ∧
      y (edgeAtCoordinate x p j a) = edgeHeight x y p j a :=
    ⟨projection_edgeAtCoordinate x p j hxj a, (edgeHeight_eq x y p j a).symm⟩
  have hD : x (edgeAtCoordinate x p j b) = b ∧
      y (edgeAtCoordinate x p j b) = edgeHeight x y p j b :=
    ⟨projection_edgeAtCoordinate x p j hxj b, (edgeHeight_eq x y p j b).symm⟩
  exact ⟨closure_stripBand_eq_union_triangle_hulls x y hxy a b _ _ ⟨z, hz⟩
      _ _ _ _ hA hB hC hD (horder a (left_mem_Icc.mpr hab)) (horder b (right_mem_Icc.mpr hab)),
    triangle_hulls_inter_eq_diagonal x y hxy a b _ _ ⟨z, hz⟩
      _ _ _ _ hA hB hC hD (horder a (left_mem_Icc.mpr hab)) (horder b (right_mem_Icc.mpr hab))⟩


omit [Fact (Module.finrank ℝ V = 2)] in
/-- A separating projection has a uniquely minimum vertex. -/
theorem exists_strict_minimum [NeZero n] (p : Polygon V n) (x : V →L[ℝ] ℝ)
    (hx : Function.Injective (x ∘ p.vertices)) :
    ∃ i : Fin n, ∀ j, j ≠ i → x (p i) < x (p j) := by
  obtain ⟨i, hi⟩ := Finite.exists_min (fun j : Fin n => x (p j))
  refine ⟨i, fun j hji => lt_of_le_of_ne (hi j) ?_⟩
  intro he
  exact hji (hx he.symm)

omit [Fact (Module.finrank ℝ V = 2)] in
/-- There is a full positive strip before the next projected vertex. -/
theorem exists_strip_after_strict_minimum (p : Polygon V n) (x : V →L[ℝ] ℝ)
    (i : Fin n) (hi : ∀ j, j ≠ i → x (p i) < x (p j)) :
    ∃ b : ℝ, x (p i) < b ∧ ∀ j, j ≠ i → b < x (p j) := by
  classical
  let T : Finset ℝ := (Finset.univ.erase i).image (fun j => x (p j))
  obtain ⟨b, hb, hbT⟩ := Finset.exists_between' {x (p i)} T (by
    intro a ha c hc
    simp only [Finset.mem_singleton] at ha
    subst a
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    exact hi j (Finset.mem_erase.mp hj).1)
  refine ⟨b, hb _ (by simp), fun j hji => ?_⟩
  apply hbT
  exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩, rfl⟩

omit [Fact (Module.finrank ℝ V = 2)] in
/-- In the first strip after a uniquely leftmost vertex, exactly its two
incident directed edges are active. This requires no triangulation. -/
theorem nearMinimum_activeEdge_iff (p : Polygon V n) (x : V →L[ℝ] ℝ)
    (he : p.HasNondegenerateEdges) (i : Fin n) {s : ℝ}
    (hs : x (p i) < s) (hothers : ∀ j, j ≠ i → s < x (p j)) (j : Fin n) :
    s ∈ uIoo (x (p j)) (x (p (finRotate n j))) ↔
      j = i ∨ j = (finRotate n).symm i := by
  have hout : finRotate n i ≠ i := fun h => he i (congrArg p h.symm)
  have hin : (finRotate n).symm i ≠ i := by
    intro h
    apply hout
    have := congrArg (finRotate n) h
    simpa only [Equiv.apply_symm_apply] using this.symm
  constructor
  · intro hj
    by_cases hji : j = i
    · exact Or.inl hji
    · right
      by_contra hprev
      have hn : finRotate n j ≠ i := by
        intro hh
        exact hprev ((finRotate n).eq_symm_apply.mpr hh)
      exact (not_lt_of_ge (lt_min (hothers j hji) (hothers _ hn)).le) hj.1
  · rintro (rfl | rfl)
    · exact mem_uIoo_of_lt hs (hothers _ hout)
    · simpa only [Equiv.apply_symm_apply] using
        (mem_uIoo_of_gt hs (hothers _ hin) :
          s ∈ uIoo (x (p ((finRotate n).symm i))) (x (p i)))

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Every boundary point in that first strip lies on one of the two
incident edges. This uses actual closed geometric polygon edges. -/
theorem nearMinimum_boundary_mem_incident (p : Polygon V n) (x : V →L[ℝ] ℝ)
    (i : Fin n) {z : V} (hz : z ∈ p.boundary ℝ)
    (_hs : x (p i) < x z) (hothers : ∀ j, j ≠ i → x z < x (p j)) :
    z ∈ p.edgeSet ℝ i ∨ z ∈ p.edgeSet ℝ ((finRotate n).symm i) := by
  rcases mem_iUnion.mp hz with ⟨j, hj⟩
  by_cases hji : j = i
  · exact Or.inl (hji ▸ hj)
  right
  have hnext : finRotate n j = i := by
    by_contra hn
    have hseg : x z ∈ uIcc (x (p j)) (x (p (finRotate n j))) := by
      have hj' : z ∈ segment ℝ (p j) (p (finRotate n j)) := by
        simpa only [Polygon.edgeSet, affineSegment_eq_segment] using hj
      rw [← segment_eq_uIcc]
      change x.toLinearMap.toAffineMap z ∈ segment ℝ
        (x.toLinearMap.toAffineMap (p j)) (x.toLinearMap.toAffineMap (p (finRotate n j)))
      rw [← image_segment]
      exact ⟨z, hj', rfl⟩
    exact (not_lt_of_ge hseg.1) (lt_min (hothers j hji) (hothers _ hn))
  have hjprev : j = (finRotate n).symm i :=
    (finRotate n).eq_symm_apply.mpr hnext
  exact hjprev ▸ hj

omit [Fact (Module.finrank ℝ V = 2)] in
/-- A linear coordinate bounded below at every polygon vertex is bounded
below on the actual polygon boundary. -/
theorem boundary_coordinate_lower_bound (x : V →L[ℝ] ℝ) (p : Polygon V n)
    {a : ℝ} (ha : ∀ i, a ≤ x (p i)) {w : V} (hw : w ∈ p.boundary ℝ) :
    a ≤ x w := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hw
  have hc : Convex ℝ {z : V | a ≤ x z} := (convex_Ici a).linear_preimage x.toLinearMap
  have hh := hc.segment_subset (ha i) (ha (finRotate n i))
  exact hh (by simpa only [Polygon.edgeSet, affineSegment_eq_segment] using hi)

/-- The corresponding coordinate upper bound, using the same straight edges. -/
theorem boundary_coordinate_upper_bound (x : V →L[ℝ] ℝ) (p : Polygon V n)
    {a : ℝ} (ha : ∀ i, x (p i) ≤ a) {w : V} (hw : w ∈ p.boundary ℝ) :
    x w ≤ a := by
  have h := boundary_coordinate_lower_bound (-x) p (a := -a) (by simpa using ha) hw
  simpa using h

/-- Every interior point avoiding the vertex cut lines lies between a
consecutive pair of actual vertex coordinates. Boundedness of the domain
rules out the two exterior strips. -/
theorem exists_adjacent_vertex_strip (x : V →L[ℝ] ℝ)
    (hx : Function.Surjective x) (p : Polygon V n) {U : Set V}
    (hU : IsBoundedSide p U) {z : V} (hz : z ∈ U)
    (hzcut : ∀ i : Fin n, x z ≠ x (p i)) :
    ∃ l r : Fin n, x z ∈ Ioo (x (p l)) (x (p r)) ∧
      ∀ k : Fin n, x (p k) ∉ Ioo (x (p l)) (x (p r)) := by
  classical
  obtain ⟨d, hd⟩ := hx 1
  obtain ⟨t, ht, htb⟩ := exists_boundary_on_ray hU hz x d hd
  obtain ⟨s, hs, hsb⟩ := exists_boundary_on_ray hU hz (-x) (-d) (by simp [hd])
  have hlow : ∃ i : Fin n, x (p i) < x z := by
    by_contra! h
    have hbound := boundary_coordinate_lower_bound x p h hsb
    simp only [map_add, map_smul, map_neg, hd, smul_eq_mul, mul_neg, mul_one] at hbound
    linarith
  have hupp : ∃ i : Fin n, x z < x (p i) := by
    by_contra! h
    have hbound := boundary_coordinate_upper_bound x p h htb
    simp only [map_add, map_smul, hd, smul_eq_mul, mul_one] at hbound
    linarith
  let lower : Finset (Fin n) := Finset.univ.filter fun k => x (p k) < x z
  let upper : Finset (Fin n) := Finset.univ.filter fun k => x z < x (p k)
  have hlower : lower.Nonempty := by
    obtain ⟨i, hi⟩ := hlow
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hupper : upper.Nonempty := by
    obtain ⟨i, hi⟩ := hupp
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨l, hl, hmax⟩ := Finset.exists_max_image lower (fun k => x (p k)) hlower
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image upper (fun k => x (p k)) hupper
  have hl' : x (p l) < x z := (Finset.mem_filter.mp hl).2
  have hr' : x z < x (p r) := (Finset.mem_filter.mp hr).2
  refine ⟨l, r, ⟨hl', hr'⟩, ?_⟩
  intro k hk
  rcases lt_or_gt_of_ne (hzcut k).symm with h | h
  · have hm := hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact (not_lt_of_ge hm) hk.1
  · have hm := hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact (not_lt_of_ge hm) hk.2

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Removing the finitely many vertical cut lines leaves a dense set.
Surjectivity is essential: the coordinate is a genuine plane coordinate. -/
theorem dense_nonvertex_coordinates (x : V →L[ℝ] ℝ)
    (hx : Function.Surjective x) (p : Polygon V n) :
    Dense {z : V | ∀ i : Fin n, x z ≠ x (p i)} := by
  have hd : Dense ((Set.range fun i : Fin n => x (p i))ᶜ) := by
    have hd' := dense_univ.sdiff_finite (Set.finite_range fun i : Fin n => x (p i))
    convert hd' using 1
    ext r
    simp only [mem_compl_iff, Set.mem_sdiff, mem_univ, true_and]
  have hh := hd.preimage (x.toLinearMap.isOpenMap_of_finiteDimensional hx)
  convert hh using 1
  ext z
  change (∀ i : Fin n, x z ≠ x (p i)) ↔ ¬∃ i : Fin n, x (p i) = x z
  simp only [not_exists, ne_eq, eq_comm]

/-- The open domain is dense even after omitting all vertex cut lines. -/
theorem closure_domain_without_vertex_lines (x : V →L[ℝ] ℝ)
    (hx : Function.Surjective x) (p : Polygon V n) {U : Set V} (hU : IsOpen U) :
    closure (U ∩ {z : V | ∀ i : Fin n, x z ≠ x (p i)}) = closure U := by
  apply subset_antisymm
  · exact closure_mono inter_subset_left
  · exact closure_minimal ((dense_nonvertex_coordinates x hx p).open_subset_closure_inter hU)
      isClosed_closure


/-- A cell label records its two cut vertices and two bounding polygon edges. -/
abbrev StripCellLabel (n : ℕ) := (Fin n × Fin n) × (Fin n × Fin n)

/-- The actual open cell corresponding to a finite label. -/
def stripCell (x y : V →L[ℝ] ℝ) (p : Polygon V n) (q : StripCellLabel n) : Set V :=
  stripBand x y (x (p q.1.1)) (x (p q.1.2))
    (edgeHeight x y p q.2.1) (edgeHeight x y p q.2.2)

/-- The finite labels of nonempty adjacent-edge strip cells inside the actual
polygonal domain. These are construction data, not inputs to the main theorem. -/
def IsSelectedStripCell (x y : V →L[ℝ] ℝ) (p : Polygon V n) (U : Set V)
    (q : StripCellLabel n) : Prop :=
  x (p q.1.1) < x (p q.1.2) ∧
  (∀ k : Fin n, x (p k) ∉ Ioo (x (p q.1.1)) (x (p q.1.2))) ∧
  (Ioo (x (p q.1.1)) (x (p q.1.2)) ⊆
    uIoo (x (p q.2.1)) (x (p (finRotate n q.2.1)))) ∧
  (Ioo (x (p q.1.1)) (x (p q.1.2)) ⊆
    uIoo (x (p q.2.2)) (x (p (finRotate n q.2.2)))) ∧
  (∀ s ∈ Ioo (x (p q.1.1)) (x (p q.1.2)), ∀ k : Fin n,
    s ∈ uIoo (x (p k)) (x (p (finRotate n k))) →
      edgeHeight x y p k s ≤ edgeHeight x y p q.2.1 s ∨
        edgeHeight x y p q.2.2 s ≤ edgeHeight x y p k s) ∧
  (stripCell x y p q).Nonempty ∧ stripCell x y p q ⊆ U

abbrev SelectedStripCell (x y : V →L[ℝ] ℝ) (p : Polygon V n) (U : Set V) :=
  {q : StripCellLabel n // IsSelectedStripCell x y p U q}

instance (x y : V →L[ℝ] ℝ) (p : Polygon V n) (U : Set V) :
    Finite (SelectedStripCell x y p U) := inferInstanceAs (Finite (Subtype _))

/-- The selected finite cells cover exactly the domain away from the vertex
cut lines, with no triangulation or covering certificate assumed. -/
theorem domain_without_vertex_lines_eq_stripCells
    (x y : V →L[ℝ] ℝ) (hxsurj : Function.Surjective x)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i))
    {U : Set V} (hU : IsBoundedSide p U) :
    U ∩ {z : V | ∀ i : Fin n, x z ≠ x (p i)} =
      ⋃ q : SelectedStripCell x y p U, stripCell x y p q.val := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨l, r, hzr, hvertices⟩ := exists_adjacent_vertex_strip x hxsurj p hU hz.1 hz.2
    obtain ⟨i, j, hi, hj, hgap, hzband, hinside⟩ :=
      exists_adjacent_stripBand_containing x y hxy hp hx hU hvertices hz.1 hzr
    let q : SelectedStripCell x y p U :=
      ⟨((l, r), (i, j)), hzr.1.trans hzr.2, hvertices, hi, hj, hgap, ⟨z, hzband⟩, hinside⟩
    exact mem_iUnion.mpr ⟨q, hzband⟩
  · intro z hz
    obtain ⟨q, hq⟩ := mem_iUnion.mp hz
    refine ⟨q.property.2.2.2.2.2.2 hq, ?_⟩
    intro k heq
    exact q.property.2.1 k (heq ▸ hq.1)

/-- The closures of finitely many genuine convex open cells cover the whole
closed polygonal region, including all cut lines and boundary points. -/
theorem closure_domain_eq_closed_stripCells
    (x y : V →L[ℝ] ℝ) (hxsurj : Function.Surjective x)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i))
    {U : Set V} (hU : IsBoundedSide p U) :
    closure U = ⋃ q : SelectedStripCell x y p U, closure (stripCell x y p q.val) := by
  rw [← closure_domain_without_vertex_lines x hxsurj p hU.1,
    domain_without_vertex_lines_eq_stripCells x y hxsurj hxy hp hx hU,
    closure_iUnion_of_finite]

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Every constructed cell is nonempty, open, convex, and contained in the
original domain. -/
theorem selectedStripCell_geometry (x y : V →L[ℝ] ℝ) (p : Polygon V n) (U : Set V)
    (q : SelectedStripCell x y p U) :
    (stripCell x y p q.val).Nonempty ∧ IsOpen (stripCell x y p q.val) ∧
      Convex ℝ (stripCell x y p q.val) ∧ stripCell x y p q.val ⊆ U := by
  exact ⟨q.property.2.2.2.2.2.1, isOpen_stripBand _ _ _ _ _ _,
    convex_stripBand _ _ _ _ _ _, q.property.2.2.2.2.2.2⟩


omit [Fact (Module.finrank ℝ V = 2)] in
/-- Overlapping strips between consecutive vertex cut lines have identical
endpoints. This uses the actual finite vertex coordinates. -/
theorem adjacent_vertex_strip_unique (x : V →L[ℝ] ℝ) (p : Polygon V n)
    (hx : Function.Injective (x ∘ p.vertices)) {l r l' r' : Fin n}
    (hvertices : ∀ k : Fin n, x (p k) ∉ Ioo (x (p l)) (x (p r)))
    (hvertices' : ∀ k : Fin n, x (p k) ∉ Ioo (x (p l')) (x (p r')))
    {s : ℝ} (hs : s ∈ Ioo (x (p l)) (x (p r)))
    (hs' : s ∈ Ioo (x (p l')) (x (p r'))) : l = l' ∧ r = r' := by
  have hll : x (p l) = x (p l') := by
    apply le_antisymm
    · exact le_of_not_gt (fun h => hvertices' l ⟨h, hs.1.trans hs'.2⟩)
    · exact le_of_not_gt (fun h => hvertices l' ⟨h, hs'.1.trans hs.2⟩)
  have hrr : x (p r) = x (p r') := by
    apply le_antisymm
    · exact le_of_not_gt (fun h => hvertices r' ⟨hs.1.trans hs'.2, h⟩)
    · exact le_of_not_gt (fun h => hvertices' r ⟨hs'.1.trans hs.2, h⟩)
  exact ⟨hx hll, hx hrr⟩

/-- Distinct labels in the constructed decomposition have disjoint open
cells, including labels from different strips. -/
theorem selectedStripCells_pairwise_disjoint (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i))
    (hxvertices : Function.Injective (x ∘ p.vertices)) (U : Set V) :
    Pairwise (fun q r : SelectedStripCell x y p U =>
      Disjoint (stripCell x y p q.val) (stripCell x y p r.val)) := by
  intro q r hne
  apply Set.disjoint_left.mpr
  intro z hzq hzr
  obtain ⟨ql, qr⟩ := adjacent_vertex_strip_unique x p hxvertices
    q.property.2.1 r.property.2.1 hzq.1 hzr.1
  have hpair : q.val.1 = r.val.1 := Prod.ext ql qr
  have hact₁ := r.property.2.2.1
  have hact₂ := r.property.2.2.2.1
  have hgap := r.property.2.2.2.2.1
  have hzr' := hzr
  unfold stripCell at hzr'
  rw [← hpair] at hact₁ hact₂ hgap hzr'
  obtain ⟨qi, qj⟩ := adjacent_stripBand_pair_unique x y hxy hp hx
    q.property.2.2.1 q.property.2.2.2.1 hact₁ hact₂
    q.property.2.2.2.2.1 hgap hzq hzr'
  apply hne
  apply Subtype.ext
  exact Prod.ext hpair (Prod.ext qi qj)

omit [Fact (Module.finrank ℝ V = 2)] in
/-- All edges are nonvertical when the first coordinate separates the
polygon vertices; the input edges remain the actual polygon edges. -/
theorem nonvertical_of_separatingProjection (x : V →L[ℝ] ℝ) {p : Polygon V n}
    (he : p.HasNondegenerateEdges) (hx : Function.Injective (x ∘ p.vertices)) :
    ∀ i, x (p (finRotate n i)) ≠ x (p i) := by
  intro i heq
  have h := congrArg p (hx heq)
  exact he i h.symm

/-- A simple polygonal domain admits a finite decomposition into disjoint
nonempty convex open strip cells, whose closures cover its closed region.
This proves the strip-decomposition stage from the original geometric inputs.
The subsequent compatible triangulation and vertex angle fans remain separate. -/
theorem exists_finite_strip_decomposition
    {p : Polygon V n} (hp : IsSimple p) {U : Set V} (hU : IsBoundedSide p U)
    (o : Orientation ℝ V (Fin 2)) :
    ∃ x y : V →L[ℝ] ℝ,
      Function.Injective (fun z : V => (x z, y z)) ∧
      Function.Injective (x ∘ p.vertices) ∧
      (∀ q : SelectedStripCell x y p U,
        (stripCell x y p q.val).Nonempty ∧ IsOpen (stripCell x y p q.val) ∧
          Convex ℝ (stripCell x y p q.val) ∧ stripCell x y p q.val ⊆ U) ∧
      Pairwise (fun q r : SelectedStripCell x y p U =>
        Disjoint (stripCell x y p q.val) (stripCell x y p r.val)) ∧
      closure U = ⋃ q : SelectedStripCell x y p U, closure (stripCell x y p q.val) := by
  obtain ⟨x, y, hxy, hx⟩ := exists_separatingCoordinates o hp
  have hxedge := nonvertical_of_separatingProjection x hp.2.2.1 hx
  obtain ⟨d, _, hxd⟩ := exists_verticalDirection y x (by
    intro z w h
    exact hxy (Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1))
  have hxsurj : Function.Surjective x := by
    intro a
    exact ⟨a • d, by simp [hxd]⟩
  exact ⟨x, y, hxy, hx, selectedStripCell_geometry x y p U,
    selectedStripCells_pairwise_disjoint x y hxy hp hxedge hx U,
    closure_domain_eq_closed_stripCells x y hxsurj hxy hp hxedge hU⟩


/-- The four actual intersections of the two edge lines with their two cut
lines generate the associated closed straight cell. Repeated corners are allowed. -/
def stripCellHull (x : V →L[ℝ] ℝ) (p : Polygon V n) (q : StripCellLabel n) : Set V :=
  convexHull ℝ {edgeAtCoordinate x p q.2.1 (x (p q.1.1)),
    edgeAtCoordinate x p q.2.1 (x (p q.1.2)),
    edgeAtCoordinate x p q.2.2 (x (p q.1.1)),
    edgeAtCoordinate x p q.2.2 (x (p q.1.2))}

/-- Every selected closed cell is the convex hull of its actual straight
corners. The necessary ordering at the cuts is proved from simplicity. -/
theorem selectedStripCell_closure_eq_hull (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i)) (U : Set V)
    (q : SelectedStripCell x y p U) :
    closure (stripCell x y p q.val) = stripCellHull x p q.val := by
  exact closure_edge_stripBand_eq_convexHull x y hxy hp (hx q.val.2.1) (hx q.val.2.2)
    q.property.2.2.1 q.property.2.2.2.1 q.property.2.2.2.2.2.1

/-- All selected closed cells are compact subsets of the given closed region. -/
theorem selectedStripCell_compact_subset (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    (p : Polygon V n) (U : Set V) (q : SelectedStripCell x y p U) :
    IsCompact (closure (stripCell x y p q.val)) ∧
      closure (stripCell x y p q.val) ⊆ closure U := by
  exact ⟨isCompact_closure_stripBand x y hxy _ _ _ _,
    closure_mono q.property.2.2.2.2.2.2⟩

/-- The complete closed region is a finite union of explicitly straight
convex hulls, with no omitted vertical cut lines or boundary points. -/
theorem closure_domain_eq_stripCell_hulls (x y : V →L[ℝ] ℝ)
    (hxsurj : Function.Surjective x)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i))
    {U : Set V} (hU : IsBoundedSide p U) :
    closure U = ⋃ q : SelectedStripCell x y p U, stripCellHull x p q.val := by
  rw [closure_domain_eq_closed_stripCells x y hxsurj hxy hp hx hU]
  exact iUnion_congr fun q => selectedStripCell_closure_eq_hull x y hxy hp hx U q

/-- Distinct selected open cells meet only on their actual frontiers after
closure. This is a geometric consequence of their disjointness and openness. -/
theorem selectedStripCells_closed_inter_subset_frontiers (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i))
    (hxvertices : Function.Injective (x ∘ p.vertices)) (U : Set V)
    {q r : SelectedStripCell x y p U} (hne : q ≠ r) :
    closure (stripCell x y p q.val) ∩ closure (stripCell x y p r.val) ⊆
      frontier (stripCell x y p q.val) ∩ frontier (stripCell x y p r.val) := by
  have hd := selectedStripCells_pairwise_disjoint x y hxy hp hx hxvertices U hne
  have hq := (selectedStripCell_geometry x y p U q).2.1
  have hr := (selectedStripCell_geometry x y p U r).2.1
  intro z hz
  rw [frontier, hq.interior_eq, frontier, hr.interior_eq]
  refine ⟨⟨hz.1, ?_⟩, ⟨hz.2, ?_⟩⟩
  · intro h
    exact Set.disjoint_left.mp (hd.closure_right hq) h hz.2
  · intro h
    exact Set.disjoint_left.mp (hd.closure_left hr) hz.1 h


/-- Each cell in the constructed finite covering has this proved local
triangle decomposition. Matching the subdivisions of neighboring cut sides
is the remaining global compatibility step. -/
theorem selectedStripCell_triangle_decomposition (x y : V →L[ℝ] ℝ)
    (hxy : Function.Injective (fun z : V => (x z, y z)))
    {p : Polygon V n} (hp : IsSimple p)
    (hx : ∀ i, x (p (finRotate n i)) ≠ x (p i)) (U : Set V)
    (q : SelectedStripCell x y p U) :
    let A := edgeAtCoordinate x p q.val.2.1 (x (p q.val.1.1))
    let B := edgeAtCoordinate x p q.val.2.1 (x (p q.val.1.2))
    let C := edgeAtCoordinate x p q.val.2.2 (x (p q.val.1.1))
    let D := edgeAtCoordinate x p q.val.2.2 (x (p q.val.1.2))
    (closure (stripCell x y p q.val) = convexHull ℝ {A, B, D} ∪ convexHull ℝ {A, C, D}) ∧
      convexHull ℝ {A, B, D} ∩ convexHull ℝ {A, C, D} = segment ℝ A D := by
  exact edge_stripBand_triangle_decomposition x y hxy hp (hx _) (hx _)
    q.property.2.2.1 q.property.2.2.2.1 q.property.2.2.2.2.2.1


/-- For oriented coordinates x=⟪v,·⟫, y=⟪Jv,·⟫, the quarter turn sends
edge coordinates `(x(e),y(e))` to `(-y(e),x(e))`. -/
theorem quarterTurn_inner_coordinates (v e : V) :
    inner ℝ v (o.rightAngleRotation e) = -inner ℝ (o.rightAngleRotation v) e ∧
    inner ℝ (o.rightAngleRotation v) (o.rightAngleRotation e) = inner ℝ v e := by
  exact ⟨o.inner_rightAngleRotation_swap v e, o.inner_comp_rightAngleRotation v e⟩

/-- The height above the supporting edge graph changes under a left normal
translate with coefficient `(x(e)^2+y(e)^2)/x(e)`. -/
theorem normalGraphSlope_identity (v e : V) :
    inner ℝ (o.rightAngleRotation v) (o.rightAngleRotation e) -
      (inner ℝ (o.rightAngleRotation v) e / inner ℝ v e) *
        inner ℝ v (o.rightAngleRotation e) =
      ((inner ℝ v e)^2 + (inner ℝ (o.rightAngleRotation v) e)^2) / inner ℝ v e := by
  rw [(quarterTurn_inner_coordinates o v e).1,
    (quarterTurn_inner_coordinates o v e).2]
  by_cases hx : inner ℝ v e = 0
  · simp [hx]
  · field_simp
    ring

/-- A nonvertical rightward edge has its left normal above its graph;
a leftward edge has its left normal below its graph. -/
theorem normalGraphSlope_pos_iff (v e : V) (hx : inner ℝ v e ≠ 0) :
    0 < inner ℝ (o.rightAngleRotation v) (o.rightAngleRotation e) -
      (inner ℝ (o.rightAngleRotation v) e / inner ℝ v e) *
        inner ℝ v (o.rightAngleRotation e) ↔ 0 < inner ℝ v e := by
  rw [normalGraphSlope_identity]
  apply div_pos_iff_of_pos_left
  exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg _)

/-- The same exact sign test for leftward edges. -/
theorem normalGraphSlope_neg_iff (v e : V) (hx : inner ℝ v e ≠ 0) :
    inner ℝ (o.rightAngleRotation v) (o.rightAngleRotation e) -
      (inner ℝ (o.rightAngleRotation v) e / inner ℝ v e) *
        inner ℝ v (o.rightAngleRotation e) < 0 ↔ inner ℝ v e < 0 := by
  rw [normalGraphSlope_identity]
  have hnum : 0 < (inner ℝ v e)^2 + (inner ℝ (o.rightAngleRotation v) e)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg _)
  rw [div_neg_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact (hnum.not_gt h).elim
  · intro h
    exact Or.inl ⟨hnum, h⟩

/-- An arbitrary point on the supporting edge line, translated by a left
normal, has this exact signed displacement from the edge's graph. -/
theorem normalTranslate_graphHeight (v a e : V) (t r : ℝ)
    (hx : inner ℝ v e ≠ 0) :
    inner ℝ (o.rightAngleRotation v) (a + t • e + r • o.rightAngleRotation e) -
      (inner ℝ (o.rightAngleRotation v) a +
        (inner ℝ (o.rightAngleRotation v) e / inner ℝ v e) *
          (inner ℝ v (a + t • e + r • o.rightAngleRotation e) - inner ℝ v a)) =
      r * (((inner ℝ v e)^2 + (inner ℝ (o.rightAngleRotation v) e)^2) /
        inner ℝ v e) := by
  simp only [inner_add_right, real_inner_smul_right,
    (quarterTurn_inner_coordinates o v e).1,
    (quarterTurn_inner_coordinates o v e).2]
  field_simp
  ring

/-- The exact displacement formula expressed using the actual polygon edge
and the affine graph function used in the strip construction. -/
theorem edgeHeight_normalTranslate {n : ℕ} (v : V) (p : Polygon V n)
    (i : Fin n) (t r : ℝ) (hx : inner ℝ v (edgeVector p i) ≠ 0) :
    inner ℝ (o.rightAngleRotation v)
        (p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i)) -
      edgeHeight (innerSL ℝ v) (innerSL ℝ (o.rightAngleRotation v)) p i
        (inner ℝ v (p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i))) =
      r * (((inner ℝ v (edgeVector p i))^2 +
        (inner ℝ (o.rightAngleRotation v) (edgeVector p i))^2) /
        inner ℝ v (edgeVector p i)) := by
  have h := normalTranslate_graphHeight o v (p i) (edgeVector p i) t r hx
  convert h using 1
  simp [edgeHeight, Polygon.edgePath, AffineMap.lineMap_apply_module', edgeVector,
    inner_sub_right, inner_add_right, real_inner_smul_right, div_eq_mul_inv]
  ring

/-- For a positive left normal translation, being above the actual edge
graph is equivalent to the edge's being rightward. -/
theorem leftNormal_above_edgeHeight_iff {n : ℕ} (v : V) (p : Polygon V n)
    (i : Fin n) (t r : ℝ) (hx : inner ℝ v (edgeVector p i) ≠ 0) (hr : 0 < r) :
    edgeHeight (innerSL ℝ v) (innerSL ℝ (o.rightAngleRotation v)) p i
        (inner ℝ v (p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i))) <
      inner ℝ (o.rightAngleRotation v)
        (p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i)) ↔
      0 < inner ℝ v (edgeVector p i) := by
  rw [← sub_pos, edgeHeight_normalTranslate o v p i t r hx,
    mul_pos_iff_of_pos_left hr]
  exact div_pos_iff_of_pos_left
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg _))

/-- For a positive left normal translation, being below the actual edge
graph is equivalent to the edge's being leftward. -/
theorem leftNormal_below_edgeHeight_iff {n : ℕ} (v : V) (p : Polygon V n)
    (i : Fin n) (t r : ℝ) (hx : inner ℝ v (edgeVector p i) ≠ 0) (hr : 0 < r) :
    inner ℝ (o.rightAngleRotation v)
        (p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i)) <
      edgeHeight (innerSL ℝ v) (innerSL ℝ (o.rightAngleRotation v)) p i
        (inner ℝ v (p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i))) ↔
      inner ℝ v (edgeVector p i) < 0 := by
  rw [← sub_neg, edgeHeight_normalTranslate o v p i t r hx]
  have hnum : 0 < (inner ℝ v (edgeVector p i))^2 +
      (inner ℝ (o.rightAngleRotation v) (edgeVector p i))^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg _)
  have hm : ∀ q : ℝ, r * q < 0 ↔ q < 0 := by
    intro q
    simpa only [mul_zero] using (mul_lt_mul_iff_right₀ hr : r * q < r * 0 ↔ q < 0)
  rw [hm, div_neg_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact (hnum.not_gt h).elim
  · intro h
    exact Or.inl ⟨hnum, h⟩

/-- On a rightward edge, the literal bounded-side-on-left hypothesis gives
points in the region lying strictly above the edge graph at every small
positive left normal displacement. -/
theorem boundedSideOnLeft_normal_above {n : ℕ} (v : V) (p : Polygon V n)
    (U : Set V) (hleft : HasBoundedSideOnLeft o p U)
    (i : Fin n) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hx : 0 < inner ℝ v (edgeVector p i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i) ∈ U ∧
      edgeHeight (innerSL ℝ v) (innerSL ℝ (o.rightAngleRotation v)) p i
          (inner ℝ v (p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i))) <
        inner ℝ (o.rightAngleRotation v)
          (p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i)) := by
  obtain ⟨ε, hε, hU⟩ := hleft i t ht
  exact ⟨ε, hε, fun r hr hre => ⟨hU r hr hre,
    (leftNormal_above_edgeHeight_iff o v p i t r hx.ne' hr).mpr hx⟩⟩

/-- The corresponding local statement on a leftward edge places its inward
normal points strictly below the edge graph. -/
theorem boundedSideOnLeft_normal_below {n : ℕ} (v : V) (p : Polygon V n)
    (U : Set V) (hleft : HasBoundedSideOnLeft o p U)
    (i : Fin n) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hx : inner ℝ v (edgeVector p i) < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i) ∈ U ∧
      inner ℝ (o.rightAngleRotation v)
          (p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i)) <
        edgeHeight (innerSL ℝ v) (innerSL ℝ (o.rightAngleRotation v)) p i
          (inner ℝ v (p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i))) := by
  obtain ⟨ε, hε, hU⟩ := hleft i t ht
  exact ⟨ε, hε, fun r hr hre => ⟨hU r hr hre,
    (leftNormal_below_edgeHeight_iff o v p i t r hx.ne hr).mpr hx⟩⟩

/-- The normal displacement coefficient has exactly the sign of the
horizontal edge coordinate. -/
theorem normalGraphSlope_sign (v e : V) (hx : inner ℝ v e ≠ 0) :
    SignType.sign (inner ℝ (o.rightAngleRotation v) (o.rightAngleRotation e) -
      (inner ℝ (o.rightAngleRotation v) e / inner ℝ v e) *
        inner ℝ v (o.rightAngleRotation e)) = SignType.sign (inner ℝ v e) := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [sign_neg ((normalGraphSlope_neg_iff o v e hx).mpr h), sign_neg h]
  · rw [sign_pos ((normalGraphSlope_pos_iff o v e hx).mpr h), sign_pos h]


/-- Positivity of the actual oriented area form gives positive angular sign. -/
theorem oangle_sign_eq_one_of_areaForm_pos {a b : V} (h : 0 < o.areaForm a b) :
    (o.oangle a b).sign = 1 := by
  have him : 0 < (o.kahler a b).im := by
    simpa [o.kahler_apply_apply] using h
  have hz : o.kahler a b ≠ 0 := by
    intro hz
    simp [hz] at him
  change SignType.sign (Real.sin (Complex.arg (o.kahler a b))) = 1
  rw [Complex.sin_arg]
  exact sign_pos (div_pos him (norm_pos_iff.mpr hz))

/-- In the oriented coordinates determined by `v,Jv`, two rightward rays
are ordered counterclockwise exactly as their slopes are ordered. -/
theorem oangle_sign_eq_one_of_rightward_slope_lt {v a b : V} (hv : v ≠ 0)
    (ha : 0 < inner ℝ v a) (hb : 0 < inner ℝ v b)
    (hs : inner ℝ (o.rightAngleRotation v) a / inner ℝ v a <
      inner ℝ (o.rightAngleRotation v) b / inner ℝ v b) :
    (o.oangle a b).sign = 1 := by
  have hdet : 0 < inner ℝ v a * inner ℝ (o.rightAngleRotation v) b -
      inner ℝ (o.rightAngleRotation v) a * inner ℝ v b := by
    have h := (div_lt_div_iff₀ ha hb).mp hs
    nlinarith
  have hid := o.inner_mul_areaForm_sub v a b
  rw [← o.inner_rightAngleRotation_left v a,
    ← o.inner_rightAngleRotation_left v b] at hid
  have hn : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  apply oangle_sign_eq_one_of_areaForm_pos o
  apply (mul_pos_iff_of_pos_left hn).mp
  rw [← hid]
  exact hdet

/-- The incoming direction at a leftmost vertex is the negative of its
backwards ray `b`.  Outgoing slope below backwards-incoming slope therefore
gives a positive convex turn from `-b` to `a`. -/
theorem oangle_neg_sign_eq_one_of_rightward_slope_lt {v a b : V} (hv : v ≠ 0)
    (ha : 0 < inner ℝ v a) (hb : 0 < inner ℝ v b)
    (hs : inner ℝ (o.rightAngleRotation v) a / inner ℝ v a <
      inner ℝ (o.rightAngleRotation v) b / inner ℝ v b) :
    (o.oangle (-b) a).sign = 1 := by
  rw [o.oangle_sign_neg_left, o.oangle_rev a b, Real.Angle.sign_neg, neg_neg]
  exact oangle_sign_eq_one_of_rightward_slope_lt o hv ha hb hs


/-- The literal positive-left condition orders the outgoing and incoming
edges near a uniquely leftmost vertex. No local orientation or convexity
certificate is assumed: boundedness supplies an actual boundary point above
an inward normal translation. -/
theorem nearMinimum_outgoing_below_incoming
    (o : Orientation ℝ V (Fin 2)) (v : V) (hv : v ≠ 0)
    {p : Polygon V n} (hp : IsSimple p) {U : Set V}
    (hU : IsBoundedSide p U) (hleft : HasBoundedSideOnLeft o p U)
    (i : Fin n) {b : ℝ} (hb : inner ℝ v (p i) < b)
    (hothers : ∀ j : Fin n, j ≠ i → b < inner ℝ v (p j)) :
    ∀ s ∈ Ioo (inner ℝ v (p i)) b,
      edgeHeight (innerSL ℝ v) (innerSL ℝ (o.rightAngleRotation v)) p i s <
        edgeHeight (innerSL ℝ v) (innerSL ℝ (o.rightAngleRotation v)) p
          ((finRotate n).symm i) s := by
  let x : V →L[ℝ] ℝ := innerSL ℝ v
  let y : V →L[ℝ] ℝ := innerSL ℝ (o.rightAngleRotation v)
  have hxy : Function.Injective (fun z : V => (x z, y z)) :=
    inner_coordinates_injective o v hv
  have hnext : finRotate n i ≠ i := fun h => hp.2.2.1 i (congrArg p h.symm)
  have hpred : (finRotate n).symm i ≠ i := by
    intro h
    apply hnext
    have := congrArg (finRotate n) h
    simpa only [Equiv.apply_symm_apply] using this.symm
  have hout : x (p i) < x (p (finRotate n i)) := hb.trans (hothers _ hnext)
  have hin : x (p i) < x (p ((finRotate n).symm i)) := hb.trans (hothers _ hpred)
  have hxi : x (p (finRotate n i)) ≠ x (p i) := hout.ne'
  have hxp : x (p (finRotate n ((finRotate n).symm i))) ≠
      x (p ((finRotate n).symm i)) := by
    simpa only [Equiv.apply_symm_apply] using hin.ne
  have hright : 0 < inner ℝ v (edgeVector p i) := by
    simpa only [edgeVector, inner_sub_right, x, innerSL_apply_apply] using sub_pos.mpr hout
  have hiActive : Ioo (x (p i)) b ⊆
      uIoo (x (p i)) (x (p (finRotate n i))) := by
    intro s hs
    exact mem_uIoo_of_lt hs.1 (hs.2.trans (hothers _ hnext))
  have hpActive : Ioo (x (p i)) b ⊆
      uIoo (x (p ((finRotate n).symm i))) (x (p (finRotate n ((finRotate n).symm i)))) := by
    intro s hs
    simpa only [Equiv.apply_symm_apply] using
      (mem_uIoo_of_gt hs.1 (hs.2.trans (hothers _ hpred)) :
        s ∈ uIoo (x (p ((finRotate n).symm i))) (x (p i)))
  obtain ⟨s₀, hs₀⟩ := exists_between hb
  let t : ℝ := (s₀ - x (p i)) / (x (p (finRotate n i)) - x (p i))
  have ht : t ∈ Ioo (0 : ℝ) 1 := lineParameter_mem_Ioo (hiActive hs₀)
  let a : V := p.edgePath ℝ i t
  have ha : x a = s₀ := by
    change x (edgeAtCoordinate x p i s₀) = s₀
    exact projection_edgeAtCoordinate x p i hxi s₀
  obtain ⟨ε, hε, hnormal⟩ := boundedSideOnLeft_normal_above o v p U hleft i t ht hright
  have hc : Continuous (fun r : ℝ => x (a + r • o.rightAngleRotation (edgeVector p i))) := by
    fun_prop
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ),
      x (a + r • o.rightAngleRotation (edgeVector p i)) ∈ Ioo (x (p i)) b := by
    apply hc.continuousAt.eventually
    apply isOpen_Ioo.mem_nhds
    simpa only [zero_smul, add_zero, ha] using (show s₀ ∈ Ioo (x (p i)) b from hs₀)
  have hnearGT : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      x (a + r • o.rightAngleRotation (edgeVector p i)) ∈ Ioo (x (p i)) b :=
    hnear.filter_mono nhdsWithin_le_nhds
  obtain ⟨r, hrstrip, hrpos, hre⟩ := (hnearGT.and (Ioo_mem_nhdsGT hε)).exists
  let z : V := a + r • o.rightAngleRotation (edgeVector p i)
  have hzU : z ∈ U := (hnormal r hrpos hre).1
  have hzabove : edgeHeight x y p i (x z) < y z := (hnormal r hrpos hre).2
  obtain ⟨d, hxd, hyd⟩ := exists_verticalDirection x y hxy
  obtain ⟨w, hw, hwx, hwy⟩ := (exists_boundary_below_above hU hzU x y d hxd hyd).2
  have hwmin : x (p i) < x w := by rw [hwx]; exact hrstrip.1
  have hwother : ∀ j : Fin n, j ≠ i → x w < x (p j) := by
    intro j hji
    rw [hwx]
    exact hrstrip.2.trans (hothers j hji)
  have horder : edgeHeight x y p i (x z) <
      edgeHeight x y p ((finRotate n).symm i) (x z) := by
    rcases nearMinimum_boundary_mem_incident p x i hw hwmin hwother with hwi | hwp
    · have hwheight : edgeHeight x y p i (x z) = y w := by
        rw [← hwx, edgeHeight_eq, edgeAtCoordinate_eq_of_mem_edgeSet x p i hxi hwi]
      exact (lt_irrefl (y w) (by linarith)).elim
    · have hwheight : edgeHeight x y p ((finRotate n).symm i) (x z) = y w := by
        rw [← hwx, edgeHeight_eq,
          edgeAtCoordinate_eq_of_mem_edgeSet x p ((finRotate n).symm i) hxp hwp]
      rw [hwheight]
      exact hzabove.trans hwy
  have hprop := edgeHeight_lt_on_strip x y hxy hp hpred.symm hxi hxp
    isPreconnected_Ioo hiActive hpActive hrstrip
    (by simpa only [← edgeHeight_eq] using horder)
  intro s hs
  simpa only [← edgeHeight_eq] using hprop s hs

omit [Fact (Module.finrank ℝ V = 2)] in
/-- A supporting edge graph expressed from its starting endpoint. -/
theorem edgeHeight_eq_start (x y : V →L[ℝ] ℝ) (p : Polygon V n)
    (i : Fin n) (s : ℝ) :
    edgeHeight x y p i s = y (p i) +
      (y (edgeVector p i) / x (edgeVector p i)) * (s - x (p i)) := by
  simp [edgeHeight, edgeVector, map_sub, div_eq_mul_inv]
  ring

omit [Fact (Module.finrank ℝ V = 2)] in
/-- The same supporting graph expressed from its terminal endpoint. -/
theorem edgeHeight_eq_end (x y : V →L[ℝ] ℝ) (p : Polygon V n)
    (i : Fin n) (s : ℝ) (hx : x (edgeVector p i) ≠ 0) :
    edgeHeight x y p i s = y (p (finRotate n i)) +
      (y (edgeVector p i) / x (edgeVector p i)) *
        (s - x (p (finRotate n i))) := by
  rw [edgeHeight_eq_start]
  simp only [edgeVector, map_sub] at hx ⊢
  field_simp
  ring

/-- The original positive-left condition forces a genuine positive convex
exterior turn at every uniquely projection-minimal vertex. -/
theorem exteriorAngle_pos_of_strict_minimum
    (o : Orientation ℝ V (Fin 2)) (v : V) (hv : v ≠ 0)
    {p : Polygon V n} (hp : IsSimple p) {U : Set V}
    (hU : IsBoundedSide p U) (hleft : HasBoundedSideOnLeft o p U)
    (i : Fin n) {b : ℝ} (hb : inner ℝ v (p i) < b)
    (hothers : ∀ j : Fin n, j ≠ i → b < inner ℝ v (p j)) :
    exteriorAngle o p i ∈ Ioo (0 : ℝ) Real.pi := by
  let x : V →L[ℝ] ℝ := innerSL ℝ v
  let y : V →L[ℝ] ℝ := innerSL ℝ (o.rightAngleRotation v)
  have hnext : finRotate n i ≠ i := fun h => hp.2.2.1 i (congrArg p h.symm)
  have hpred : (finRotate n).symm i ≠ i := by
    intro h
    apply hnext
    have := congrArg (finRotate n) h
    simpa only [Equiv.apply_symm_apply] using this.symm
  have ha : 0 < inner ℝ v (edgeVector p i) := by
    simp only [edgeVector, inner_sub_right]
    exact sub_pos.mpr (hb.trans (hothers _ hnext))
  have hb' : 0 < inner ℝ v (-incomingVector p i) := by
    simp only [incomingVector, edgeVector, Equiv.apply_symm_apply, inner_neg_right,
      inner_sub_right]
    linarith [hothers _ hpred]
  have hinc : x (edgeVector p ((finRotate n).symm i)) ≠ 0 := by
    change inner ℝ v (incomingVector p i) ≠ 0
    exact neg_ne_zero.mp (by simpa only [inner_neg_right] using (ne_of_gt hb'))
  obtain ⟨s, hs⟩ := exists_between hb
  have hheight := nearMinimum_outgoing_below_incoming o v hv hp hU hleft i hb hothers s hs
  change edgeHeight x y p i s < edgeHeight x y p ((finRotate n).symm i) s at hheight
  rw [edgeHeight_eq_start, edgeHeight_eq_end x y p ((finRotate n).symm i) s hinc,
    Equiv.apply_symm_apply] at hheight
  have hmul :
      (y (edgeVector p i) / x (edgeVector p i)) * (s - x (p i)) <
      (y (incomingVector p i) / x (incomingVector p i)) * (s - x (p i)) := by
    exact add_lt_add_iff_left (y (p i)) |>.mp hheight
  have hdelta : 0 < s - x (p i) := sub_pos.mpr hs.1
  have hslope : y (edgeVector p i) / x (edgeVector p i) <
      y (incomingVector p i) / x (incomingVector p i) := by
    exact (mul_lt_mul_iff_left₀ hdelta).mp hmul
  have hslope' : inner ℝ (o.rightAngleRotation v) (edgeVector p i) /
        inner ℝ v (edgeVector p i) <
      inner ℝ (o.rightAngleRotation v) (-incomingVector p i) /
        inner ℝ v (-incomingVector p i) := by
    simpa only [x, y, innerSL_apply_apply, inner_neg_right, neg_div_neg_eq] using hslope
  have hsign := oangle_neg_sign_eq_one_of_rightward_slope_lt o hv ha hb' hslope'
  simp only [neg_neg] at hsign
  exact Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr hsign


/-- The actual geometric input supplies a separating projection with a positive
exterior turn at its unique minimum, without any prescribed turning number. -/
theorem exists_positive_minimum_turn (o : Orientation ℝ V (Fin 2))
    {p : Polygon V n} (hp : IsSimple p) {U : Set V}
    (hU : IsBoundedSide p U) (hleft : HasBoundedSideOnLeft o p U) :
    ∃ (v : V) (i : Fin n), v ≠ 0 ∧
      Function.Injective (fun j : Fin n => inner ℝ v (p j)) ∧
      (∀ j : Fin n, j ≠ i → inner ℝ v (p i) < inner ℝ v (p j)) ∧
      exteriorAngle o p i ∈ Ioo (0 : ℝ) Real.pi := by
  have : NeZero n := ⟨by have := hp.1; omega⟩
  obtain ⟨v, hv⟩ := exists_separating_direction p hp.2.1
  have hv₀ : v ≠ 0 := by
    intro hzero
    have h : (⟨0, by have := hp.1; omega⟩ : Fin n) =
        ⟨1, by have := hp.1; omega⟩ := hv (by simp [hzero])
    have hval := congrArg Fin.val h
    simp at hval
  obtain ⟨i, hi⟩ := exists_strict_minimum p (innerSL ℝ v) hv
  obtain ⟨b, hb, hothers⟩ := exists_strip_after_strict_minimum p (innerSL ℝ v) i hi
  exact ⟨v, i, hv₀, hv, hi,
    exteriorAngle_pos_of_strict_minimum o v hv₀ hp hU hleft i hb hothers⟩

theorem principalAngle_mem_rightHalfplane {v x : V}
    (hv : v ≠ 0) (hx : 0 < inner ℝ v x) :
    (o.oangle v x).toReal ∈ Ioo (-Real.pi / 2) (Real.pi / 2) := by
  have hx0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  have hangle : InnerProductGeometry.angle v x < Real.pi / 2 := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt hx)
      (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr h)
  rw [o.angle_eq_abs_oangle_toReal hv hx0] at hangle
  simpa only [Set.mem_Ioo, neg_div] using abs_lt.mp hangle

theorem principalAngle_sub_mem_Ioo {v x y : V}
    (hv : v ≠ 0) (hx : 0 < inner ℝ v x) (hy : 0 < inner ℝ v y) :
    (o.oangle v y).toReal - (o.oangle v x).toReal ∈ Ioo (-Real.pi) Real.pi := by
  obtain ⟨hxl, hxu⟩ := principalAngle_mem_rightHalfplane o hv hx
  obtain ⟨hyl, hyu⟩ := principalAngle_mem_rightHalfplane o hv hy
  constructor <;> linarith

/-- Two rays in the right half-plane, whose turn from the negative second ray
back to the first is positive, satisfy the exact real branch identity. -/
theorem principalAngle_sub_add_positive_turn {v x y : V}
    (hv : v ≠ 0) (hx : 0 < inner ℝ v x) (hy : 0 < inner ℝ v y)
    (hpositive : 0 < (o.oangle (-y) x).toReal) :
    ((o.oangle v y).toReal - (o.oangle v x).toReal) +
      (o.oangle (-y) x).toReal = Real.pi := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have hβ := principalAngle_sub_mem_Ioo o hv hx hy
  have hε := Real.Angle.toReal_le_pi (o.oangle (-y) x)
  have hcoeβ :
      (((o.oangle v y).toReal - (o.oangle v x).toReal : ℝ) : Real.Angle) =
        o.oangle x y := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    exact o.oangle_sub_left hv hx0 hy0
  have hcoe :
      ((Real.pi - (o.oangle (-y) x).toReal : ℝ) : Real.Angle) = o.oangle x y := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_toReal,
      o.oangle_neg_left hy0 hx0, o.oangle_rev y x]
    abel
  have hbranches := congrArg Real.Angle.toReal (hcoeβ.trans hcoe.symm)
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hβ.1, hβ.2.le⟩,
    Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos], by linarith⟩]
    at hbranches
  linarith


open P202Specs.PolygonTurning

/-- At an actual uniquely projection-minimal polygon vertex, the half-plane
secant chart and positive exterior turn satisfy the exact real branch identity. -/
theorem minimum_principalAngle_sub_add_exteriorAngle
    (v : V) (hv : v ≠ 0) {n : ℕ} {p : Polygon V n}
    (hp : IsSimple p) {U : Set V} (hU : IsBoundedSide p U)
    (hleft : HasBoundedSideOnLeft o p U) (i : Fin n)
    (hmin : ∀ j : Fin n, j ≠ i → inner ℝ v (p i) < inner ℝ v (p j)) :
    ((o.oangle v (-incomingVector p i)).toReal -
      (o.oangle v (edgeVector p i)).toReal) + exteriorAngle o p i = Real.pi := by
  have hnext : finRotate n i ≠ i := fun h => hp.2.2.1 i (congrArg p h.symm)
  have hpred : (finRotate n).symm i ≠ i := by
    intro h
    apply hnext
    have := congrArg (finRotate n) h
    simpa only [Equiv.apply_symm_apply] using this.symm
  have hout : 0 < inner ℝ v (edgeVector p i) := by
    simp only [edgeVector, inner_sub_right]
    exact sub_pos.mpr (hmin _ hnext)
  have hin : 0 < inner ℝ v (-incomingVector p i) := by
    simp only [incomingVector, edgeVector, Equiv.apply_symm_apply, inner_neg_right,
      inner_sub_right]
    linarith [hmin _ hpred]
  obtain ⟨b, hb, hothers⟩ :=
    exists_strip_after_strict_minimum p (innerSL ℝ v) i hmin
  have hε := exteriorAngle_pos_of_strict_minimum o v hv hp hU hleft i hb hothers
  have hpos : 0 < (o.oangle (-(-incomingVector p i)) (edgeVector p i)).toReal := by
    simpa only [neg_neg, exteriorAngle] using hε.1
  simpa only [neg_neg, exteriorAngle] using
    principalAngle_sub_add_positive_turn o hv hout hin hpos


/-- The half-plane chart difference is the shorter signed angle between
its two rays, with no branch correction. -/
theorem oangle_toReal_eq_sub_of_rightHalfplane {v x y : V}
    (hv : v ≠ 0) (hx : 0 < inner ℝ v x) (hy : 0 < inner ℝ v y) :
    (o.oangle x y).toReal =
      (o.oangle v y).toReal - (o.oangle v x).toReal := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have hβ := principalAngle_sub_mem_Ioo o hv hx hy
  have hcoe :
      (((o.oangle v y).toReal - (o.oangle v x).toReal : ℝ) : Real.Angle) =
        o.oangle x y := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    exact o.oangle_sub_left hv hx0 hy0
  rw [← hcoe]
  exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hβ.1, hβ.2.le⟩

/-- The shortest secant angle at an actual minimum vertex is the complement
of its positive exterior turn, including the exact real branch choice. -/
theorem minimum_shortAngle_add_exteriorAngle
    (v : V) (hv : v ≠ 0) {n : ℕ} {p : Polygon V n}
    (hp : IsSimple p) {U : Set V} (hU : IsBoundedSide p U)
    (hleft : HasBoundedSideOnLeft o p U) (i : Fin n)
    (hmin : ∀ j : Fin n, j ≠ i → inner ℝ v (p i) < inner ℝ v (p j)) :
    (o.oangle (edgeVector p i) (-incomingVector p i)).toReal +
      exteriorAngle o p i = Real.pi := by
  have hnext : finRotate n i ≠ i := fun h => hp.2.2.1 i (congrArg p h.symm)
  have hpred : (finRotate n).symm i ≠ i := by
    intro h
    apply hnext
    have := congrArg (finRotate n) h
    simpa only [Equiv.apply_symm_apply] using this.symm
  have hout : 0 < inner ℝ v (edgeVector p i) := by
    simp only [edgeVector, inner_sub_right]
    exact sub_pos.mpr (hmin _ hnext)
  have hin : 0 < inner ℝ v (-incomingVector p i) := by
    simp only [incomingVector, edgeVector, Equiv.apply_symm_apply, inner_neg_right,
      inner_sub_right]
    linarith [hmin _ hpred]
  rw [oangle_toReal_eq_sub_of_rightHalfplane o hv hout hin]
  exact minimum_principalAngle_sub_add_exteriorAngle o v hv hp hU hleft i hmin


end Projection

namespace DiscreteSecant
open scoped Pointwise
theorem principalAngle_abs_lt_half_pi_of_inner_pos {a x : V}
    (h : 0 < inner ℝ a x) : |(o.oangle a x).toReal| < Real.pi / 2 := by
  apply Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two.mp
  have ha : a ≠ 0 := by rintro rfl; simp at h
  have hx : x ≠ 0 := by rintro rfl; simp at h
  rw [o.cos_oangle_eq_inner_div_norm_mul_norm ha hx]
  exact div_pos h (mul_pos (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hx))

theorem oangle_toReal_eq_sub_of_common_halfplane {a x y : V}
    (hx : 0 < inner ℝ a x) (hy : 0 < inner ℝ a y) :
    (o.oangle x y).toReal = (o.oangle a y).toReal - (o.oangle a x).toReal := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hxb := abs_lt.mp (principalAngle_abs_lt_half_pi_of_inner_pos o hx)
  have hyb := abs_lt.mp (principalAngle_abs_lt_half_pi_of_inner_pos o hy)
  let t := (o.oangle a y).toReal - (o.oangle a x).toReal
  have ht : ((t : ℝ) : Real.Angle) = o.oangle x y := by
    dsimp [t]
    rw [Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    exact o.oangle_sub_left ha0 hx0 hy0
  rw [← ht]
  exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩

theorem oangle_toReal_triangle_sum_of_common_halfplane {a x y z : V}
    (hx : 0 < inner ℝ a x) (hy : 0 < inner ℝ a y) (hz : 0 < inner ℝ a z) :
    (o.oangle x y).toReal + (o.oangle y z).toReal = (o.oangle x z).toReal := by
  rw [oangle_toReal_eq_sub_of_common_halfplane o hx hy,
    oangle_toReal_eq_sub_of_common_halfplane o hy hz,
    oangle_toReal_eq_sub_of_common_halfplane o hx hz]
  ring

theorem exists_inner_positive_of_convex_compact {S : Set V}
    (hconv : Convex ℝ S) (hcomp : IsCompact S) (h0 : (0 : V) ∉ S) :
    ∃ a : V, ∀ x ∈ S, 0 < inner ℝ a x := by
  let : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  obtain ⟨f, u, hu, hS⟩ := geometric_hahn_banach_point_closed hconv hcomp.isClosed h0
  refine ⟨(InnerProductSpace.toDual ℝ V).symm f, ?_⟩
  intro x hx
  rw [InnerProductSpace.toDual_symm_apply]
  simpa using (hu.trans (hS x hx))


omit [Fact (Module.finrank ℝ V = 2)] in
theorem isCompact_real_segment (a b : V) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image (by fun_prop)

theorem oangle_toReal_add_through_sum {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (hπ : o.oangle x y ≠ (Real.pi : Real.Angle)) :
    (o.oangle x (x + y)).toReal + (o.oangle (x + y) y).toReal =
      (o.oangle x y).toReal := by
  have h0 : (0 : V) ∉ segment ℝ x y := by
    intro hz
    have hr : SameRay ℝ (-x) y := by
      simpa using mem_segment_iff_sameRay.mp hz
    exact hπ (o.oangle_eq_pi_iff_sameRay_neg.mpr ⟨hx, hy, sameRay_neg_swap.mp hr⟩)
  obtain ⟨a, ha⟩ := exists_inner_positive_of_convex_compact (convex_segment x y)
    (isCompact_real_segment x y) h0
  have hax := ha x (left_mem_segment ℝ x y)
  have hay := ha y (right_mem_segment ℝ x y)
  apply oangle_toReal_triangle_sum_of_common_halfplane o hax _ hay
  rw [inner_add_right]
  exact add_pos hax hay

theorem oangle_toReal_square_of_disjoint_segments {a b c d : V}
    (h : Disjoint (segment ℝ a b) (segment ℝ c d)) :
    (o.oangle (c - a) (d - a)).toReal + (o.oangle (d - a) (d - b)).toReal =
      (o.oangle (c - a) (c - b)).toReal + (o.oangle (c - b) (d - b)).toReal := by
  let S := segment ℝ c d - segment ℝ a b
  have hconv : Convex ℝ S := (convex_segment c d).sub (convex_segment a b)
  have hcomp : IsCompact S := by
    dsimp [S]
    rw [← sub_image_prod]
    exact ((isCompact_real_segment c d).prod (isCompact_real_segment a b)).image (by fun_prop)
  have h0 : (0 : V) ∉ S := h.symm.zero_notMem_sub_set
  obtain ⟨v, hv⟩ := exists_inner_positive_of_convex_compact hconv hcomp h0
  have hca := hv (c - a) (sub_mem_sub (left_mem_segment ℝ c d) (left_mem_segment ℝ a b))
  have hcb := hv (c - b) (sub_mem_sub (left_mem_segment ℝ c d) (right_mem_segment ℝ a b))
  have hda := hv (d - a) (sub_mem_sub (right_mem_segment ℝ c d) (left_mem_segment ℝ a b))
  have hdb := hv (d - b) (sub_mem_sub (right_mem_segment ℝ c d) (right_mem_segment ℝ a b))
  rw [oangle_toReal_triangle_sum_of_common_halfplane o hca hda hdb,
    oangle_toReal_triangle_sum_of_common_halfplane o hca hcb hdb]


omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] in
theorem rectangle_row_cancellation (A B : ℕ → ℕ → ℝ) (r j : ℕ)
    (h : ∀ i < r, A i j + B i (j + 1) = B i j + A (i + 1) j) :
    A 0 j + ∑ i ∈ Finset.range r, B i (j + 1) =
      A r j + ∑ i ∈ Finset.range r, B i j := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hi := ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self r)))
    have hr := h r (Nat.lt_succ_self r)
    simp only [Finset.sum_range_succ]
    linarith

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] in
theorem triangularGrid_cancellation (A B : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (m : ℕ)
    (htriangle : ∀ i ≤ m, E i = A i (i + 1) + B i (i + 2))
    (hsquare : ∀ i j, i + 1 < j → j ≤ m + 1 →
      A i j + B i (j + 1) = B i j + A (i + 1) j) :
    (∑ i ∈ Finset.range (m + 1), E i) =
      (∑ j ∈ Finset.range (m + 1), A 0 (j + 1)) +
        (∑ i ∈ Finset.range (m + 1), B i (m + 2)) := by
  induction m with
  | zero => simpa using htriangle 0 (Nat.zero_le 0)
  | succ m ih =>
    have hi := ih (fun i hi => htriangle i (Nat.le_trans hi (Nat.le_succ m)))
      (fun i j hij hj => hsquare i j hij (Nat.le_trans hj (Nat.le_succ _)))
    have hr := rectangle_row_cancellation A B (m + 1) (m + 2) (by
      intro i hi
      exact hsquare i (m + 2) (by omega) (by omega))
    have ht := htriangle (m + 1) (by omega)
    simp only [Finset.sum_range_succ] at *
    linarith


/-- A purely finite secant comparison for a closed embedded polygonal vertex
array.  The two boundary position-vector sums come from the two outside legs
of the secant triangle; no interpolation or angle lift is needed. -/
theorem closedArray_secant_comparison (m : ℕ) (v : ℕ → V)
    (hclose : v (m + 3) = v 0)
    (hne : ∀ i < m + 3, v (i + 1) - v i ≠ 0)
    (hturn : ∀ i < m + 2,
      o.oangle (v (i + 1) - v i) (v (i + 2) - v (i + 1)) ≠
        (Real.pi : Real.Angle))
    (hclosing : o.oangle (v (m + 3) - v (m + 2)) (v 1 - v 0) ≠
      (Real.pi : Real.Angle))
    (hdisj : ∀ i j, i + 1 < j → j < m + 3 →
      ¬ (i = 0 ∧ j = m + 2) →
      Disjoint (segment ℝ (v i) (v (i + 1))) (segment ℝ (v j) (v (j + 1)))) :
    (∑ i ∈ Finset.range (m + 2),
      (o.oangle (v (i + 1) - v i) (v (i + 2) - v (i + 1))).toReal) =
    2 * (∑ j ∈ Finset.range (m + 1),
      (o.oangle (v (j + 1) - v 0) (v (j + 2) - v 0)).toReal) +
      (o.oangle (v (m + 3) - v (m + 2)) (v 1 - v 0)).toReal := by
  let C : ℕ → ℕ → V := fun i j => v j - v i
  let e : ℕ → V := fun i => C i (i + 1)
  let ε := (o.oangle (e (m + 2)) (e 0)).toReal
  let A : ℕ → ℕ → ℝ := fun i j =>
    if i = 0 ∧ j = m + 2 then ε else (o.oangle (C i j) (C i (j + 1))).toReal
  let B : ℕ → ℕ → ℝ := fun i j =>
    if i = 0 ∧ j = m + 3 then 0 else (o.oangle (C i j) (C (i + 1) j)).toReal
  let E : ℕ → ℝ := fun i => (o.oangle (e i) (e (i + 1))).toReal
  have he : ∀ i < m + 3, e i ≠ 0 := hne
  have hπ : ∀ i < m + 2, o.oangle (e i) (e (i + 1)) ≠ (Real.pi : Real.Angle) := by
    intro i hi
    simpa [e, C, Nat.add_assoc] using hturn i hi
  have hπ0 : o.oangle (e (m + 2)) (e 0) ≠ (Real.pi : Real.Angle) := hclosing
  have htriangle (i : ℕ) (hi : i ≤ m + 1) :
      E i = A i (i + 1) + B i (i + 2) := by
    have hAi : ¬ (i = 0 ∧ i + 1 = m + 2) := by omega
    have hBi : ¬ (i = 0 ∧ i + 2 = m + 3) := by omega
    have hC : C i (i + 2) = e i + e (i + 1) := by
      dsimp [C, e]
      simp only [Nat.add_assoc]
      abel
    simpa only [E, A, B, ite_eq_right hAi, ite_eq_right hBi, hC, show C i (i + 1) = e i from rfl,
      show C (i + 1) (i + 2) = e (i + 1) by simp [C, e, Nat.add_assoc]] using
      (oangle_toReal_add_through_sum o (he i (by omega)) (he (i + 1) (by omega))
        (hπ i (by omega))).symm
  have hsquare (i j : ℕ) (hij : i + 1 < j) (hj : j ≤ m + 2) :
      A i j + B i (j + 1) = B i j + A (i + 1) j := by
    have hBj : ¬ (i = 0 ∧ j = m + 3) := by omega
    have hAi : ¬ (i + 1 = 0 ∧ j = m + 2) := by omega
    by_cases hcorner : i = 0 ∧ j = m + 2
    · rcases hcorner with ⟨rfl, rfl⟩
      have hcA : C 0 (m + 2) = -e (m + 2) := by dsimp [C, e]; rw [hclose]; abel
      have hcB : C 1 (m + 2) = -e (m + 2) + -e 0 := by
        dsimp [C, e]; rw [hclose]; abel
      have hcC : C 1 (m + 2 + 1) = -e 0 := by
        dsimp [C, e]; rw [show m + 2 + 1 = m + 3 by omega, hclose]; abel
      have hsum := oangle_toReal_add_through_sum o
        (neg_ne_zero.mpr (he (m + 2) (by omega))) (neg_ne_zero.mpr (he 0 (by omega)))
        (by simpa using hπ0)
      simp only [A, B, show m + 2 + 1 = m + 3 by omega, ite_eq_left (by omega : 0 = 0 ∧ m + 2 = m + 2),
        ite_eq_left (by omega : 0 = 0 ∧ m + 3 = m + 3), ite_eq_right (by omega : ¬ (0 = 0 ∧ m + 2 = m + 3)),
        ite_eq_right (by omega : ¬ (0 + 1 = 0 ∧ m + 2 = m + 2)), add_zero,
        show 0 + 1 = 1 from rfl, hcA, hcB, hcC]
      simpa only [ε, o.oangle_neg_neg] using hsum.symm
    · have hBnext : ¬ (i = 0 ∧ j + 1 = m + 3) := by omega
      simp only [A, B, ite_eq_right hcorner, ite_eq_right hBnext, ite_eq_right hBj, ite_eq_right hAi]
      exact oangle_toReal_square_of_disjoint_segments o
        (hdisj i j hij (by omega) hcorner)
  have hc := triangularGrid_cancellation A B E (m + 1) htriangle hsquare
  have hAboundary : (∑ j ∈ Finset.range (m + 2), A 0 (j + 1)) =
      (∑ j ∈ Finset.range (m + 1),
        (o.oangle (v (j + 1) - v 0) (v (j + 2) - v 0)).toReal) + ε := by
    rw [Finset.sum_range_succ]
    have hAterm : ∀ j ∈ Finset.range (m + 1), A 0 (j + 1) =
        (o.oangle (v (j + 1) - v 0) (v (j + 2) - v 0)).toReal := by
      intro j hj
      have : ¬ (0 = 0 ∧ j + 1 = m + 2) := by have := Finset.mem_range.mp hj; omega
      simp only [A, ite_eq_right this, C, Nat.add_assoc]
    rw [Finset.sum_congr rfl hAterm]
    simp [A]
  have hBboundary : (∑ i ∈ Finset.range (m + 2), B i (m + 3)) =
      (∑ j ∈ Finset.range (m + 1),
        (o.oangle (v (j + 1) - v 0) (v (j + 2) - v 0)).toReal) := by
    rw [Finset.sum_range_succ']
    have hBterm : ∀ i ∈ Finset.range (m + 1), B (i + 1) (m + 3) =
        (o.oangle (v (i + 1) - v 0) (v (i + 2) - v 0)).toReal := by
      intro i hi
      have : ¬ (i + 1 = 0 ∧ m + 3 = m + 3) := by omega
      simp only [B, ite_eq_right this, C, hclose]
      rw [show v 0 - v (i + 1) = -(v (i + 1) - v 0) by abel,
        show v 0 - v (i + 1 + 1) = -(v (i + 2) - v 0) by simp [Nat.add_assoc],
        o.oangle_neg_neg]
    rw [Finset.sum_congr rfl hBterm]
    simp [B]
  rw [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega,
    hAboundary, hBboundary] at hc
  have hE : (∑ i ∈ Finset.range (m + 2), E i) =
      (∑ i ∈ Finset.range (m + 2),
        (o.oangle (v (i + 1) - v i) (v (i + 2) - v (i + 1))).toReal) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [E, e, C, Nat.add_assoc]
  rw [hE] at hc
  dsimp [ε, e, C] at hc
  linarith


open Fin.NatCast
open P202Specs.PolygonTurning
variable {n : ℕ} [NeZero n]

def vertex (p : Polygon V n) (i : ℕ) : V := p (Nat.cast i : Fin n)
def chord (p : Polygon V n) (i j : ℕ) : V := vertex p j - vertex p i

@[simp] theorem vertex_zero (p : Polygon V n) : vertex p 0 = p 0 := rfl
@[simp] theorem vertex_period (p : Polygon V n) : vertex p n = p 0 := by
  simp [vertex]

theorem vertex_succ (p : Polygon V n) (i : ℕ) :
    vertex p (i+1) = p (finRotate n (Nat.cast i : Fin n)) := by
  simp [vertex, finRotate_apply, Nat.cast_add, Nat.cast_one]

@[simp] theorem chord_succ_eq_edgeVector (p : Polygon V n) (i : ℕ) :
    chord p i (i+1) = edgeVector p (Nat.cast i : Fin n) := by
  rw [chord, vertex_succ]
  rfl

theorem incomingVector_succ_eq_edgeVector (p : Polygon V n) (i : ℕ) :
    incomingVector p (Nat.cast (i+1) : Fin n) = edgeVector p (Nat.cast i : Fin n) := by
  have h : (Nat.cast (i+1) : Fin n) = finRotate n (Nat.cast i : Fin n) := by
    simp [finRotate_apply, Nat.cast_add, Nat.cast_one]
  rw [h, incomingVector, Equiv.symm_apply_apply]

theorem natural_segment_eq_edgeSet (p : Polygon V n) (i : ℕ) :
    segment ℝ (vertex p i) (vertex p (i+1)) = p.edgeSet ℝ (Nat.cast i : Fin n) := by
  rw [vertex_succ]
  simp only [vertex, Polygon.edgeSet, affineSegment_eq_segment]

theorem disjoint_natural_segments {p : Polygon V n} (hp : IsSimple p)
    {i j : ℕ} (hij : i+1 < j) (hj : j < n)
    (hclosing : ¬(i = 0 ∧ j = n-1)) :
    Disjoint (segment ℝ (vertex p i) (vertex p (i+1)))
      (segment ℝ (vertex p j) (vertex p (j+1))) := by
  have hi : i < n := by omega
  have hi1 : i+1 < n := by omega
  have hne : (Nat.cast i : Fin n) ≠ (Nat.cast j : Fin n) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv
    omega
  have hnext : finRotate n (Nat.cast i : Fin n) ≠ (Nat.cast j : Fin n) := by
    intro h
    rw [finRotate_apply, ← Nat.cast_one, ← Nat.cast_add] at h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natCast, Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hj] at hv
    omega
  have hprev : finRotate n (Nat.cast j : Fin n) ≠ (Nat.cast i : Fin n) := by
    intro h
    rw [finRotate_apply, ← Nat.cast_one, ← Nat.cast_add] at h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natCast, Nat.mod_eq_of_lt hi] at hv
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj) with hj1 | hj1
    · rw [Nat.mod_eq_of_lt hj1] at hv
      omega
    · apply hclosing
      constructor
      · have heq : j+1 = n := by omega
        rw [heq, Nat.mod_self] at hv
        exact hv.symm
      · omega
  rw [natural_segment_eq_edgeSet, natural_segment_eq_edgeSet]
  exact P202.PolygonTurning.disjoint_edgeSets_of_nonadjacent hp hne hnext hprev

theorem exteriorAngle_succ_eq {p : Polygon V n}
    (o : Orientation ℝ V (Fin 2)) (i : ℕ) :
    exteriorAngle o p (Nat.cast (i+1) : Fin n) =
      (o.oangle (chord p i (i+1)) (chord p (i+1) (i+2))).toReal := by
  rw [exteriorAngle, incomingVector_succ_eq_edgeVector, chord_succ_eq_edgeVector]
  have he := chord_succ_eq_edgeVector p (i+1)
  have h : i+1+1 = i+2 := by omega
  rw [h] at he
  rw [he]


theorem natural_chord_ne_zero {p : Polygon V n} (hp : p.HasNondegenerateEdges) (i : ℕ) :
    chord p i (i+1) ≠ 0 := by
  rw [chord_succ_eq_edgeVector]
  exact P202.PolygonTurning.edgeVector_ne_zero hp _

theorem natural_adjacent_oangle_ne_pi {p : Polygon V n}
    (o : Orientation ℝ V (Fin 2)) (hp : p.HasNondegenerateEdges) (hc : Noncuspidal p)
    (i : ℕ) :
    o.oangle (chord p i (i+1)) (chord p (i+1) (i+2)) ≠ (Real.pi : Real.Angle) := by
  have h := P202.PolygonTurning.oangle_ne_pi_of_noncuspidal o hp hc
    (Nat.cast (i+1) : Fin n)
  rw [incomingVector_succ_eq_edgeVector] at h
  rw [chord_succ_eq_edgeVector]
  have he := chord_succ_eq_edgeVector p (i+1)
  have hi : i+1+1 = i+2 := by omega
  rw [hi] at he
  rw [he]
  exact h

variable {m : ℕ}
theorem totalTurning_eq_initial_add_natural_sum (o : Orientation ℝ V (Fin 2))
    (p : Polygon V (m+3)) :
    totalTurning o p = exteriorAngle o p 0 +
      ∑ i ∈ Finset.range (m+2), exteriorAngle o p (Nat.cast (i+1) : Fin (m+3)) := by
  change (∑ i : Fin (m+3), exteriorAngle o p i) = _
  rw [Fin.sum_univ_succ]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Fin.ext
  simp only [Fin.val_succ, Fin.val_natCast]
  rw [Nat.mod_eq_of_lt (by omega)]


theorem incomingVector_zero (p : Polygon V (m+3)) :
    incomingVector p 0 = edgeVector p (Nat.cast (m+2) : Fin (m+3)) := by
  have hrot : finRotate (m+3) (Nat.cast (m+2) : Fin (m+3)) = 0 := by
    rw [finRotate_apply, ← Nat.cast_one, ← Nat.cast_add]
    have h : m+2+1 = m+3 := by omega
    simp [h]
  have hpred : (finRotate (m+3)).symm 0 = (Nat.cast (m+2) : Fin (m+3)) :=
    (finRotate (m+3)).symm_apply_eq.mpr hrot.symm
  rw [incomingVector, hpred]

theorem natural_closing_oangle_ne_pi {p : Polygon V (m+3)}
    (o : Orientation ℝ V (Fin 2)) (hp : p.HasNondegenerateEdges) (hc : Noncuspidal p) :
    o.oangle (chord p (m+2) (m+3)) (chord p 0 1) ≠ (Real.pi : Real.Angle) := by
  have h := P202.PolygonTurning.oangle_ne_pi_of_noncuspidal o hp hc (0 : Fin (m+3))
  rw [incomingVector_zero] at h
  have he : chord p (m+2) (m+3) = edgeVector p (Nat.cast (m+2) : Fin (m+3)) := by
    simpa only [Nat.add_assoc] using chord_succ_eq_edgeVector p (m+2)
  rw [he, chord_succ_eq_edgeVector]
  exact h

theorem exteriorAngle_zero_eq (o : Orientation ℝ V (Fin 2)) (p : Polygon V (m+3)) :
    exteriorAngle o p 0 =
      (o.oangle (chord p (m+2) (m+3)) (chord p 0 1)).toReal := by
  rw [exteriorAngle, incomingVector_zero]
  have he : chord p (m+2) (m+3) = edgeVector p (Nat.cast (m+2) : Fin (m+3)) := by
    simpa only [Nat.add_assoc] using chord_succ_eq_edgeVector p (m+2)
  rw [he, chord_succ_eq_edgeVector]
  rfl

theorem totalTurning_eq_initial_add_chord_sum (o : Orientation ℝ V (Fin 2))
    (p : Polygon V (m+3)) :
    totalTurning o p = exteriorAngle o p 0 +
      ∑ i ∈ Finset.range (m+2),
        (o.oangle (chord p i (i+1)) (chord p (i+1) (i+2))).toReal := by
  rw [totalTurning_eq_initial_add_natural_sum]
  simp_rw [exteriorAngle_succ_eq]



theorem polygon_secant_comparison (o : Orientation ℝ V (Fin 2))
    {m : ℕ} (p : Polygon V (m+3)) (hp : IsSimple p) (hc : Noncuspidal p) :
    totalTurning o p = 2 *
      ((∑ j ∈ Finset.range (m+1),
        (o.oangle (vertex p (j+1) - vertex p 0) (vertex p (j+2) - vertex p 0)).toReal)
        + exteriorAngle o p 0) := by
  have hclose : vertex p (m+3) = vertex p 0 := by simp
  have hne : ∀ i < m+3, vertex p (i+1) - vertex p i ≠ 0 := by
    intro i hi
    exact natural_chord_ne_zero hp.2.2.1 i
  have hturn : ∀ i < m+2,
      o.oangle (vertex p (i+1) - vertex p i)
        (vertex p (i+2) - vertex p (i+1)) ≠ (Real.pi : Real.Angle) := by
    intro i hi
    exact natural_adjacent_oangle_ne_pi o hp.2.2.1 hc i
  have hclosing : o.oangle (vertex p (m+3) - vertex p (m+2))
      (vertex p 1 - vertex p 0) ≠ (Real.pi : Real.Angle) := by
    exact natural_closing_oangle_ne_pi o hp.2.2.1 hc
  have hdisj : ∀ i j, i+1 < j → j < m+3 → ¬(i=0 ∧ j=m+2) →
      Disjoint (segment ℝ (vertex p i) (vertex p (i+1)))
        (segment ℝ (vertex p j) (vertex p (j+1))) := by
    intro i j hij hj hclosing
    apply disjoint_natural_segments hp hij hj
    simpa only [show m+3-1=m+2 by omega] using hclosing
  have h := closedArray_secant_comparison o m (vertex p) hclose hne hturn hclosing hdisj
  have htotal := totalTurning_eq_initial_add_chord_sum o p
  have hzero := exteriorAngle_zero_eq o p
  change totalTurning o p = exteriorAngle o p 0 +
    (∑ i ∈ Finset.range (m+2),
      (o.oangle (vertex p (i+1) - vertex p i)
        (vertex p (i+2) - vertex p (i+1))).toReal) at htotal
  change exteriorAngle o p 0 =
    (o.oangle (vertex p (m+3) - vertex p (m+2)) (vertex p 1 - vertex p 0)).toReal at hzero
  linarith


theorem radialAngleSum_eq_shortAngle (o : Orientation ℝ V (Fin 2))
    {m : ℕ} (p : Polygon V (m+3)) (a : V)
    (hmin : ∀ j : Fin (m+3), j ≠ 0 → inner ℝ a (p 0) < inner ℝ a (p j)) :
    (∑ j ∈ Finset.range (m+1),
      (o.oangle (vertex p (j+1) - vertex p 0) (vertex p (j+2) - vertex p 0)).toReal) =
    (o.oangle (edgeVector p 0) (-incomingVector p 0)).toReal := by
  have hpos (k : ℕ) (hk0 : 0 < k) (hkn : k < m+3) :
      0 < inner ℝ a (vertex p k - vertex p 0) := by
    have hk : (Nat.cast k : Fin (m+3)) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natCast, Nat.mod_eq_of_lt hkn, Fin.val_zero] at hv
      omega
    simp only [vertex, Nat.cast_zero, inner_sub_right]
    exact sub_pos.mpr (hmin _ hk)
  let f : ℕ → ℝ := fun j => (o.oangle a (vertex p (j+1) - vertex p 0)).toReal
  have hsum : (∑ j ∈ Finset.range (m+1),
      (o.oangle (vertex p (j+1) - vertex p 0) (vertex p (j+2) - vertex p 0)).toReal) =
      f (m+1) - f 0 := by
    rw [← Finset.sum_range_sub f (m+1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj : j < m+1 := Finset.mem_range.mp hj
    have hangle := oangle_toReal_eq_sub_of_common_halfplane o
      (hpos (j+1) (by omega) (by omega)) (hpos (j+2) (by omega) (by omega))
    simpa only [f, Nat.add_assoc] using hangle
  have hangle := oangle_toReal_eq_sub_of_common_halfplane o
    (hpos 1 (by omega) (by omega)) (hpos (m+2) (by omega) (by omega))
  have hback : vertex p (m+2) - vertex p 0 = -incomingVector p 0 := by
    rw [incomingVector_zero]
    have he : chord p (m+2) (m+3) = edgeVector p (Nat.cast (m+2) : Fin (m+3)) := by
      simpa only [Nat.add_assoc] using chord_succ_eq_edgeVector p (m+2)
    rw [← he]
    simp only [chord, vertex_period, vertex_zero]
    abel
  have hout : vertex p 1 - vertex p 0 = edgeVector p 0 := by
    exact chord_succ_eq_edgeVector p 0
  rw [hsum]
  have heq : f (m+1) - f 0 =
      (o.oangle (vertex p 1 - vertex p 0) (vertex p (m+2) - vertex p 0)).toReal := by
    simpa only [f, Nat.add_assoc, Nat.zero_add] using hangle.symm
  rw [heq, hback, hout]

theorem polygon_minimum_secant_comparison (o : Orientation ℝ V (Fin 2))
    {m : ℕ} (p : Polygon V (m+3)) (hp : IsSimple p) (hc : Noncuspidal p) (a : V)
    (hmin : ∀ j : Fin (m+3), j ≠ 0 → inner ℝ a (p 0) < inner ℝ a (p j)) :
    totalTurning o p = 2 *
      ((o.oangle (edgeVector p 0) (-incomingVector p 0)).toReal + exteriorAngle o p 0) := by
  rw [polygon_secant_comparison o p hp hc, radialAngleSum_eq_shortAngle o p a hmin]

end DiscreteSecant

/-- Signed shorter angles along any finite sequence in one open half-plane
telescope in its real principal chart; angular monotonicity is unnecessary. -/
theorem oangle_sum_of_rightHalfplane {m : ℕ} (v : V)
    (d : Fin (m + 1) → V) (hinner : ∀ i, 0 < inner ℝ v (d i)) :
    (∑ i : Fin m, (o.oangle (d i.castSucc) (d i.succ)).toReal) =
      (o.oangle (d 0) (d (Fin.last m))).toReal := by
  have hv : v ≠ 0 := by intro h; simpa [h] using hinner 0
  simp_rw [oangle_toReal_eq_sub_of_rightHalfplane o hv (hinner _) (hinner _)]
  rw [Finset.sum_sub_distrib]
  have hs := (Fin.sum_univ_succ (fun i => (o.oangle v (d i)).toReal)).symm.trans
    (Fin.sum_univ_castSucc (fun i => (o.oangle v (d i)).toReal))
  linarith

/-- The natural-number indexing form needed for the boundary row of the
finite secant grid. -/
theorem oangle_sum_range_of_rightHalfplane (v : V) (d : ℕ → V) (m : ℕ)
    (hinner : ∀ i ≤ m, 0 < inner ℝ v (d i)) :
    (∑ i ∈ Finset.range m, (o.oangle (d i) (d (i + 1))).toReal) =
      (o.oangle (d 0) (d m)).toReal := by
  have hv : v ≠ 0 := by intro h; simpa [h] using hinner 0 (Nat.zero_le m)
  calc
    _ = ∑ i ∈ Finset.range m,
        ((o.oangle v (d (i + 1))).toReal - (o.oangle v (d i)).toReal) := by
      apply Finset.sum_congr rfl
      intro i hi
      have him : i < m := Finset.mem_range.mp hi
      exact oangle_toReal_eq_sub_of_rightHalfplane o hv
        (hinner i him.le) (hinner (i + 1) (Nat.succ_le_of_lt him))
    _ = (o.oangle v (d m)).toReal - (o.oangle v (d 0)).toReal :=
      Finset.sum_range_sub (fun i => (o.oangle v (d i)).toReal) m
    _ = _ := (oangle_toReal_eq_sub_of_rightHalfplane o hv
      (hinner 0 (Nat.zero_le m)) (hinner m le_rfl)).symm


/-- Cyclically start the polygon at its positive minimum vertex. -/
theorem exists_rotated_positive_minimum (o : Orientation ℝ V (Fin 2))
    {p : Polygon V n} (hp : IsSimple p) {U : Set V}
    (hU : IsBoundedSide p U) (hleft : HasBoundedSideOnLeft o p U) :
    ∃ (_ : NeZero n) (v : V) (i : Fin n), v ≠ 0 ∧
      (∀ j : Fin n, j ≠ 0 →
        inner ℝ v (rotate p i 0) < inner ℝ v (rotate p i j)) ∧
      exteriorAngle o (rotate p i) 0 ∈ Ioo (0 : ℝ) Real.pi := by
  have : NeZero n := ⟨by have := hp.1; omega⟩
  refine ⟨inferInstance, ?_⟩
  obtain ⟨v, i, hv, _, hmin, hε⟩ := exists_positive_minimum_turn o hp hU hleft
  refine ⟨v, i, hv, ?_, ?_⟩
  · intro j hj
    change inner ℝ v (p (0+i)) < inner ℝ v (p (j+i))
    rw [zero_add]
    exact hmin (j+i) (by simpa only [ne_eq, add_eq_right] using hj)
  · simpa only [exteriorAngle_rotate, zero_add] using hε


/-- Three rays occurring in order inside the same open half-plane give
additivity of their smaller unsigned angles. -/
theorem angle_add_of_oangle_sign_pos {x y z : V}
    (hxy : (o.oangle x y).sign = 1) (hyz : (o.oangle y z).sign = 1)
    (hxz : (o.oangle x z).sign = 1) :
    InnerProductGeometry.angle x y + InnerProductGeometry.angle y z =
      InnerProductGeometry.angle x z := by
  have hx := o.left_ne_zero_of_oangle_sign_eq_one hxy
  have hy := o.right_ne_zero_of_oangle_sign_eq_one hxy
  have hz := o.right_ne_zero_of_oangle_sign_eq_one hyz
  have hπxy : o.oangle x y ≠ (Real.pi : Real.Angle) := by
    intro h
    simp [h] at hxy
  have hπyz : o.oangle y z ≠ (Real.pi : Real.Angle) := by
    intro h
    simp [h] at hyz
  rw [o.angle_eq_abs_oangle_toReal hx hy, o.angle_eq_abs_oangle_toReal hy hz,
    o.angle_eq_abs_oangle_toReal hx hz,
    abs_of_nonneg (Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr hxy).1.le,
    abs_of_nonneg (Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr hyz).1.le,
    abs_of_nonneg (Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr hxz).1.le]
  have hadd := o.oangle_add hx hy hz
  rw [← hadd]
  exact (Real.Angle.toReal_add_eq_toReal_add_toReal hπxy hπyz
    (Or.inr (by rw [hadd, hxy, hxz]))).symm

/-- A positive combination of the two rays lies between them within their
convex sector, so splitting the sector along it preserves its unsigned angle. -/
theorem angle_add_of_positive_combination {x z : V} {a b : ℝ}
    (hxz : (o.oangle x z).sign = 1) (ha : 0 < a) (hb : 0 < b) :
    InnerProductGeometry.angle x (a • x + b • z) +
      InnerProductGeometry.angle (a • x + b • z) z =
      InnerProductGeometry.angle x z := by
  apply angle_add_of_oangle_sign_pos o
  · rw [o.oangle_sign_smul_add_smul_right, hxz, sign_pos hb, one_mul]
  · rw [o.oangle_sign_smul_add_smul_left, hxz, sign_pos ha, one_mul]
  · exact hxz

/-- Within a common convex sector of aperture at most π, an increasing pair
of principal angles has unsigned angular distance equal to their difference. -/
theorem angle_eq_sub_of_ordered_principal_angles {a x y : V}
    (ha : a ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hx0 : 0 ≤ (o.oangle a x).toReal)
    (hxy : (o.oangle a x).toReal ≤ (o.oangle a y).toReal) :
    InnerProductGeometry.angle x y =
      (o.oangle a y).toReal - (o.oangle a x).toReal := by
  let t := (o.oangle a y).toReal - (o.oangle a x).toReal
  have ht0 : 0 ≤ t := sub_nonneg.mpr hxy
  have htπ : t ≤ Real.pi := by
    dsimp [t]
    linarith [Real.Angle.toReal_le_pi (o.oangle a y)]
  have ht : ((t : ℝ) : Real.Angle) = o.oangle x y := by
    dsimp [t]
    rw [Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    exact o.oangle_sub_left ha hx hy
  rw [o.angle_eq_abs_oangle_toReal hx hy, ← ht,
    (Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos], htπ⟩),
    abs_of_nonneg ht0]

/-- Telescoping the actual unsigned angles of a finite ordered fan.  The
monotone principal angles put every ray in the same closed semicircle based
at its first ray; repeated rays and the endpoint angle π are allowed. -/
theorem fanAngle_sum_of_monotone_principal_angles {m : ℕ}
    (d : Fin (m + 1) → V) (hd : ∀ i, d i ≠ 0)
    (hmono : Monotone (fun i => (o.oangle (d 0) (d i)).toReal)) :
    (∑ i : Fin m, InnerProductGeometry.angle (d i.castSucc) (d i.succ)) =
      InnerProductGeometry.angle (d 0) (d (Fin.last m)) := by
  let f : Fin (m + 1) → ℝ := fun i => (o.oangle (d 0) (d i)).toReal
  have hf0 : f 0 = 0 := by simp [f]
  have hfnonneg (i : Fin (m + 1)) : 0 ≤ f i := by
    rw [← hf0]
    exact hmono (Fin.zero_le _)
  have hstep (i : Fin m) :
      InnerProductGeometry.angle (d i.castSucc) (d i.succ) =
        f i.succ - f i.castSucc :=
    angle_eq_sub_of_ordered_principal_angles o (hd 0) (hd _) (hd _)
      (hfnonneg _) (hmono (Fin.castSucc_le_succ i))
  simp_rw [hstep]
  rw [Finset.sum_sub_distrib]
  have hs := (Fin.sum_univ_succ f).symm.trans (Fin.sum_univ_castSucc f)
  rw [o.angle_eq_abs_oangle_toReal (hd _) (hd _),
    abs_of_nonneg (hfnonneg (Fin.last m))]
  change (∑ i : Fin m, f i.succ) - (∑ i : Fin m, f i.castSucc) = f (Fin.last m)
  linarith

/-- Strict angular ordering inside a common sector is a special case of the
fan sum theorem. -/
theorem fanAngle_sum_of_strictMono_principal_angles {m : ℕ}
    (d : Fin (m + 1) → V) (hd : ∀ i, d i ≠ 0)
    (hmono : StrictMono (fun i => (o.oangle (d 0) (d i)).toReal)) :
    (∑ i : Fin m, InnerProductGeometry.angle (d i.castSucc) (d i.succ)) =
      InnerProductGeometry.angle (d 0) (d (Fin.last m)) :=
  fanAngle_sum_of_monotone_principal_angles o d hd hmono.monotone

/-- In a common angular chart of width π, taking a principal difference
commutes with `toReal`; neither ordering nor an angle sum is assumed. -/
theorem oangle_toReal_eq_sub_of_common_sector {a x y : V}
    (ha : a ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxsector : (o.oangle a x).toReal ∈ Ico (0 : ℝ) Real.pi)
    (hysector : (o.oangle a y).toReal ∈ Ico (0 : ℝ) Real.pi) :
    (o.oangle x y).toReal =
      (o.oangle a y).toReal - (o.oangle a x).toReal := by
  let t := (o.oangle a y).toReal - (o.oangle a x).toReal
  have htlo : -Real.pi < t := by dsimp [t]; linarith [hxsector.2, hysector.1]
  have hthi : t ≤ Real.pi := by dsimp [t]; linarith [hxsector.1, hysector.2]
  have ht : ((t : ℝ) : Real.Angle) = o.oangle x y := by
    dsimp [t]
    rw [Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    exact o.oangle_sub_left ha hx hy
  rw [← ht]
  exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨htlo, hthi⟩

/-- A finite list of nonzero rays whose successive oriented angles are
positive and which all lie in the same convex sector gives an unsigned fan
sum equal to its endpoint angle. These are local geometric ordering inputs,
not a fan-sum certificate. -/
theorem fanAngle_sum_of_positive_order {m : ℕ}
    (d : Fin (m + 1) → V) (hd : ∀ i, d i ≠ 0)
    (hsector : ∀ i, (o.oangle (d 0) (d i)).toReal ∈ Ico (0 : ℝ) Real.pi)
    (hstep : ∀ i : Fin m, (o.oangle (d i.castSucc) (d i.succ)).sign = 1) :
    (∑ i : Fin m, InnerProductGeometry.angle (d i.castSucc) (d i.succ)) =
      InnerProductGeometry.angle (d 0) (d (Fin.last m)) := by
  apply fanAngle_sum_of_strictMono_principal_angles o d hd
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have h := (Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr (hstep i)).1
  rw [oangle_toReal_eq_sub_of_common_sector o (hd 0) (hd _) (hd _)
    (hsector _) (hsector _)] at h
  linarith


/-- The actual unsigned angle at a corner of a straight triangle. -/
def triangleAngle (t : Fin 3 → V) (i : Fin 3) : ℝ :=
  EuclideanGeometry.angle (t ((finRotate 3).symm i)) (t i) (t (finRotate 3 i))

omit [Fact (Module.finrank ℝ V = 2)] in
/-- The triangle-angle sum used in the source is a real equality, not an
equality only in the circle of angles. -/
theorem triangleAngle_sum (t : Fin 3 → V) (ht : Function.Injective t) :
    ∑ i, triangleAngle t i = Real.pi := by
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (t 2)
    (ht.ne (by decide : (1 : Fin 3) ≠ 0))
  simpa [triangleAngle, Fin.sum_univ_three, show (-1 : Fin 3) = 2 by decide,
    add_comm, add_left_comm, add_assoc]
    using h

omit [Fact (Module.finrank ℝ V = 2)] in
/-- All corners of all triangles, grouped by their actual vertex indices.
This is a double count; it makes no unproved local angle-fan assertion. -/
theorem triangleAngles_by_vertex {N F : ℕ} (x : Fin N → V)
    (face : Fin F → Fin 3 → Fin N)
    (hface : ∀ f, Function.Injective (x ∘ face f)) :
    (∑ v : Fin N, ∑ f : Fin F, ∑ i : Fin 3,
      if face f i = v then triangleAngle (x ∘ face f) i else 0) = Real.pi * (F : ℝ) := by
  classical
  calc
    _ = ∑ f : Fin F, ∑ i : Fin 3, ∑ v : Fin N,
        if face f i = v then triangleAngle (x ∘ face f) i else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.sum_comm]
    _ = ∑ f : Fin F, ∑ i : Fin 3, triangleAngle (x ∘ face f) i := by simp
    _ = Real.pi * (F : ℝ) := by
      simp only [triangleAngle_sum _ (hface _), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Deduce the global angle accounting from local fans of actual triangles.
The first `Vb` vertex indices are boundary vertices and the rest are interior
vertices. Proving those local fan hypotheses from a geometric triangulation
remains separate work. -/
theorem fanAngleSum {Vb Vi F : ℕ} (x : Fin (Vb + Vi) → V)
    (face : Fin F → Fin 3 → Fin (Vb + Vi))
    (hface : ∀ f, Function.Injective (x ∘ face f)) (α : Fin Vb → ℝ)
    (hboundary : ∀ v : Fin Vb,
      (∑ f : Fin F, ∑ i : Fin 3, if face f i = v.castAdd Vi then
        triangleAngle (x ∘ face f) i else 0) = α v)
    (hinterior : ∀ v : Fin Vi,
      (∑ f : Fin F, ∑ i : Fin 3, if face f i = v.natAdd Vb then
        triangleAngle (x ∘ face f) i else 0) = 2 * Real.pi) :
    (∑ v, α v) + 2 * Real.pi * (Vi : ℝ) = Real.pi * (F : ℝ) := by
  classical
  have h := triangleAngles_by_vertex x face hface
  rw [Fin.sum_univ_add] at h
  simp only [hboundary, hinterior, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  nlinarith [h]

/-- Counting the three sides of each face by their global edge indices.
Each interior edge must actually have two incident face sides, and each
boundary edge one. These are the precise incidence hypotheses needed for
the combinatorial identity; no planarity certificate is assumed or created. -/
theorem triangleEdgeCount {Ei Eb F : ℕ}
    (side : Fin F × Fin 3 → Fin (Ei + Eb))
    (hinterior : ∀ e : Fin Ei, Nat.card {a // side a = e.castAdd Eb} = 2)
    (hboundary : ∀ e : Fin Eb, Nat.card {a // side a = e.natAdd Ei} = 1) :
    3 * F = 2 * Ei + Eb := by
  classical
  have hcard : Fintype.card (Fin F × Fin 3) =
      Fintype.card (Σ e, {a // side a = e}) :=
    Fintype.card_congr (Equiv.sigmaFiberEquiv side).symm
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  have hf (e : Fin (Ei + Eb)) : Fintype.card {a // side a = e} =
      Nat.card {a // side a = e} := (Nat.card_eq_fintype_card).symm
  simp_rw [hf] at hcard
  rw [Fin.sum_univ_add] at hcard
  simp only [hinterior, hboundary, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hcard
  omega

/-- The algebraic count in paper.tex 4902–4911, isolated from the geometric
construction. The fan angle equality and edge incidence counts are explicit
inputs of this helper only; they are not assumptions of `Expected.turning`.
The counts allow inserted straight boundary vertices and interior vertices. -/
theorem angleAccounting (Vb Vi Ei Eb F : ℕ) (α : Fin Vb → ℝ)
    (hfan : (∑ i, α i) + 2 * Real.pi * (Vi : ℝ) = Real.pi * (F : ℝ))
    (hincidence : 3 * F = 2 * Ei + Eb) (hboundary : Eb = Vb) :
    (∑ i, (Real.pi - α i)) =
      2 * Real.pi * ((Vi : ℝ) + (Vb : ℝ) - (Ei : ℝ) - (Eb : ℝ) + (F : ℝ)) := by
  have hi : (3 : ℝ) * (F : ℝ) = 2 * (Ei : ℝ) + (Eb : ℝ) := by
    exact_mod_cast hincidence
  have hb : (Eb : ℝ) = (Vb : ℝ) := by exact_mod_cast hboundary
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination -hfan - Real.pi * hi + Real.pi * hb

/-- The Euler-value specialization, still with all geometric work exposed
in the helper's hypotheses. No original target is defined from this lemma. -/
theorem angleAccounting_disk (Vb Vi Ei Eb F : ℕ) (α : Fin Vb → ℝ)
    (hfan : (∑ i, α i) + 2 * Real.pi * (Vi : ℝ) = Real.pi * (F : ℝ))
    (hincidence : 3 * F = 2 * Ei + Eb) (hboundary : Eb = Vb)
    (heuler : (Vi : ℤ) + (Vb : ℤ) - (Ei : ℤ) - (Eb : ℤ) + (F : ℤ) = 1) :
    (∑ i, (Real.pi - α i)) = 2 * Real.pi := by
  have he : (Vi : ℝ) + (Vb : ℝ) - (Ei : ℝ) - (Eb : ℝ) + (F : ℝ) = 1 := by
    exact_mod_cast heuler
  rw [angleAccounting Vb Vi Ei Eb F α hfan hincidence hboundary, he, mul_one]

/-- Reversal negates the actual signed turning sum for every nondegenerate
noncuspidal closed polygon, without simplicity or Euler assumptions. -/
theorem reversal : P202Specs.PolygonTurning.Expected.reversal.{u} := by
  intro V _ _ _ n p o he hc
  exact totalTurning_reverse o he hc

/-- The signed exterior-angle sum of the actual positively traversed simple
closed polygon is 2π, including reflex and inserted straight vertices.
The proof cancels the finite secant grid and determines its sign at a
projection-minimal vertex using the original bounded-side-on-left condition. -/
theorem turning : P202Specs.PolygonTurning.Expected.turning.{u} := by
  intro V _ _ _ n p o U hp hc hU hleft
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by have := hp.1; omega⟩
  obtain ⟨_, v, i, hv, hmin, _⟩ := exists_rotated_positive_minimum o hp hU hleft
  have hp' := isSimple_rotate hp i
  have hc' := noncuspidal_rotate hc i
  have hU' := isBoundedSide_rotate hU i
  have hleft' := hasBoundedSideOnLeft_rotate o hleft i
  have hs := DiscreteSecant.polygon_minimum_secant_comparison o (rotate p i) hp' hc' v hmin
  have ha := minimum_shortAngle_add_exteriorAngle o v hv hp' hU' hleft' 0 hmin
  have ht : totalTurning o p = 2 * Real.pi := by
    rw [← totalTurning_rotate o p i, hs, ha]
  exact ⟨ht, by rw [totalTurning_reverse o hp.2.2.1 hc, ht]⟩


end P202.PolygonTurning
