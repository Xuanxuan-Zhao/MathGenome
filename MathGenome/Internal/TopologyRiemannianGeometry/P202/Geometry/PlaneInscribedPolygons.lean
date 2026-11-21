import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneInscribedPolygons
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionCornerCollar
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionComponents
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlaneTurningData
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PolygonTurning
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.FineInscribedCollarGraphs
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.TransversePolygonGraphTransport
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Geometry and approximation estimates for the literal inscribed polygon.
Every sufficiently fine knot-preserving partition gives a simple noncuspidal
polygon with its actual bounded side on the left. The transverse collar graph
and its ambient transport supply orientation preservation.
-/
noncomputable section
open Set
open scoped unitInterval ContDiff

namespace P202.PlaneInscribedPolygons
open P202Specs.PlaneTurning
open P202Specs.PlanarRegionTopology (Plane ParameterCircle RegularJordanCurve realLift)

lemma partition_time_mem (Q : Partition) (i : Fin (Q.count + 1)) :
    Q.time i ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [← Q.first]
    exact Q.strictMono.monotone (Fin.zero_le i)
  · rw [← Q.last]
    exact Q.strictMono.monotone (Fin.le_last i)

lemma partition_vertex_time_mem (Q : Partition) (i : Fin Q.count) :
    Q.time i.castSucc ∈ Ico (0 : ℝ) 1 := by
  refine ⟨(partition_time_mem Q i.castSucc).1, ?_⟩
  rw [← Q.last]
  exact Q.strictMono (by exact i.isLt)

lemma realLift_injective_on_period (c : RegularJordanCurve) :
    InjOn (realLift c.parametrization) (Ico (0 : ℝ) 1) := by
  intro s hs t ht h
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ))
    (by simpa using hs) (by simpa using ht)).mp
  exact c.injective h

lemma vertices_injective (c : RegularJordanCurve) (Q : Partition) :
    Function.Injective (inscribedPolygon c Q).vertices := by
  intro i j h
  apply Fin.castSucc_injective
  apply Q.strictMono.injective
  exact realLift_injective_on_period c (partition_vertex_time_mem Q i)
    (partition_vertex_time_mem Q j) h

/-- At the last edge, parameter 1 is the same circle point as parameter 0. -/
lemma next_vertex (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count) :
    inscribedVertex c Q (finRotate Q.count i) =
      realLift c.parametrization (Q.time i.succ) := by
  have general : ∀ (n : ℕ) (i : Fin n),
      (finRotate n i).castSucc = i.succ ∨
      ((finRotate n i).castSucc = 0 ∧ i.succ = Fin.last n) := by
    intro n i
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      by_cases hi : i = Fin.last n
      · right
        subst i
        simp
      · left
        apply Fin.ext
        exact coe_finRotate_of_ne_last hi
  have hrot := general Q.count i
  rcases hrot with h | ⟨hzero, hlast⟩
  · simp only [inscribedVertex, h]
  · simp only [inscribedVertex, hzero, hlast, Q.first, Q.last, realLift]
    congr 1
    exact (AddCircle.coe_period (1 : ℝ)).symm

lemma edgeVector_eq (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count) :
    P202Specs.PolygonTurning.edgeVector (inscribedPolygon c Q) i =
      inscribedEdge c Q i := by
  exact congrArg (fun v => v - inscribedVertex c Q i) (next_vertex c Q i)

lemma edges_nondegenerate (c : RegularJordanCurve) (Q : Partition) :
    (inscribedPolygon c Q).HasNondegenerateEdges := by
  intro i h
  have hi := vertices_injective c Q h
  have nofixed : ∀ (n : ℕ), 3 ≤ n → ∀ i : Fin n, i ≠ finRotate n i := by
    intro n hn i
    cases n with
    | zero => omega
    | succ n =>
      intro heq
      have hv := congrArg Fin.val heq
      rw [coe_finRotate] at hv
      split_ifs at hv with hlast
      · have hi' := congrArg Fin.val hlast
        simp only [Fin.val_last] at hi'
        omega
      · omega
  exact nofixed Q.count Q.at_least_three i hi

lemma edgePath_eq (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count)
    (t : unitInterval) :
    (inscribedPolygon c Q).edgePath ℝ i t = inscribedEdgeMap c Q i t := by
  change AffineMap.lineMap (inscribedVertex c Q i)
    (inscribedVertex c Q (finRotate Q.count i)) (t : ℝ) = _
  rw [next_vertex]
  simp [AffineMap.lineMap_apply_module, inscribedEdgeMap, inscribedEdge]
  module

lemma boundary_eq_trace (c : RegularJordanCurve) (Q : Partition) :
    (inscribedPolygon c Q).boundary ℝ = inscribedTrace c Q := by
  apply iUnion_congr
  intro i
  rw [Polygon.edgeSet_eq_image_edgePath]
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, (edgePath_eq c Q i ⟨t, ht⟩).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.property, edgePath_eq c Q i t⟩

theorem vertexGeometry : InscribedExpected.vertexGeometry := by
  intro c Q
  exact ⟨vertices_injective c Q, edges_nondegenerate c Q, edgeVector_eq c Q,
    edgePath_eq c Q, boundary_eq_trace c Q⟩

/-- Each point of an edge is no farther from its initial vertex than the
edge length. This estimate also applies to the closing edge. -/
lemma edgeMap_dist_vertex_le (c : RegularJordanCurve) (Q : Partition)
    (i : Fin Q.count) (t : unitInterval) :
    dist (inscribedEdgeMap c Q i t) (inscribedVertex c Q i) ≤
      dist (realLift c.parametrization (Q.time i.succ)) (inscribedVertex c Q i) := by
  rw [dist_eq_norm, inscribedEdgeMap, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg t.property.1, dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg _) t.property.2

lemma edgeParameter_mem (Q : Partition) (i : Fin Q.count) (t : unitInterval) :
    Q.time i.castSucc + (Q.time i.succ - Q.time i.castSucc) * t ∈
      Icc (Q.time i.castSucc) (Q.time i.succ) := by
  have hi : Q.time i.castSucc < Q.time i.succ := Q.strictMono (by simp)
  constructor
  · nlinarith [t.property.1]
  · nlinarith [t.property.2]

/-- Heine--Cantor gives one threshold for all affine edge points, with no
extra geometric certificate in the partitions. -/
theorem uniformApproximation : InscribedExpected.uniformApproximation := by
  intro c ε hε
  have hc : Continuous (realLift c.parametrization) :=
    c.parametrization.continuous.comp continuous_quotient_mk'
  have hu : UniformContinuousOn (realLift c.parametrization) (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 3) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro Q hmesh i t
  let a := Q.time i.castSucc
  let b := Q.time i.succ
  let s := a + (b - a) * (t : ℝ)
  have hab : a < b := Q.strictMono (by simp)
  have hs : s ∈ Icc a b := edgeParameter_mem Q i t
  have ha01 := partition_time_mem Q i.castSucc
  have hb01 := partition_time_mem Q i.succ
  have hs01 : s ∈ Icc (0 : ℝ) 1 :=
    ⟨ha01.1.trans hs.1, hs.2.trans hb01.2⟩
  have hba : dist b a < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hab)]
    exact hmesh i
  have has : dist a s < δ := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.1])]
    have hgap := hmesh i
    change b - a < δ at hgap
    linarith [hs.2]
  have hchord := hdist b hb01 a ha01 hba
  have hsample := hdist a ha01 s hs01 has
  have hpoly := edgeMap_dist_vertex_le c Q i t
  change dist (inscribedEdgeMap c Q i t) (realLift c.parametrization a) ≤
    dist (realLift c.parametrization b) (realLift c.parametrization a) at hpoly
  calc
    dist (inscribedEdgeMap c Q i t) (realLift c.parametrization s) ≤
        dist (inscribedEdgeMap c Q i t) (realLift c.parametrization a) +
        dist (realLift c.parametrization a) (realLift c.parametrization s) :=
      dist_triangle _ _ _
    _ < ε := by linarith

/-- Uniform continuity of the inverse Jordan parametrization. The metric
is on the parameter circle, so this includes neighborhoods crossing the cut. -/
lemma inverse_parameter_modulus (c : RegularJordanCurve) (η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s t : ParameterCircle,
      dist (c.parametrization s) (c.parametrization t) < ρ → dist s t < η := by
  have he : Topology.IsEmbedding c.parametrization :=
    (c.parametrization.continuous.isClosedEmbedding c.injective).isEmbedding
  let e := he.toHomeomorph
  have : CompactSpace (range c.parametrization) :=
    isCompact_iff_compactSpace.mp (isCompact_range c.parametrization.continuous)
  have hu := CompactSpace.uniformContinuous_of_continuous e.symm.continuous
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.uniformContinuous_iff.mp hu η hη
  refine ⟨ρ, hρ, ?_⟩
  intro s t h
  have hh := hsmall (a := e s) (b := e t) h
  simpa using hh

lemma short_edges (c : RegularJordanCurve) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ → ∀ i : Fin Q.count,
      dist (realLift c.parametrization (Q.time i.succ)) (inscribedVertex c Q i) < ε := by
  have hc : Continuous (realLift c.parametrization) :=
    c.parametrization.continuous.comp continuous_quotient_mk'
  have hu : UniformContinuousOn (realLift c.parametrization) (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ, ?_⟩
  intro Q hmesh i
  exact hdist _ (partition_time_mem Q i.succ) _ (partition_time_mem Q i.castSucc) (by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr (Q.strictMono (by simp)))]
    exact hmesh i)

/-- A collision of sufficiently short edges forces their starting parameters
into one small circle neighborhood. No simplicity assumption is used. -/
theorem intersectingEdgesLocalize : InscribedExpected.intersectingEdgesLocalize := by
  intro c η hη
  obtain ⟨ρ, hρ, hinv⟩ := inverse_parameter_modulus c η hη
  obtain ⟨δ, hδ, hshort⟩ := short_edges c (ρ / 3) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro Q hmesh i j s t heq
  apply hinv
  change dist (inscribedVertex c Q i) (inscribedVertex c Q j) < ρ
  have hi := (edgeMap_dist_vertex_le c Q i s).trans_lt (hshort Q hmesh i)
  have hj := (edgeMap_dist_vertex_le c Q j t).trans_lt (hshort Q hmesh j)
  have htri := dist_triangle (inscribedVertex c Q i)
    (inscribedEdgeMap c Q i s) (inscribedVertex c Q j)
  rw [dist_comm (inscribedVertex c Q i) (inscribedEdgeMap c Q i s), heq] at htri
  rw [heq] at hi
  linarith

/-- The strict projection order in a graph chart excludes intersections
between the interior of an earlier chord and a later closed chord. -/
lemma disjoint_openSegment_segment_of_projection_order (L : Plane →L[ℝ] ℝ)
    {a b c d : Plane} (hab : L a < L b) (hbc : L b ≤ L c) (hcd : L c ≤ L d) :
    Disjoint (openSegment ℝ a b) (segment ℝ c d) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' : L x < L b := by
    obtain ⟨α, β, hα, hβ, hsum, rfl⟩ := hx
    simp only [map_add, map_smul, smul_eq_mul]
    have hβeq : β = 1 - α := by linarith
    rw [hβeq]
    nlinarith [mul_pos hα (sub_pos.mpr hab)]
  have hy' : L c ≤ L x := by
    obtain ⟨α, β, hα, hβ, hsum, rfl⟩ := hy
    simp only [map_add, map_smul, smul_eq_mul]
    have hαeq : α = 1 - β := by linarith
    rw [hαeq]
    nlinarith [mul_nonneg hβ (sub_nonneg.mpr hcd)]
  linarith

/-- A common strictly positive projection excludes opposite normalized
vectors. No angle or sign of a corner is assumed. -/
lemma normalize_ne_neg_of_projection_pos (L : Plane →L[ℝ] ℝ) {u v : Plane}
    (hu : 0 < L u) (hv : 0 < L v) :
    NormedSpace.normalize u ≠ -NormedSpace.normalize v := by
  have hune : u ≠ 0 := by intro h; simp [h] at hu
  have hvne : v ≠ 0 := by intro h; simp [h] at hv
  have hnu : 0 < L (NormedSpace.normalize u) := by
    simp only [NormedSpace.normalize, map_smul, smul_eq_mul]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hune)) hu
  have hnv : 0 < L (NormedSpace.normalize v) := by
    simp only [NormedSpace.normalize, map_smul, smul_eq_mul]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hvne)) hv
  intro h
  have he := congrArg L h
  rw [map_neg] at he
  linarith

/-- A uniform increasing-projection radius on a full period, obtained from
the actual noncuspidal joins and compactness. -/
lemma uniform_projection_radius (c : RegularJordanCurve) :
    ∃ η : ℝ, 0 < η ∧ ∀ s ∈ Icc (0 : ℝ) 1,
      ∃ L : Plane →L[ℝ] ℝ,
        StrictMonoOn (fun t => L (realLift c.parametrization t)) (Icc (s - η) (s + η)) := by
  choose ε a hε ha hm using P202.PlanarRegionTopology.cornerProjection c
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric
    (s := Icc (0 : ℝ) 1) (c := fun t : ℝ => Ioo (t - ε t) (t + ε t))
    isCompact_Icc (fun _ => isOpen_Ioo) (by
      intro t ht
      exact mem_iUnion.mpr ⟨t, by constructor <;> linarith [hε t]⟩)
  refine ⟨δ / 2, by positivity, ?_⟩
  intro s hs
  obtain ⟨t, ht⟩ := hcover s hs
  refine ⟨innerSL ℝ (a t), (hm t).mono ?_⟩
  intro x hx
  have hball : x ∈ Metric.ball s δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact ⟨(ht hball).1.le, (ht hball).2.le⟩

/-- The real lift is unchanged under every integer parameter shift. -/
lemma realLift_int_shift (c : RegularJordanCurve) (s : ℝ) (k : ℤ) :
    realLift c.parametrization (s + k) = realLift c.parametrization s := by
  have hp : Function.Periodic (realLift c.parametrization) 1 := by
    intro t
    simp [realLift]
  simpa using hp.int_mul k s

/-- Close circle parameters have close real lifts after an integer shift. -/
lemma circle_close_lifts {s t η : ℝ}
    (h : dist (s : ParameterCircle) (t : ParameterCircle) ≤ η) :
    ∃ k : ℤ, dist (t + k) s ≤ η := by
  have hh : t ∈ ((↑) : ℝ → ParameterCircle) ⁻¹'
      Metric.closedBall (s : ParameterCircle) η := by
    exact (dist_comm _ _).le.trans h
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hh
  obtain ⟨k, hk⟩ := mem_iUnion.mp hh
  refine ⟨-k, ?_⟩
  simpa only [Metric.mem_closedBall, zsmul_eq_mul, mul_one, Int.cast_neg,
    Real.dist_eq, sub_add_eq_sub_sub, ← sub_eq_add_neg, sub_right_comm] using hk

/-- Distinct edges retain ordered parameter intervals after every integer shift. -/
lemma edge_parameter_order (Q : Partition) {i j : Fin Q.count} (hij : i ≠ j) (k : ℤ) :
    Q.time i.succ ≤ Q.time j.castSucc + k ∨
      Q.time j.succ + k ≤ Q.time i.castSucc := by
  have hi := partition_time_mem Q i.succ
  have hj := partition_time_mem Q j.castSucc
  have hi' := partition_time_mem Q i.castSucc
  have hj' := partition_time_mem Q j.succ
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · right
    have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    linarith [hi'.1, hj'.2]
  · simp only [Int.cast_zero, add_zero]
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · left
      exact Q.strictMono.monotone (by exact hij')
    · right
      exact Q.strictMono.monotone (by exact hij')
  · left
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    linarith [hi.2, hj.1]

/-- Either scalar interval order separates an open chord from a closed chord. -/
lemma disjoint_chords_of_projection_order (L : Plane →L[ℝ] ℝ)
    {a b c d : Plane} (hab : L a < L b) (hcd : L c < L d)
    (horder : L b ≤ L c ∨ L d ≤ L a) :
    Disjoint (openSegment ℝ a b) (segment ℝ c d) := by
  rcases horder with h | h
  · exact disjoint_openSegment_segment_of_projection_order L hab h hcd.le
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : L a < L x := by
      obtain ⟨α, β, hα, hβ, hsum, rfl⟩ := hx
      simp only [map_add, map_smul, smul_eq_mul]
      have hαeq : α = 1 - β := by linarith
      rw [hαeq]
      nlinarith [mul_pos hβ (sub_pos.mpr hab)]
    have hy' : L x ≤ L d := by
      obtain ⟨α, β, hα, hβ, hsum, rfl⟩ := hy
      simp only [map_add, map_smul, smul_eq_mul]
      have hβeq : β = 1 - α := by linarith
      rw [hβeq]
      nlinarith [mul_nonneg hα (sub_nonneg.mpr hcd.le)]
    linarith

/-- The upstream edge is the literal segment, including at the cyclic cut. -/
lemma edgeSet_eq_segment (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count) :
    (inscribedPolygon c Q).edgeSet ℝ i =
      segment ℝ (inscribedVertex c Q i) (realLift c.parametrization (Q.time i.succ)) := by
  change affineSegment ℝ (inscribedVertex c Q i)
    (inscribedVertex c Q (finRotate Q.count i)) = _
  rw [affineSegment_eq_segment, next_vertex]

/-- An upstream edge point has a literal affine parameter in the unit interval. -/
lemma mem_edgeSet_iff (c : RegularJordanCurve) (Q : Partition)
    (i : Fin Q.count) (x : Plane) :
    x ∈ (inscribedPolygon c Q).edgeSet ℝ i ↔
      ∃ t : unitInterval, inscribedEdgeMap c Q i t = x := by
  rw [Polygon.edgeSet_eq_image_edgePath]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨⟨t, ht⟩, (edgePath_eq c Q i ⟨t, ht⟩).symm.trans h⟩
  · rintro ⟨t, h⟩
    exact ⟨t, t.property, (edgePath_eq c Q i t).trans h⟩

/-- Every sufficiently fine inscribed polygon is simple. This includes every
partition, with no knot-preservation assumption, and the cyclic closing edge. -/
theorem eventualSimplicity (c : RegularJordanCurve) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
      P202Specs.PolygonTurning.IsSimple (inscribedPolygon c Q) := by
  obtain ⟨η, hη, hgraph⟩ := uniform_projection_radius c
  obtain ⟨δ, hδ, hlocal⟩ := intersectingEdgesLocalize c (η / 4) (by positivity)
  refine ⟨min δ (η / 4), lt_min hδ (by positivity), ?_⟩
  intro Q hmesh
  have hmδ : Q.MeshLT δ := fun i => (hmesh i).trans_le (min_le_left _ _)
  have hmη : Q.MeshLT (η / 4) := fun i => (hmesh i).trans_le (min_le_right _ _)
  refine ⟨Q.at_least_three, vertices_injective c Q, edges_nondegenerate c Q, ?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  change x ∈ openSegment ℝ (inscribedVertex c Q i)
    (inscribedVertex c Q (finRotate Q.count i)) at hx
  rw [next_vertex] at hx
  have hxclosed : x ∈ (inscribedPolygon c Q).edgeSet ℝ i := by
    rw [edgeSet_eq_segment]
    exact openSegment_subset_segment ℝ _ _ hx
  obtain ⟨s, hs⟩ := (mem_edgeSet_iff c Q i x).mp hxclosed
  obtain ⟨t, ht⟩ := (mem_edgeSet_iff c Q j x).mp hy
  have hnear := hlocal Q hmδ i j s t (hs.trans ht.symm)
  obtain ⟨k, hk⟩ := circle_close_lifts hnear.le
  rw [Real.dist_eq, abs_le] at hk
  obtain ⟨L, hL⟩ := hgraph (Q.time i.castSucc) (partition_time_mem Q i.castSucc)
  have hia : Q.time i.castSucc ∈
      Icc (Q.time i.castSucc - η) (Q.time i.castSucc + η) := by
    constructor <;> linarith
  have hib : Q.time i.succ ∈
      Icc (Q.time i.castSucc - η) (Q.time i.castSucc + η) := by
    have hinc := Q.strictMono (a := i.castSucc) (b := i.succ) (by simp)
    have hgap := hmη i
    constructor <;> linarith
  have hja : Q.time j.castSucc + k ∈
      Icc (Q.time i.castSucc - η) (Q.time i.castSucc + η) := by
    constructor <;> linarith [hk.1, hk.2]
  have hjb : Q.time j.succ + k ∈
      Icc (Q.time i.castSucc - η) (Q.time i.castSucc + η) := by
    have hinc := Q.strictMono (a := j.castSucc) (b := j.succ) (by simp)
    have hgap := hmη j
    constructor <;> linarith [hk.1, hk.2]
  have hmono := hL.monotoneOn
  have hiaib := hL hia hib (Q.strictMono (by simp))
  have hjajb := hL hja hjb (by
    have hinc := Q.strictMono (a := j.castSucc) (b := j.succ) (by simp)
    linarith)
  have horder := edge_parameter_order Q hij k
  have hprojorder :
      L (realLift c.parametrization (Q.time i.succ)) ≤
        L (realLift c.parametrization (Q.time j.castSucc + k)) ∨
      L (realLift c.parametrization (Q.time j.succ + k)) ≤
        L (realLift c.parametrization (Q.time i.castSucc)) := by
    rcases horder with h | h
    · exact Or.inl (hmono hib hja h)
    · exact Or.inr (hmono hjb hia h)
  have hd := disjoint_chords_of_projection_order L hiaib hjajb hprojorder
  simp only [realLift_int_shift] at hd
  apply Set.disjoint_left.mp hd
  · exact hx
  · rwa [edgeSet_eq_segment] at hy

/-- Adjacent short directed chords share a strictly positive projection,
including at reflex corners and across the cyclic parameter cut. -/
theorem eventualNoncuspidality (c : RegularJordanCurve) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
      P202Specs.PolygonTurning.Noncuspidal (inscribedPolygon c Q) := by
  obtain ⟨η, hη, hgraph⟩ := uniform_projection_radius c
  refine ⟨η, hη, ?_⟩
  intro Q hmesh
  have adjacent : ∀ i : Fin Q.count,
      NormedSpace.normalize (inscribedEdge c Q i) ≠
        -NormedSpace.normalize (inscribedEdge c Q (finRotate Q.count i)) := by
    intro i
    let j := finRotate Q.count i
    have he : (Q.time j.castSucc : ParameterCircle) = (Q.time i.succ : ParameterCircle) :=
      c.injective (next_vertex c Q i)
    have hdist : dist (Q.time i.succ : ParameterCircle)
        (Q.time j.castSucc : ParameterCircle) ≤ 0 := by rw [he]; simp
    obtain ⟨k, hk⟩ := circle_close_lifts hdist
    have hkeq := dist_le_zero.mp hk
    obtain ⟨L, hL⟩ := hgraph (Q.time i.succ) (partition_time_mem Q i.succ)
    have hia : Q.time i.castSucc ∈ Icc (Q.time i.succ - η) (Q.time i.succ + η) := by
      have hi := Q.strictMono (a := i.castSucc) (b := i.succ) (by simp)
      have hg := hmesh i
      constructor <;> linarith
    have hib : Q.time i.succ ∈ Icc (Q.time i.succ - η) (Q.time i.succ + η) := by
      constructor <;> linarith
    have hjb : Q.time j.succ + k ∈ Icc (Q.time i.succ - η) (Q.time i.succ + η) := by
      have hi := Q.strictMono (a := j.castSucc) (b := j.succ) (by simp)
      have hg := hmesh j
      constructor <;> linarith
    have hi := hL hia hib (Q.strictMono (by simp))
    have hj := hL hib hjb (by
      have hi := Q.strictMono (a := j.castSucc) (b := j.succ) (by simp)
      linarith)
    have hp : 0 < L (inscribedEdge c Q i) := by
      simpa only [inscribedEdge, inscribedVertex, map_sub, sub_pos] using hi
    have hq : 0 < L (inscribedEdge c Q j) := by
      dsimp only at hj
      rw [← hkeq] at hj
      simp only [realLift_int_shift] at hj
      simpa only [realLift_int_shift, inscribedEdge, inscribedVertex, map_sub, sub_pos] using hj
    exact normalize_ne_neg_of_projection_pos L hp hq
  intro i
  have h := adjacent ((finRotate Q.count).symm i)
  simpa only [Equiv.apply_symm_apply, P202Specs.PolygonTurning.incomingVector,
    edgeVector_eq] using h

/-- Uniform eventual simplicity and noncuspidality for every fine partition.
Bounded-side orientation is a separate conclusion and is not asserted here. -/
theorem eventualEmbeddedGeometry (c : RegularJordanCurve) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
      P202Specs.PolygonTurning.IsSimple (inscribedPolygon c Q) ∧
      P202Specs.PolygonTurning.Noncuspidal (inscribedPolygon c Q) := by
  obtain ⟨δs, hs, hsimple⟩ := eventualSimplicity c
  obtain ⟨δn, hn, hnoncusp⟩ := eventualNoncuspidality c
  refine ⟨min δs δn, lt_min hs hn, ?_⟩
  intro Q hmesh
  exact ⟨hsimple Q (fun i => (hmesh i).trans_le (min_le_left _ _)),
    hnoncusp Q (fun i => (hmesh i).trans_le (min_le_right _ _))⟩


/-- A scalar linear projection of a chord lies between its endpoint values. -/
lemma projection_mem_interval (L : Plane →L[ℝ] ℝ) {a b x : Plane}
    (hab : L a ≤ L b) (hx : x ∈ segment ℝ a b) : L x ∈ Icc (L a) (L b) := by
  obtain ⟨α, β, hα, hβ, hsum, rfl⟩ := hx
  simp only [map_add, map_smul, smul_eq_mul, mem_Icc]
  have hαeq : α = 1 - β := by linarith
  have hβeq : β = 1 - α := by linarith
  constructor
  · rw [hαeq]
    nlinarith [mul_nonneg hβ (sub_nonneg.mpr hab)]
  · rw [hβeq]
    nlinarith [mul_nonneg hα (sub_nonneg.mpr hab)]

/-- A short chord can meet the original curve only on its own closed
parameter subarc. The integer shift records the closing edge exactly. -/
theorem eventualArcIsolation (c : RegularJordanCurve) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
      ∀ (i : Fin Q.count) (t : ℝ),
        realLift c.parametrization t ∈ (inscribedPolygon c Q).edgeSet ℝ i →
        ∃ k : ℤ, t + k ∈ Icc (Q.time i.castSucc) (Q.time i.succ) := by
  obtain ⟨η, hη, hgraph⟩ := uniform_projection_radius c
  obtain ⟨ρ, hρ, hinv⟩ := inverse_parameter_modulus c (η / 2) (by positivity)
  obtain ⟨δ, hδ, hshort⟩ := short_edges c ρ hρ
  refine ⟨min δ (η / 2), lt_min hδ (by positivity), ?_⟩
  intro Q hmesh i t ht
  have hmδ : Q.MeshLT δ := fun j => (hmesh j).trans_le (min_le_left _ _)
  have hmη : Q.MeshLT (η / 2) := fun j => (hmesh j).trans_le (min_le_right _ _)
  obtain ⟨u, hu⟩ := (mem_edgeSet_iff c Q i _).mp ht
  have hdist : dist (inscribedVertex c Q i) (realLift c.parametrization t) < ρ := by
    rw [← hu, dist_comm]
    exact (edgeMap_dist_vertex_le c Q i u).trans_lt (hshort Q hmδ i)
  have hnear := hinv (Q.time i.castSucc : ParameterCircle) (t : ParameterCircle) hdist
  obtain ⟨k, hk⟩ := circle_close_lifts hnear.le
  rw [Real.dist_eq, abs_le] at hk
  obtain ⟨L, hL⟩ := hgraph (Q.time i.castSucc) (partition_time_mem Q i.castSucc)
  have ha : Q.time i.castSucc ∈
      Icc (Q.time i.castSucc - η) (Q.time i.castSucc + η) := by
    constructor <;> linarith
  have hb : Q.time i.succ ∈
      Icc (Q.time i.castSucc - η) (Q.time i.castSucc + η) := by
    have hinc := Q.strictMono (a := i.castSucc) (b := i.succ) (by simp)
    have hgap := hmη i
    constructor <;> linarith
  have htk : t + k ∈ Icc (Q.time i.castSucc - η) (Q.time i.castSucc + η) := by
    constructor <;> linarith [hk.1, hk.2]
  have hab := hL ha hb (Q.strictMono (by simp))
  rw [edgeSet_eq_segment] at ht
  have hp := projection_mem_interval L hab.le ht
  have hvalue : L (realLift c.parametrization (t + k)) ∈
      Icc (L (realLift c.parametrization (Q.time i.castSucc)))
        (L (realLift c.parametrization (Q.time i.succ))) := by
    simpa only [realLift_int_shift] using hp
  exact ⟨k, (hL.le_iff_le ha htk).mp hvalue.1, (hL.le_iff_le htk hb).mp hvalue.2⟩

open Filter
open scoped _root_.Topology

/-- A short ray into an open set determines every ray in the same local
open half-space when the frontier is locally contained in its bounding plane. -/
lemma short_ray_into_of_local_frontier {U : Set Plane} (hU : IsOpen U)
    (p w v : Plane) (L : Plane →L[ℝ] ℝ)
    (hw : 0 < L w) (hv : 0 < L v)
    (hflat : ∃ R : ℝ, 0 < R ∧ ∀ x ∈ Metric.ball p R,
      x ∈ frontier U → L x = L p)
    (hinto : ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε → p + r • w ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε → p + r • v ∈ U := by
  obtain ⟨R, hR, hflat⟩ := hflat
  let C : Set Plane := Metric.ball p R ∩ {x | L p < L x}
  have hconv : Convex ℝ C := (convex_ball p R).inter
    (convex_halfSpace_gt L.toLinearMap.isLinear (L p))
  have havoid : Disjoint C (frontier U) := by
    apply disjoint_left.mpr
    intro x hx hxf
    exact (ne_of_gt hx.2) (hflat x hx.1 hxf)
  have hball (d : Plane) : ∀ᶠ r : ℝ in 𝓝 0, p + r • d ∈ Metric.ball p R := by
    have hc : Continuous (fun r : ℝ => p + r • d) := by fun_prop
    have hp : p + (0 : ℝ) • d ∈ Metric.ball p R := by simpa using hR
    exact hc.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hp)
  obtain ⟨η, hη, hηw⟩ := Metric.eventually_nhds_iff.mp (hball w)
  obtain ⟨ε, hε, hεw⟩ := hinto
  let r := min ε η / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r < ε := by dsimp [r]; have := min_le_left ε η; linarith
  have hrη : r < η := by dsimp [r]; have := min_le_right ε η; linarith
  have hmem : p + r • w ∈ C := by
    refine ⟨hηw (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using hrη), ?_⟩
    change L p < L (p + r • w)
    rw [map_add, map_smul, smul_eq_mul]
    exact lt_add_of_pos_right _ (mul_pos hr hw)
  have hCU : C ⊆ U := by
    apply hconv.isPreconnected.subset_of_closure_inter_subset hU
      ⟨_, hmem, hεw r hr hre⟩
    intro x hx
    by_contra hxU
    apply disjoint_left.mp havoid hx.2
    rw [hU.frontier_eq]
    exact ⟨hx.1, hxU⟩
  obtain ⟨δ, hδ, hδv⟩ := Metric.eventually_nhds_iff.mp (hball v)
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsδ
  apply hCU
  refine ⟨hδv (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hs] using hsδ), ?_⟩
  change L p < L (p + s • v)
  rw [map_add, map_smul, smul_eq_mul]
  exact lt_add_of_pos_right _ (mul_pos hs hv)

lemma polygon_frontier_locally_in_edgeLine {n : ℕ} (p : Polygon Plane n)
    (o : Orientation ℝ Plane (Fin 2)) (hp : P202Specs.PolygonTurning.IsSimple p)
    {U : Set Plane} (hfr : frontier U = p.boundary ℝ)
    (i : Fin n) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ Metric.ball (p.edgePath ℝ i t) R,
      x ∈ frontier U →
      inner ℝ (o.rightAngleRotation (P202Specs.PolygonTurning.edgeVector p i)) x =
        inner ℝ (o.rightAngleRotation (P202Specs.PolygonTurning.edgeVector p i))
          (p.edgePath ℝ i t) := by
  classical
  let F : Set Plane := ⋃ j : {j : Fin n // j ≠ i}, p.edgeSet ℝ j.val
  have hF : IsClosed F := by
    apply isClosed_iUnion_of_finite
    intro j
    rw [Polygon.edgeSet_eq_image_edgePath]
    exact (isCompact_Icc.image (by
      simp only [Polygon.edgePath]
      fun_prop)).isClosed
  have hx : p.edgePath ℝ i t ∉ F := by
    intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hp.2.2.2 i j.val (Ne.symm j.property))
      (lineMap_mem_openSegment ℝ (p i) (p (finRotate n i)) ht) hj
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hF.isOpen_compl.mem_nhds hx)
  refine ⟨R, hR, ?_⟩
  intro x hxball hxfr
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hfr ▸ hxfr)
  have hji : j = i := by
    by_contra hji
    exact hball hxball (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  subst j
  rw [Polygon.edgeSet_eq_image_edgePath] at hj
  obtain ⟨s, hs, rfl⟩ := hj
  have hn : inner ℝ (o.rightAngleRotation (P202Specs.PolygonTurning.edgeVector p i))
      (P202Specs.PolygonTurning.edgeVector p i) = 0 := o.inner_rightAngleRotation_self _
  simp only [Polygon.edgePath, AffineMap.lineMap_apply_module']
  change inner ℝ _ (s • P202Specs.PolygonTurning.edgeVector p i + p i) =
    inner ℝ _ (t • P202Specs.PolygonTurning.edgeVector p i + p i)
  simp only [inner_add_right, real_inner_smul_right, hn, mul_zero, zero_add]

lemma polygonLeft_of_transverse_ray {n : ℕ} (p : Polygon Plane n)
    (o : Orientation ℝ Plane (Fin 2)) (hp : P202Specs.PolygonTurning.IsSimple p)
    {U : Set Plane} (hU : IsOpen U) (hfr : frontier U = p.boundary ℝ)
    (hrays : ∀ (i : Fin n) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 →
      ∃ w : Plane, 0 < inner ℝ w (o.rightAngleRotation
          (P202Specs.PolygonTurning.edgeVector p i)) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
          p.edgePath ℝ i t + r • w ∈ U) :
    P202Specs.PolygonTurning.HasBoundedSideOnLeft o p U := by
  intro i t ht
  obtain ⟨w, hw, hray⟩ := hrays i t ht
  let v := o.rightAngleRotation (P202Specs.PolygonTurning.edgeVector p i)
  have he : P202Specs.PolygonTurning.edgeVector p i ≠ 0 :=
    sub_ne_zero.mpr (hp.2.2.1 i).symm
  have hv : v ≠ 0 := by
    intro hz
    apply he
    apply o.rightAngleRotation.injective
    simpa only [map_zero] using hz
  apply short_ray_into_of_local_frontier hU (p.edgePath ℝ i t) w v (innerSL ℝ v)
  · change 0 < inner ℝ v w
    exact (real_inner_comm w v) ▸ hw
  · exact real_inner_self_pos.mpr hv
  · exact polygon_frontier_locally_in_edgeLine p o hp hfr i t ht
  · exact hray

open P202Specs.PlanarRegionTopology (HasSideOnLeft quarterTurn)
open P202.PlanarRegionTopology

/-- The two global halves of a genuine bicollar lie on opposite Jordan sides. -/
theorem bicollar_side_selection (c : RegularJordanCurve) (A B : Set Plane)
    (hA : IsOpen A) (hB : IsOpen B) (hd : Disjoint A B)
    (hu : A ∪ B = c.traceᶜ) (hfA : frontier A = c.trace) (hfB : frontier B = c.trace)
    {a : ℝ} (ha : 0 < a) (e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane)
    (hsource : e.source = univ ×ˢ Ioo (-a) a)
    (hzero : ∀ q : ParameterCircle, e (q, 0) = c.parametrization q) :
    (e '' (univ ×ˢ Ioo 0 a) ⊆ A ∧ e '' (univ ×ˢ Ioo (-a) 0) ⊆ B) ∨
    (e '' (univ ×ˢ Ioo (-a) 0) ⊆ A ∧ e '' (univ ×ˢ Ioo 0 a) ⊆ B) := by
  have hzsource : ∀ q : ParameterCircle, (q, (0 : ℝ)) ∈ e.source := by
    intro q
    rw [hsource]
    exact ⟨mem_univ _, neg_lt_zero.mpr ha, ha⟩
  have hboundary : ∀ z ∈ e.source, e z ∈ c.trace ↔ z.2 = 0 := by
    intro z hz
    constructor
    · rintro ⟨q, heq⟩
      have heq' : e z = e (q, 0) := by rw [hzero]; exact heq.symm
      exact congrArg Prod.snd (e.injOn hz (hzsource q) heq')
    · intro hz0
      rw [show z = (z.1, 0) from Prod.ext rfl hz0, hzero]
      exact mem_range_self _
  have hpos : univ ×ˢ Ioo 0 a ⊆ e.source := by
    intro z hz
    rw [hsource]
    exact ⟨mem_univ _, (neg_lt_zero.mpr ha).trans hz.2.1, hz.2.2⟩
  have hneg : univ ×ˢ Ioo (-a) 0 ⊆ e.source := by
    intro z hz
    rw [hsource]
    exact ⟨mem_univ _, hz.2.1, hz.2.2.trans ha⟩
  have hpartition : e.target \ c.trace =
      e '' (univ ×ˢ Ioo 0 a) ∪ e '' (univ ×ˢ Ioo (-a) 0) := by
    ext y
    constructor
    · intro hy
      let z := e.symm y
      have hzs : z ∈ e.source := e.map_target hy.1
      have hezy : e z = y := e.right_inv hy.1
      have hz0 : z.2 ≠ 0 := fun hz0 => hy.2 (hezy ▸ (hboundary z hzs).2 hz0)
      have hzinterval : z.2 ∈ Ioo (-a) a := by rw [hsource] at hzs; exact hzs.2
      rcases lt_or_gt_of_ne hz0 with hzneg | hzpos
      · exact Or.inr ⟨z, ⟨mem_univ _, hzinterval.1, hzneg⟩, hezy⟩
      · exact Or.inl ⟨z, ⟨mem_univ _, hzpos, hzinterval.2⟩, hezy⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · refine ⟨e.map_source (hpos hz), ?_⟩
        exact fun hzb => hz.2.1.ne' ((hboundary z (hpos hz)).1 hzb)
      · refine ⟨e.map_source (hneg hz), ?_⟩
        exact fun hzb => hz.2.2.ne ((hboundary z (hneg hz)).1 hzb)
  have hposconn : IsPreconnected (e '' (univ ×ˢ Ioo 0 a)) :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image e (e.continuousOn.mono hpos)
  have hnegconn : IsPreconnected (e '' (univ ×ˢ Ioo (-a) 0)) :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image e (e.continuousOn.mono hneg)
  have hcover : e '' (univ ×ˢ Ioo 0 a) ∪ e '' (univ ×ˢ Ioo (-a) 0) ⊆ A ∪ B := by
    rw [← hpartition, hu]
    exact fun _ hx => hx.2
  have hp := hposconn.subset_or_subset hA hB hd (Subset.trans subset_union_left hcover)
  have hn := hnegconn.subset_or_subset hA hB hd (Subset.trans subset_union_right hcover)
  have hpt : c.parametrization 0 ∈ e.target := hzero 0 ▸ e.map_source (hzsource 0)
  have hpf : c.parametrization 0 ∈ c.trace := mem_range_self _
  have hex (E : Set Plane) (hfE : frontier E = c.trace) :
      (e.target ∩ E).Nonempty := by
    have hcl : c.parametrization 0 ∈ closure E := frontier_subset_closure (hfE.symm ▸ hpf)
    exact mem_closure_iff.mp hcl e.target e.open_target hpt
  have hxAB (E : Set Plane) (hE : IsOpen E) (hfE : frontier E = c.trace)
      (hxE : E ⊆ A ∪ B) :
      ∃ x ∈ e '' (univ ×ˢ Ioo 0 a) ∪ e '' (univ ×ˢ Ioo (-a) 0), x ∈ E := by
    obtain ⟨x, hxt, hxE'⟩ := hex E hfE
    refine ⟨x, ?_, hxE'⟩
    rw [← hpartition]
    refine ⟨hxt, ?_⟩
    intro hxf
    have hxf' := hfE.symm ▸ hxf
    rw [hE.frontier_eq] at hxf'
    exact hxf'.2 hxE'
  obtain ⟨x, hx, hxA⟩ := hxAB A hA hfA subset_union_left
  obtain ⟨y, hy, hyB⟩ := hxAB B hB hfB subset_union_right
  rcases hp with hp | hp <;> rcases hn with hn | hn
  · exact False.elim (disjoint_left.mp hd (hy.elim (fun h => hp h) (fun h => hn h)) hyB)
  · exact Or.inl ⟨hp, hn⟩
  · exact Or.inr ⟨hn, hp⟩
  · exact False.elim (disjoint_left.mp hd hxA (hx.elim (fun h => hp h) (fun h => hn h)))

/-- Every regular Jordan parametrization has a coherent choice of opposite
normal orientations into a prescribed actual Jordan side. -/
theorem coherent_jordan_orientation (c : RegularJordanCurve) (A B : Set Plane)
    (hA : IsOpen A) (hB : IsOpen B) (hd : Disjoint A B)
    (hu : A ∪ B = c.traceᶜ) (hfA : frontier A = c.trace) (hfB : frontier B = c.trace) :
    ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧ HasSideOnLeft A c sign ∧ HasSideOnLeft B c (-sign) := by
  obtain ⟨W, a, e, ha, hsource, hformula, hWoff⟩ := curve_bicollar c
  have hzero : ∀ q : ParameterCircle, e (q, 0) = c.parametrization q := by
    intro q
    simp only [hformula, zero_smul, add_zero]
  have hmap : (fun z : ParameterCircle × ℝ =>
      c.parametrization z.1 + z.2 • W z.1) = e := by
    funext z
    exact (hformula z).symm
  have hray : ∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
      ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
        realLift c.parametrization t + r • quarterTurn (deriv (realLift c.parametrization) t) ∈
          e '' (univ ×ˢ Ioo 0 a) ∧
        realLift c.parametrization t - r • quarterTurn (deriv (realLift c.parametrization) t) ∈
          e '' (univ ×ˢ Ioo (-a) 0) := by
    intro t ht
    simpa only [hmap] using affine_bicollar_normal_rays c W t a ha
      (c.smooth_off_joins t ht) (hWoff t ht).1 (hWoff t ht).2
  rcases bicollar_side_selection c A B hA hB hd hu hfA hfB ha e hsource hzero with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · intro t ht
      obtain ⟨ε, hε, htest⟩ := hray t ht
      exact ⟨ε, hε, fun r hr hre => by simpa using hpos.1 (htest r hr hre).1⟩
    · intro t ht
      obtain ⟨ε, hε, htest⟩ := hray t ht
      exact ⟨ε, hε, fun r hr hre => by simpa [sub_eq_add_neg] using hpos.2 (htest r hr hre).2⟩
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · intro t ht
      obtain ⟨ε, hε, htest⟩ := hray t ht
      exact ⟨ε, hε, fun r hr hre => by simpa [sub_eq_add_neg] using hneg.1 (htest r hr hre).2⟩
    · intro t ht
      obtain ⟨ε, hε, htest⟩ := hray t ht
      exact ⟨ε, hε, fun r hr hre => by simpa using hneg.2 (htest r hr hre).1⟩

open Set _root_.Topology
namespace JordanPolygon
open P202Specs.PlanarRegionTopology
open P202.PlanarRegionTopology
open P202.PlanarRegionComponents

/-- Jordan separation uses only the literal continuous embedding, with no
piecewise-smooth or derivative packaging requirement. -/
theorem continuous_spherical_jordan_separation (γ : C(ParameterCircle, Plane))
    (hγ : Function.Injective γ) :
    ∃ A B : Set (OnePoint Plane), IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = ((fun x : Plane => (x : OnePoint Plane)) '' range γ)ᶜ ∧
      frontier A = (fun x : Plane => (x : OnePoint Plane)) '' range γ ∧
      frontier B = (fun x : Plane => (x : OnePoint Plane)) '' range γ := by
  obtain ⟨h⟩ := compactificationSphere
  obtain ⟨q⟩ := parameterCircleSphere
  let f : P202.Duality.NeighborhoodCohomology.Sphere 1 →
      P202.Duality.NeighborhoodCohomology.Sphere 2 :=
    fun z => h (γ (q.symm z))
  have hf : _root_.Topology.IsEmbedding f :=
    h.isEmbedding.comp (OnePoint.isOpenEmbedding_coe.isEmbedding.comp
      ((γ.continuous.isClosedEmbedding hγ).isEmbedding.comp q.symm.isEmbedding))
  obtain ⟨⟨e⟩, he⟩ := P202.JordanBrouwer.separation 2 (by omega) f hf
  let _ := P202.JordanBrouwer.sphere_locallyConnected 2
  obtain ⟨A, B, hA, hB, hcA, hcB, hd, hu, hfA, hfB⟩ :=
    two_sides_of_components (P202.JordanBrouwer.sphere_range_closed hf) e he
  have hrange : range f = h '' ((fun x : Plane => (x : OnePoint Plane)) '' range γ) := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, ⟨_, ⟨q.symm t, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
      exact ⟨q t, by simp [f]⟩
  have hp : h ⁻¹' range f = (fun x : Plane => (x : OnePoint Plane)) '' range γ := by
    rw [hrange, preimage_image_eq _ h.injective]
  refine ⟨h ⁻¹' A, h ⁻¹' B, hA.preimage h.continuous, hB.preimage h.continuous,
    h.isConnected_preimage.mpr hcA, h.isConnected_preimage.mpr hcB,
    hd.preimage _, ?_, ?_, ?_⟩
  · rw [← preimage_union, hu, preimage_compl, hp]
  · rw [← h.preimage_frontier, hfA, hp]
  · rw [← h.preimage_frontier, hfB, hp]

/-- Every continuous injective circle map bounds an actual bounded connected
open set, whose frontier is exactly its range. -/
theorem continuous_bounded_jordan_side (γ : C(ParameterCircle, Plane))
    (hγ : Function.Injective γ) :
    ∃ U : Set Plane, IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧ frontier U = range γ := by
  obtain ⟨A, B, hA, hB, hcA, hcB, hd, hu, hfA, hfB⟩ :=
    continuous_spherical_jordan_separation γ hγ
  have hi : (OnePoint.infty : OnePoint Plane) ∈ A ∪ B :=
    hu.symm ▸ OnePoint.infty_notMem_image_coe
  have hside (E : Set (OnePoint Plane)) (hE : IsOpen E) (hcE : IsConnected E)
      (hfE : frontier E = (fun x : Plane => (x : OnePoint Plane)) '' range γ)
      (hinfty : (OnePoint.infty : OnePoint Plane) ∉ E) :
      ∃ U : Set Plane, IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧ frontier U = range γ := by
    refine ⟨planarPart E, hE.preimage OnePoint.continuous_coe,
      planarPart_connected hE hcE, planarPart_bounded_of_not_infty ?_ hinfty, ?_⟩
    · rw [hfE]
      exact OnePoint.infty_notMem_image_coe
    · change frontier (((↑) : Plane → OnePoint Plane) ⁻¹' E) = range γ
      rw [← OnePoint.isOpenMap_coe.preimage_frontier_eq_frontier_preimage
        OnePoint.continuous_coe, hfE]
      exact preimage_image_eq _ OnePoint.coe_injective
  rcases hi with hi | hi
  · exact hside B hB hcB hfB (fun h => disjoint_left.mp hd hi h)
  · exact hside A hA hcA hfA (fun h => disjoint_left.mp hd h hi)
end JordanPolygon

open Set _root_.Topology
open scoped unitInterval
namespace JordanPolygon
open P202Specs.PlanarRegionTopology (Plane ParameterCircle)
open P202Specs.PlaneTurning
open P202Specs.PolygonTurning
open P202.PlaneTurning

lemma uniformSlot_first (n : ℕ) (hn : 0 < n) :
    uniformSlot n hn ⟨0, hn⟩ 0 = 0 := by
  apply Subtype.ext
  simp [uniformSlot]

lemma uniformSlot_last (n : ℕ) (hn : 0 < n) :
    uniformSlot n hn ⟨n-1, by omega⟩ 1 = 1 := by
  apply Subtype.ext
  change (((n-1 : ℕ) : ℝ) + 1) / n = 1
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [div_eq_one_iff_eq hn']
  exact_mod_cast (show n-1+1=n by omega)

lemma uniformSlot_cyclic_endpoint (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (((uniformSlot n hn i 1 : unitInterval) : ℝ) : ParameterCircle) =
      (((uniformSlot n hn (finRotate n i) 0 : unitInterval) : ℝ) : ParameterCircle) := by
  by_cases hi : i.val + 1 < n
  · have hrot : (finRotate n i).val = i.val + 1 := by
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      exact Nat.mod_eq_of_lt hi
    congr 1
    dsimp [uniformSlot]
    simp only [hrot, Nat.cast_add, Nat.cast_one, add_zero]
  · have hilast : i = ⟨n-1, by omega⟩ := Fin.ext (by change i.val = n-1; omega)
    have hrot : finRotate n i = ⟨0, hn⟩ := by
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      have hi' : i.val+1=n := by omega
      rw [hi', Nat.mod_self]
    rw [hilast, uniformSlot_last, show finRotate n ⟨n-1, by omega⟩ = ⟨0, hn⟩ from hilast ▸ hrot,
      uniformSlot_first]
    simp

/-- A simple polygon has a literal injective circle parametrization, with the
uniform edge slots and exact boundary range. -/
theorem simple_polygon_circle {n : ℕ} (p : Polygon Plane n) (hp : IsSimple p) :
    ∃ γ : C(ParameterCircle, Plane), Function.Injective γ ∧ range γ = p.boundary ℝ ∧
      ∀ (i : Fin n) (t : unitInterval),
        γ (((uniformSlot n (by have := hp.1; omega) i t : unitInterval) : ℝ) : ParameterCircle) =
          p.edgePath ℝ i t := by
  have hn : 0 < n := by have := hp.1; omega
  let f : Fin n → C(unitInterval, Plane) := fun i =>
    ⟨fun t => p.edgePath ℝ i (t : ℝ), AffineMap.lineMap_continuous.comp continuous_subtype_val⟩
  have hjoin : ∀ j k : Fin n, j.val+1=k.val → f j 1=f k 0 := by
    intro j k hjk
    have hrot : finRotate n j = k := by
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      rw [hjk, Nat.mod_eq_of_lt k.isLt]
    change p.edgePath ℝ j 1 = p.edgePath ℝ k 0
    simp only [Polygon.edgePath, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero]
    exact congrArg p hrot
  obtain ⟨M, hM⟩ := glue_uniform_slots n hn f hjoin
  have hclosed : M 0 = M 1 := by
    rw [← uniformSlot_first n hn, hM, ← uniformSlot_last n hn, hM]
    have hrot : finRotate n (⟨n-1, by omega⟩ : Fin n) = ⟨0, hn⟩ := by
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      have hi : n-1+1=n := by omega
      rw [hi, Nat.mod_self]
    change p.edgePath ℝ ⟨0, hn⟩ 0 = p.edgePath ℝ ⟨n-1, by omega⟩ 1
    simp only [Polygon.edgePath, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero]
    exact (congrArg p hrot).symm
  let F : ℝ → Plane := fun t => M (projIcc 0 1 zero_le_one t)
  have hF : Continuous F := M.continuous.comp continuous_projIcc
  have hFclosed : F 0 = F 1 := by simpa [F] using hclosed
  let γ : C(ParameterCircle, Plane) :=
    ⟨AddCircle.liftIco 1 0 F, AddCircle.liftIco_zero_continuous hFclosed hF.continuousOn⟩
  have hγM (t : unitInterval) : γ ((t : ℝ) : ParameterCircle) = M t := by
    by_cases ht : (t : ℝ) < 1
    · change AddCircle.liftIco 1 0 F _ = _
      rw [AddCircle.liftIco_zero_coe_apply ⟨t.property.1, ht⟩]
      simp [F, projIcc_of_mem zero_le_one t.property]
    · have ht' : t = 1 := Subtype.ext (by change (t : ℝ) = 1; exact le_antisymm t.property.2 (le_of_not_gt ht))
      subst t
      change AddCircle.liftIco 1 0 F ((1 : ℝ) : ParameterCircle) = M 1
      rw [AddCircle.coe_period, ← AddCircle.coe_zero,
        AddCircle.liftIco_zero_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 1)]
      simpa [F] using hclosed
  have hslot (i : Fin n) (t : unitInterval) :
      γ (((uniformSlot n hn i t : unitInterval) : ℝ) : ParameterCircle) = p.edgePath ℝ i t := by
    rw [hγM, hM]
    rfl
  have hrepr : ∀ x : ParameterCircle, ∃ i : Fin n, ∃ t : unitInterval,
      (((uniformSlot n hn i t : unitInterval) : ℝ) : ParameterCircle) = x := by
    intro x
    obtain ⟨s, hs, rfl⟩ := AddCircle.eq_coe_Ico x
    obtain ⟨⟨i, t⟩, hit⟩ := uniformSlot_surjective n hn ⟨s, hs.1, hs.2.le⟩
    exact ⟨i, t, congrArg (fun z : unitInterval => ((z : ℝ) : ParameterCircle)) hit⟩
  refine ⟨γ, ?_, ?_, hslot⟩
  · intro x y hxy
    obtain ⟨i, t, rfl⟩ := hrepr x
    obtain ⟨j, u, rfl⟩ := hrepr y
    rw [hslot, hslot] at hxy
    rcases (P202.PolygonTurning.edgePath_eq_iff hp i j t.property u.property).mp hxy with
      ⟨hij, htu⟩ | ⟨hij, ht, hu⟩ | ⟨hji, ht, hu⟩
    · subst j
      have htu' : t=u := Subtype.ext htu
      rw [htu']
    · have ht' : t=1 := Subtype.ext ht
      have hu' : u=0 := Subtype.ext hu
      rw [ht', hu', ← hij]
      exact uniformSlot_cyclic_endpoint n hn i
    · have ht' : t=0 := Subtype.ext ht
      have hu' : u=1 := Subtype.ext hu
      rw [ht', hu', ← hji]
      exact (uniformSlot_cyclic_endpoint n hn j).symm
  · ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨i, t, rfl⟩ := hrepr x
      rw [hslot]
      exact mem_iUnion.mpr ⟨i, ⟨(t : ℝ), t.property, rfl⟩⟩
    · intro hz
      obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hz
      exact ⟨(((uniformSlot n hn i ⟨t, ht⟩ : unitInterval) : ℝ) : ParameterCircle), hslot i ⟨t, ht⟩⟩
end JordanPolygon

namespace JordanPolygon
open P202Specs.PlanarRegionTopology (Plane)
open P202Specs.PolygonTurning

theorem simple_polygon_has_bounded_side {n : ℕ} (p : Polygon Plane n) (hp : IsSimple p) :
    ∃ U : Set Plane, IsBoundedSide p U := by
  obtain ⟨γ, hγ, hrange, _⟩ := simple_polygon_circle p hp
  obtain ⟨U, hU, hcU, hbU, hfU⟩ := continuous_bounded_jordan_side γ hγ
  exact ⟨U, hU, hcU, hbU, hfU.trans hrange⟩
end JordanPolygon

/-- Strict positivity persists jointly in the sample point and varying covector. -/
theorem uniform_projection_across_join {c : RegularJordanCurve} {t δ : ℝ}
    {l r : ℝ → Plane} {a : ℝ → Plane} (hδ : 0 < δ)
    (hl : ContDiffOn ℝ ∞ l (Ioo (t - δ) (t + δ)))
    (hr : ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)))
    (hel : EqOn l (realLift c.parametrization) (Icc (t - δ) t))
    (her : EqOn r (realLift c.parametrization) (Icc t (t + δ)))
    (ha : ContinuousAt a t)
    (hpl : 0 < inner ℝ (a t) (deriv l t))
    (hpr : 0 < inner ℝ (a t) (deriv r t)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ Icc (t - ε) (t + ε),
      StrictMonoOn (fun s => inner ℝ (a q) (realLift c.parametrization s))
        (Icc (t - ε) (t + ε)) := by
  have ht : t ∈ Ioo (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
  have hcl : ContinuousAt (deriv l) t :=
    (hl.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).continuousAt
      (isOpen_Ioo.mem_nhds ht)
  have hcr : ContinuousAt (deriv r) t :=
    (hr.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).continuousAt
      (isOpen_Ioo.mem_nhds ht)
  have ha₂ : ContinuousAt (fun p : ℝ × ℝ => a p.1) (t, t) :=
    ContinuousAt.comp (g := a) ha continuousAt_fst
  have hcl₂ : ContinuousAt (fun p : ℝ × ℝ => deriv l p.2) (t, t) :=
    ContinuousAt.comp (g := deriv l) hcl continuousAt_snd
  have hcr₂ : ContinuousAt (fun p : ℝ × ℝ => deriv r p.2) (t, t) :=
    ContinuousAt.comp (g := deriv r) hcr continuousAt_snd
  have hcontl : ContinuousAt (fun p : ℝ × ℝ =>
      inner ℝ (a p.1) (deriv l p.2)) (t, t) := ha₂.inner (𝕜 := ℝ) hcl₂
  have hcontr : ContinuousAt (fun p : ℝ × ℝ =>
      inner ℝ (a p.1) (deriv r p.2)) (t, t) := ha₂.inner (𝕜 := ℝ) hcr₂
  have hposl : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, t),
      0 < inner ℝ (a p.1) (deriv l p.2) :=
    hcontl.eventually (Ioi_mem_nhds hpl)
  have hposr : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, t),
      0 < inner ℝ (a p.1) (deriv r p.2) :=
    hcontr.eventually (Ioi_mem_nhds hpr)
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp (hposl.and hposr)
  let ε := min δ η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; have := min_le_left δ η; linarith
  have hεη : ε < η := by dsimp [ε]; have := min_le_right δ η; linarith
  have hsmall : ∀ q ∈ Icc (t - ε) (t + ε), ∀ s ∈ Icc (t - ε) (t + ε),
      s ∈ Ioo (t - δ) (t + δ) ∧
      0 < inner ℝ (a q) (deriv l s) ∧ 0 < inner ℝ (a q) (deriv r s) := by
    intro q hq s hs
    refine ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    apply hηball (a := (q, s))
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor <;> rw [Real.dist_eq, abs_lt] <;>
      constructor <;> linarith [hq.1, hq.2, hs.1, hs.2]
  have hsubL : Icc (t - ε) t ⊆ Ioo (t - δ) (t + δ) := by
    intro s hs
    exact (hsmall t ⟨by linarith, by linarith⟩ s ⟨hs.1, by linarith [hs.2]⟩).1
  have hsubR : Icc t (t + ε) ⊆ Ioo (t - δ) (t + δ) := by
    intro s hs
    exact (hsmall t ⟨by linarith, by linarith⟩ s ⟨by linarith [hs.1], hs.2⟩).1
  refine ⟨ε, hε, ?_⟩
  intro q hq
  have hlmono : StrictMonoOn (fun s => inner ℝ (a q) (l s)) (Icc (t - ε) t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuousOn_const.inner (hl.continuousOn.mono hsubL)))
    intro s hs
    have hs' := interior_subset hs
    have hds : DifferentiableAt ℝ l s :=
      ((hl s (hsubL hs')).contDiffAt (isOpen_Ioo.mem_nhds (hsubL hs'))).differentiableAt
        (by simp)
    rw [deriv_inner_apply ℝ (differentiableAt_const (a q)) hds]
    simpa using (hsmall q hq s ⟨hs'.1, by linarith [hs'.2]⟩).2.1
  have hrmono : StrictMonoOn (fun s => inner ℝ (a q) (r s)) (Icc t (t + ε)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuousOn_const.inner (hr.continuousOn.mono hsubR)))
    intro s hs
    have hs' := interior_subset hs
    have hds : DifferentiableAt ℝ r s :=
      ((hr s (hsubR hs')).contDiffAt (isOpen_Ioo.mem_nhds (hsubR hs'))).differentiableAt
        (by simp)
    rw [deriv_inner_apply ℝ (differentiableAt_const (a q)) hds]
    simpa using (hsmall q hq s ⟨by linarith [hs'.1], hs'.2⟩).2.2
  refine strictMonoOn_across_join hε hlmono hrmono ?_ ?_
  · exact hel.mono (by intro s hs; exact ⟨by linarith [hs.1], hs.2⟩)
  · exact her.mono (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩)

/-- A continuous varying transverse field pairs positively with all nearby secants,
including secants crossing a noncuspidal join. -/
theorem uniform_secant_transversality {c : RegularJordanCurve} {t δ : ℝ}
    {l r W : ℝ → Plane} (hδ : 0 < δ)
    (hl : ContDiffOn ℝ ∞ l (Ioo (t - δ) (t + δ)))
    (hr : ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)))
    (hel : EqOn l (realLift c.parametrization) (Icc (t - δ) t))
    (her : EqOn r (realLift c.parametrization) (Icc t (t + δ)))
    (hW : ContinuousAt W t)
    (hpl : 0 < inner ℝ (W t) (quarterTurn (deriv l t)))
    (hpr : 0 < inner ℝ (W t) (quarterTurn (deriv r t))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ Icc (t - ε) (t + ε),
      ∀ s ∈ Icc (t - ε) (t + ε), ∀ u ∈ Icc (t - ε) (t + ε), s < u →
        0 < inner ℝ (W q) (quarterTurn
          (realLift c.parametrization u - realLift c.parametrization s)) := by
  have hQ : Continuous quarterTurn := by unfold quarterTurn; fun_prop
  have ha : ContinuousAt (fun q => -quarterTurn (W q)) t :=
    ((hQ.continuousAt).comp hW).neg
  obtain ⟨ε, hε, hm⟩ := uniform_projection_across_join hδ hl hr hel her ha
    (by simpa only [inner_neg_quarterTurn_left] using hpl)
    (by simpa only [inner_neg_quarterTurn_left] using hpr)
  refine ⟨ε, hε, ?_⟩
  intro q hq s hs u hu hsu
  have h := sub_pos.mpr (hm q hq hs hu hsu)
  rw [← inner_sub_right, inner_neg_quarterTurn_left] at h
  exact h

/-- A line transverse to each actual affine collar fiber meets each fiber at most once. -/
theorem affine_fiber_projection_injective {X : Type*} {S : Set ℝ}
    (γ W : X → Plane) (q : ℝ → X) (r : ℝ → ℝ) (b E : Plane)
    (hfib : ∀ s ∈ S, b + s • E = γ (q s) + r s • W (q s))
    (htrans : ∀ s ∈ S, 0 < inner ℝ (W (q s)) (quarterTurn E)) :
    Set.InjOn q S := by
  intro s hs t ht hst
  let a := -quarterTurn (W (q s))
  have horth : inner ℝ a (W (q s)) = 0 := inner_neg_quarterTurn_self _
  have hpos : 0 < inner ℝ a E := by
    simpa only [a, inner_neg_quarterTurn_left] using htrans s hs
  have h₁ := congrArg (fun x => inner ℝ a x) (hfib s hs)
  have h₂ := congrArg (fun x => inner ℝ a x) (hfib t ht)
  rw [← hst] at h₂
  simp only [inner_add_right, inner_smul_right, horth, mul_zero, add_zero] at h₁ h₂
  nlinarith

/-- The left normal of a transverse chord enters the positive side of any
fiber graph representing that chord. This is an exact linear identity. -/
theorem left_normal_above_fiber_graph {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (b E γ W : V) (s u ρ h f : ℝ)
    (hE : E ≠ 0) (hρ : 0 < ρ)
    (htrans : 0 < inner ℝ W (o.rightAngleRotation E))
    (hx : b + s • E + ρ • o.rightAngleRotation E = γ + h • W)
    (hy : b + u • E = γ + f • W) : f < h := by
  have horth : inner ℝ (o.rightAngleRotation E) E = 0 :=
    o.inner_rightAngleRotation_self E
  have hnorm : inner ℝ (o.rightAngleRotation E) (o.rightAngleRotation E) = inner ℝ E E :=
    o.inner_comp_rightAngleRotation E E
  have hpos : 0 < inner ℝ (o.rightAngleRotation E) W := by
    simpa only [real_inner_comm] using htrans
  have hposE : 0 < inner ℝ E E := real_inner_self_pos.mpr hE
  have h₁ := congrArg (fun x => inner ℝ (o.rightAngleRotation E) x) hx
  have h₂ := congrArg (fun x => inner ℝ (o.rightAngleRotation E) x) hy
  simp only [inner_add_right, inner_smul_right, horth, hnorm, mul_zero, add_zero] at h₁ h₂
  nlinarith [mul_pos hρ hposE]


/-- The fine literal polygons have genuine bounded Jordan domains. The sign
of their orientation has not been included in the assumptions or conclusion. -/
theorem eventualBoundedGeometry : InscribedExpected.eventualBoundedGeometry := by
  intro c
  obtain ⟨δ, hδ, hgeom⟩ := eventualEmbeddedGeometry c
  refine ⟨δ, hδ, ?_⟩
  intro Q hmesh
  obtain ⟨hsimple, hnoncusp⟩ := hgeom Q hmesh
  exact ⟨hsimple, hnoncusp,
    JordanPolygon.simple_polygon_has_bounded_side (inscribedPolygon c Q) hsimple⟩

/-- Compactness upgrades short-edge control to containment in any given
open neighborhood, a first step toward working in the genuine bicollar. -/
theorem eventualNeighborhoodContainment : InscribedExpected.eventualNeighborhoodContainment := by
  intro c O hO htrace
  have hcompact : IsCompact c.trace := isCompact_range c.parametrization.continuous
  obtain ⟨ε, hε, hεO⟩ := hcompact.exists_thickening_subset_open hO htrace
  obtain ⟨δ, hδ, hshort⟩ := short_edges c ε hε
  refine ⟨δ, hδ, ?_⟩
  intro Q hmesh x hx
  obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hx
  apply hεO
  exact Metric.mem_thickening_iff.mpr ⟨inscribedVertex c Q i, mem_range_self _,
    (edgeMap_dist_vertex_le c Q i t).trans_lt (hshort Q hmesh i)⟩

/-- The criterion is expressed using the original polygon left-side predicate. -/
theorem transverseRayCriterion : InscribedExpected.transverseRayCriterion := by
  intro n p o U hp hU hfr hrays
  exact polygonLeft_of_transverse_ray p o hp hU hfr hrays

/-- A coherent normal sign follows from the actual two-sided bicollar. -/
theorem coherentJordanOrientation : InscribedExpected.coherentJordanOrientation := by
  intro c A B hA hB hd hu hfA hfB
  exact coherent_jordan_orientation c A B hA hB hd hu hfA hfB

/-- Fine literal inscribed polygons preserve the bounded-left orientation.
The mesh bound simultaneously ensures embedding and the global transverse
collar graph; transport of the original Jordan side supplies the actual side
and the exact left-normal tests for every directed polygon edge. -/
theorem eventualGeometry : InscribedExpected.eventualGeometry := by
  intro c o U hU hleft A
  obtain ⟨δE, hδE, hE⟩ := eventualEmbeddedGeometry c
  obtain ⟨D, δG, hδG, hG⟩ := P202.FineInscribedCollarGraphs.fineGraphs c o A
  refine ⟨min δE δG, lt_min hδE hδG, ?_⟩
  intro Q href hmesh
  have hmE : Q.MeshLT δE := fun i => (hmesh i).trans_le (min_le_left _ _)
  have hmG : Q.MeshLT δG := fun i => (hmesh i).trans_le (min_le_right _ _)
  obtain ⟨hsimple, hnoncusp⟩ := hE Q hmE
  obtain ⟨⟨f, hf, hgraph⟩, htrans⟩ := hG Q href hmG
  refine ⟨hsimple, hnoncusp, ?_⟩
  exact P202.TransversePolygonGraphTransport.transport c o U hU hleft
    D.field D.width D.width_pos D.chart D.source_eq
    (fun q r => D.formula (q, r)) D.smooth_transverse
    Q.count (inscribedPolygon c Q) hsimple f hf hgraph htrans

end P202.PlaneInscribedPolygons
