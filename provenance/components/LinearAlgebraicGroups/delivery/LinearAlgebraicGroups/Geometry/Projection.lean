import LinearAlgebraicGroups.Geometry.CAT0Comparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence

/-! Nearest-point projection onto complete convex subsets of CAT(0) spaces. -/

open Filter Set unitInterval
open scoped Topology

noncomputable section

namespace LinearAlgebraicGroups.Geometry

variable {X : Type*} [MetricSpace X] {C : Set X}

/-- A nearest point to `x` belongs to `C` and minimizes distance from `x` on `C`. -/
def IsNearestPoint (C : Set X) (x p : X) : Prop :=
  p ∈ C ∧ ∀ q ∈ C, dist x p ≤ dist x q

/-- Choose a nearest point when one exists. The input is the fallback value. -/
noncomputable def nearestPoint (C : Set X) (x : X) : X := by
  classical
  exact if h : ∃ p, IsNearestPoint C x p then Classical.choose h else x

private theorem CAT0.exists_nearestPoint (hX : CAT0 X) [CompleteSpace C]
    (hne : C.Nonempty) (hC : GeodesicConvex C) (x : X) :
    ∃ p, IsNearestPoint C x p := by
  let ρ := Metric.infDist x C
  let D := (dist x ·) '' C
  have hD : BddBelow D := ⟨0, by rintro _ ⟨y, _, rfl⟩; exact dist_nonneg⟩
  have hρ : sInf D = ρ := (Metric.isGLB_infDist hne).csInf_eq (hne.image _)
  obtain ⟨v, _, hv, hvD⟩ := exists_seq_tendsto_sInf (hne.image (dist x ·)) hD
  rw [hρ] at hv
  choose u huC hu using hvD
  let w : ℕ → C := fun n => ⟨u n, huC n⟩
  have hw : Tendsto (fun n => dist x (w n : X)) atTop (𝓝 ρ) := by
    simpa only [w, hu] using hv
  have hwSq := hw.pow 2
  have hpair (m n : ℕ) :
      dist (w m) (w n) ^ 2 ≤
        2 * dist x (w m : X) ^ 2 + 2 * dist x (w n : X) ^ 2 - 4 * ρ ^ 2 := by
    obtain ⟨p⟩ := hX.1.2 (w m : X) (w n : X)
    let t : I := ⟨1 / 2, by norm_num⟩
    have hmid := hX.squaredDistanceComparison x p t
    change dist x (p.val t) ^ 2 ≤
      (1 - 1 / 2) * dist x (w m : X) ^ 2 + (1 / 2) * dist x (w n : X) ^ 2 -
        (1 / 2) * (1 - 1 / 2) * dist (w m : X) (w n : X) ^ 2 at hmid
    have hlow : ρ ^ 2 ≤ dist x (p.val t) ^ 2 :=
      (sq_le_sq₀ Metric.infDist_nonneg dist_nonneg).2
        (Metric.infDist_le_dist_of_mem (hC (w m).prop (w n).prop p t))
    change dist (w m : X) (w n : X) ^ 2 ≤ _
    linarith
  have hcauchy : CauchySeq w := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    have hδ : 0 < ε ^ 2 / 4 := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hwSq (ε ^ 2 / 4) hδ
    have hupper (m : ℕ) (hm : N ≤ m) :
        dist x (w m : X) ^ 2 - ρ ^ 2 < ε ^ 2 / 4 := by
      have h := hN m hm
      rw [Real.dist_eq] at h
      exact (abs_lt.mp h).2
    refine ⟨N, fun m hm n hn => (sq_lt_sq₀ dist_nonneg hε.le).1 ?_⟩
    linarith [hpair m n, hupper m hm, hupper n hn]
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hp' : Tendsto (fun n => dist x (w n : X)) atTop (𝓝 (dist x (p : X))) :=
    (continuousAt_const.dist
      (continuous_subtype_val.continuousAt : ContinuousAt ((↑) : C → X) p)).comp hp
  have hdist : dist x (p : X) = ρ := tendsto_nhds_unique hp' hw
  exact ⟨p, p.prop, fun q hq => hdist.le.trans (Metric.infDist_le_dist_of_mem hq)⟩

/-- Along a segment in `C` starting at a nearest point, comparison gives a
Pythagorean lower bound at the other endpoint. -/
theorem CAT0.dist_sq_add_dist_sq_le_of_isNearestPoint (hX : CAT0 X)
    (hC : GeodesicConvex C) {x p q : X} (hp : IsNearestPoint C x p) (hq : q ∈ C) :
    dist x p ^ 2 + dist p q ^ 2 ≤ dist x q ^ 2 := by
  obtain ⟨s⟩ := hX.1.2 p q
  have hlim : Tendsto (fun t : ℝ => (1 - t) * dist p q ^ 2) (𝓝[>] 0)
      (𝓝 (dist p q ^ 2)) := by
    have hc : Continuous (fun t : ℝ => (1 - t) * dist p q ^ 2) :=
      (continuous_const.sub continuous_id).mul continuous_const
    simpa using (hc.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hle : dist p q ^ 2 ≤ dist x q ^ 2 - dist x p ^ 2 := by
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    let r : I := ⟨t, ht.1.le, ht.2.le⟩
    have hmin := (sq_le_sq₀ dist_nonneg dist_nonneg).2 (hp.2 _ (hC hp.1 hq s r))
    have hcmp := hX.squaredDistanceComparison x s r
    change dist x (s.val r) ^ 2 ≤
      (1 - t) * dist x p ^ 2 + t * dist x q ^ 2 - t * (1 - t) * dist p q ^ 2 at hcmp
    by_contra! h
    have hbad := mul_lt_mul_of_pos_left h ht.1
    linarith only [hmin, hcmp, hbad]
  linarith

theorem CAT0.isNearestPoint_unique (hX : CAT0 X) (hC : GeodesicConvex C)
    {x p q : X} (hp : IsNearestPoint C x p) (hq : IsNearestPoint C x q) : p = q := by
  have h₁ := hX.dist_sq_add_dist_sq_le_of_isNearestPoint hC hp hq.1
  have h₂ := (sq_le_sq₀ dist_nonneg dist_nonneg).2 (hq.2 _ hp.1)
  have hzero : dist p q ^ 2 = 0 := by linarith [sq_nonneg (dist p q)]
  exact dist_eq_zero.mp (sq_eq_zero_iff.mp hzero)

/-- The projection is characterized by existence and uniqueness of the nearest point. -/
theorem CAT0.existsUnique_nearestPoint (hX : CAT0 X) [CompleteSpace C]
    (hne : C.Nonempty) (hC : GeodesicConvex C) (x : X) : ∃! p, IsNearestPoint C x p := by
  obtain ⟨p, hp⟩ := hX.exists_nearestPoint hne hC x
  exact ⟨p, hp, fun q hq => hX.isNearestPoint_unique hC hq hp⟩

theorem CAT0.isNearestPoint_nearestPoint (hX : CAT0 X) [CompleteSpace C]
    (hne : C.Nonempty) (hC : GeodesicConvex C) (x : X) :
    IsNearestPoint C x (nearestPoint C x) := by
  classical
  have h := hX.exists_nearestPoint hne hC x
  rw [nearestPoint, dite_eq_left h]
  exact Classical.choose_spec h

theorem CAT0.dist_sq_add_dist_nearestPoint_sq_le (hX : CAT0 X) [CompleteSpace C]
    (hne : C.Nonempty) (hC : GeodesicConvex C) (x : X) {q : X} (hq : q ∈ C) :
    dist x (nearestPoint C x) ^ 2 + dist (nearestPoint C x) q ^ 2 ≤ dist x q ^ 2 :=
  hX.dist_sq_add_dist_sq_le_of_isNearestPoint hC (hX.isNearestPoint_nearestPoint hne hC x) hq

theorem CAT0.lipschitzWith_nearestPoint (hX : CAT0 X) [CompleteSpace C]
    (hne : C.Nonempty) (hC : GeodesicConvex C) : LipschitzWith 1 (nearestPoint C) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let p := nearestPoint C x
  let q := nearestPoint C y
  have hp := hX.isNearestPoint_nearestPoint hne hC x
  have hq := hX.isNearestPoint_nearestPoint hne hC y
  have h₁ := hX.dist_sq_add_dist_sq_le_of_isNearestPoint hC hp hq.1
  have h₂ := hX.dist_sq_add_dist_sq_le_of_isNearestPoint hC hq hp.1
  have hquad := hX.quadrilateral x p q y
  rw [dist_comm p y, dist_comm q y, dist_comm y x] at hquad
  rw [dist_comm q p] at h₂
  change dist x p ^ 2 + dist p q ^ 2 ≤ dist x q ^ 2 at h₁
  change dist y q ^ 2 + dist p q ^ 2 ≤ dist y p ^ 2 at h₂
  simpa only [NNReal.coe_one, one_mul] using
    le_of_sq_le_sq (show dist p q ^ 2 ≤ dist x y ^ 2 by linarith) dist_nonneg

theorem CAT0.nearestPoint_isometry (hX : CAT0 X) [CompleteSpace C]
    (hne : C.Nonempty) (hC : GeodesicConvex C) (g : X ≃ᵢ X) (hg : g '' C = C) (x : X) :
    nearestPoint C (g x) = g (nearestPoint C x) := by
  have hp := hX.isNearestPoint_nearestPoint hne hC x
  apply hX.isNearestPoint_unique hC (hX.isNearestPoint_nearestPoint hne hC (g x))
  refine ⟨?_, fun q hq => ?_⟩
  · have hmem := mem_image_of_mem g hp.1
    simpa only [hg] using hmem
  · obtain ⟨r, hr, rfl⟩ := hg.symm ▸ hq
    simpa only [g.isometry.dist_eq] using hp.2 r hr

theorem CAT0.closedConvex_minset [CompleteSpace X] (hX : CAT0 X) (g : X ≃ᵢ X) :
    IsClosed (minset g) ∧ GeodesicConvex (minset g) ∧ CompleteSpace (minset g) :=
  ⟨isClosed_minset g, hX.geodesicConvex_minset g, (isClosed_minset g).completeSpace_coe⟩

theorem CAT0.closedConvex_commonMinset [CompleteSpace X] (hX : CAT0 X)
    {ι : Type*} (f : ι → X ≃ᵢ X) :
    IsClosed (commonMinset f) ∧ GeodesicConvex (commonMinset f) ∧
      CompleteSpace (commonMinset f) :=
  ⟨isClosed_commonMinset f, hX.geodesicConvex_commonMinset f,
    (isClosed_commonMinset f).completeSpace_coe⟩

/-- A nearest point to the endpoint is still nearest along the segment from it. -/
theorem IsNearestPoint.along_segment {p x : X} (hp : IsNearestPoint C x p)
    (a : GeodesicSegment p x) (s : I) : IsNearestPoint C (a.val s) p := by
  refine ⟨hp.1, fun q hq => ?_⟩
  have hadd : dist x (a.val s) + dist (a.val s) p = dist x p := by
    rw [dist_comm x (a.val s), dist_comm (a.val s) p, dist_comm x p,
      a.dist_target, a.dist_source]
    ring
  linarith only [hadd, hp.2 q hq, dist_triangle x (a.val s) q]

/-- The angle at `p) in the Euclidean comparison triangle, by the cosine law. -/
noncomputable def comparisonAngle (p x y : X) : ℝ :=
  Real.arccos ((dist p x ^ 2 + dist p y ^ 2 - dist x y ^ 2) /
    (2 * dist p x * dist p y))

/-- The comparison angle on two segments at positive constant-speed parameters. -/
noncomputable def segmentComparisonAngle {p x y : X}
    (a : GeodesicSegment p x) (b : GeodesicSegment p y)
    (st : Ioc (0 : ℝ) 1 × Ioc (0 : ℝ) 1) : ℝ :=
  comparisonAngle p (a.val ⟨st.1, st.1.prop.1.le, st.1.prop.2⟩)
    (b.val ⟨st.2, st.2.prop.1.le, st.2.prop.2⟩)

/-- The Alexandrov angle between two nonconstant segments with a common source,
expressed as the infimum of their comparison angles in a CAT(0) space. -/
noncomputable def alexandrovAngle {p x y : X}
    (a : GeodesicSegment p x) (b : GeodesicSegment p y) : ℝ :=
  ⨅ st, segmentComparisonAngle a b st

private theorem comparisonAngle_comm (p x y : X) :
    comparisonAngle p x y = comparisonAngle p y x := by
  simp [comparisonAngle, dist_comm x y, add_comm, mul_comm, mul_left_comm]

private theorem CAT0.comparisonAngle_mono (hX : CAT0 X) {p x z : X}
    (hx : p ≠ x) (hz : p ≠ z) (a : GeodesicSegment p x)
    (s t : I) (hs : 0 < (s : ℝ)) (hst : (s : ℝ) ≤ (t : ℝ)) :
    comparisonAngle p (a.val s) z ≤ comparisonAngle p (a.val t) z := by
  have ht := hs.trans_le hst
  let r : I := ⟨(s : ℝ) / (t : ℝ), (div_pos hs ht).le, (div_le_one ht).2 hst⟩
  have hr : 0 < (r : ℝ) := div_pos hs ht
  have hrt : (r : ℝ) * (t : ℝ) = (s : ℝ) := div_mul_cancel₀ _ ht.ne'
  have hparam : Icc.convexComb (0 : I) t r = s := by
    apply Subtype.ext
    change (1 - (r : ℝ)) * 0 + (r : ℝ) * (t : ℝ) = (s : ℝ)
    rw [mul_zero, zero_add, hrt]
  have hcmp := hX.squaredDistanceComparison z (a.subpath 0 t) r
  change dist z (a.val (Icc.convexComb 0 t r)) ^ 2 ≤
    (1 - (r : ℝ)) * dist z (a.val 0) ^ 2 + (r : ℝ) * dist z (a.val t) ^ 2 -
      (r : ℝ) * (1 - (r : ℝ)) * dist (a.val 0) (a.val t) ^ 2 at hcmp
  rw [hparam, Path.source, dist_comm z p, dist_comm z (a.val t),
    dist_comm z (a.val s)] at hcmp
  have hlen : dist p (a.val s) = (r : ℝ) * dist p (a.val t) := by
    rw [a.dist_source, a.dist_source, ← mul_assoc, hrt]
  have hpos : 0 < dist p (a.val t) := by
    rw [a.dist_source]
    exact mul_pos ht (dist_pos.mpr hx)
  have hD : 0 < 2 * dist p (a.val t) * dist p z :=
    mul_pos (mul_pos two_pos hpos) (dist_pos.mpr hz)
  unfold comparisonAngle
  apply Real.arccos_le_arccos
  rw [hlen, show 2 * ((r : ℝ) * dist p (a.val t)) * dist p z =
      (r : ℝ) * (2 * dist p (a.val t) * dist p z) by ring,
    div_le_div_iff₀ hD (mul_pos hr hD)]
  have hnum : (r : ℝ) *
      (dist p (a.val t) ^ 2 + dist p z ^ 2 - dist (a.val t) z ^ 2) ≤
      ((r : ℝ) * dist p (a.val t)) ^ 2 + dist p z ^ 2 - dist (a.val s) z ^ 2 := by
    linarith only [hcmp]
  convert mul_le_mul_of_nonneg_right hnum hD.le using 1
  ring

/-- The infimum of comparison angles is their joint limit as both positive
parameters decrease to zero. -/
theorem CAT0.tendsto_segmentComparisonAngle (hX : CAT0 X) {p x y : X}
    (hx : p ≠ x) (hy : p ≠ y) (a : GeodesicSegment p x) (b : GeodesicSegment p y) :
    Tendsto (segmentComparisonAngle a b) atBot (𝓝 (alexandrovAngle a b)) := by
  apply tendsto_atBot_ciInf
  · rintro ⟨s, u⟩ ⟨t, v⟩ ⟨hst, huv⟩
    let s' : I := ⟨s, s.prop.1.le, s.prop.2⟩
    let t' : I := ⟨t, t.prop.1.le, t.prop.2⟩
    let u' : I := ⟨u, u.prop.1.le, u.prop.2⟩
    let v' : I := ⟨v, v.prop.1.le, v.prop.2⟩
    change comparisonAngle p (a.val s') (b.val u') ≤ comparisonAngle p (a.val t') (b.val v')
    have hu : p ≠ b.val u' := by
      apply dist_pos.mp
      rw [b.dist_source]
      exact mul_pos u.prop.1 (dist_pos.mpr hy)
    have ht : p ≠ a.val t' := by
      apply dist_pos.mp
      rw [a.dist_source]
      exact mul_pos t.prop.1 (dist_pos.mpr hx)
    calc
      comparisonAngle p (a.val s') (b.val u') ≤ comparisonAngle p (a.val t') (b.val u') :=
        hX.comparisonAngle_mono hx hu a s' t' s.prop.1 hst
      _ ≤ comparisonAngle p (a.val t') (b.val v') := by
        rw [comparisonAngle_comm p (a.val t') (b.val u'),
          comparisonAngle_comm p (a.val t') (b.val v')]
        exact hX.comparisonAngle_mono hy ht b u' v' u.prop.1 huv
  · exact ⟨0, by rintro _ ⟨st, rfl⟩; exact Real.arccos_nonneg _⟩

/-- Any nonconstant segment from a projection point to the projected point
makes at least a right angle with any nonconstant segment in the convex set. -/
theorem CAT0.pi_div_two_le_alexandrovAngle_of_isNearestPoint (hX : CAT0 X)
    (hC : GeodesicConvex C) {p x q : X} (hp : IsNearestPoint C x p) (hq : q ∈ C)
    (hx : p ≠ x) (hpq : p ≠ q) (a : GeodesicSegment p x) (b : GeodesicSegment p q) :
    Real.pi / 2 ≤ alexandrovAngle a b := by
  let one : Ioc (0 : ℝ) 1 := ⟨1, zero_lt_one, le_rfl⟩
  let : Nonempty (Ioc (0 : ℝ) 1 × Ioc (0 : ℝ) 1) := ⟨(one, one)⟩
  apply le_ciInf
  rintro ⟨s, t⟩
  let s' : I := ⟨s, s.prop.1.le, s.prop.2⟩
  let t' : I := ⟨t, t.prop.1.le, t.prop.2⟩
  have hpy : 0 < dist p (a.val s') := by
    rw [a.dist_source]
    exact mul_pos s.prop.1 (dist_pos.mpr hx)
  have hpz : 0 < dist p (b.val t') := by
    rw [b.dist_source]
    exact mul_pos t.prop.1 (dist_pos.mpr hpq)
  have h := hX.dist_sq_add_dist_sq_le_of_isNearestPoint hC
    (hp.along_segment a s') (hC hp.1 hq b t')
  change Real.pi / 2 ≤ comparisonAngle p (a.val s') (b.val t')
  rw [comparisonAngle, ← Real.arccos_zero]
  apply Real.arccos_le_arccos
  apply div_nonpos_of_nonpos_of_nonneg _ (mul_pos (mul_pos two_pos hpy) hpz).le
  rw [dist_comm p (a.val s')]
  linarith only [h]

private theorem image_minset_of_commute (a b : X ≃ᵢ X) (hab : Function.Commute a b) :
    b '' minset a = minset a := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change dist y (a y) = translationLength a at hy
    change dist (b y) (a (b y)) = translationLength a
    rw [hab y, b.isometry.dist_eq, hy]
  · intro hx
    obtain ⟨y, rfl⟩ := b.surjective x
    refine ⟨y, ?_, rfl⟩
    change dist (b y) (a (b y)) = translationLength a at hx
    rwa [hab y, b.isometry.dist_eq] at hx

/-- The projection used in the flat torus induction preserves displacement
minimizers of an isometry commuting with the one defining the target minset. -/
theorem CAT0.nearestPoint_minset_mem_minset [CompleteSpace X] (hX : CAT0 X)
    (a b : X ≃ᵢ X) (ha : IsSemisimple a) (hab : Function.Commute a b)
    {x : X} (hx : x ∈ minset b) :
    nearestPoint (minset a) x ∈ minset a ∩ minset b := by
  obtain ⟨_, hconv, hcomplete⟩ := hX.closedConvex_minset a
  let _ : CompleteSpace (minset a) := hcomplete
  have hmap := hX.nearestPoint_isometry ha hconv b (image_minset_of_commute a b hab) x
  refine ⟨(hX.isNearestPoint_nearestPoint ha hconv x).1, ?_⟩
  have hle := (hX.lipschitzWith_nearestPoint ha hconv).dist_le_mul x (b x)
  rw [hmap, NNReal.coe_one, one_mul] at hle
  change dist x (b x) = translationLength b at hx
  rw [hx] at hle
  exact le_antisymm hle (ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact dist_nonneg⟩ _)

end LinearAlgebraicGroups.Geometry
