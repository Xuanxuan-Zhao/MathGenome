import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Geometry.Projection
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic
/-! Axes of positive-length semisimple isometries of CAT(0) spaces. -/

open Set unitInterval
open scoped Topology

noncomputable section

namespace LinearAlgebraicGroups.Geometry

variable {X : Type*} [MetricSpace X]

/-- An oriented, unit-speed line on which the isometry translates by `L`. -/
def IsAxis (a : X ≃ᵢ X) (L : ℝ) (c : ℝ → X) : Prop :=
  Isometry c ∧ ∀ t : ℝ, a (c t) = c (t + L)

/-- Time zero on the second axis is the nearest point to time zero on the first. -/
def AxesAligned (c d : ℝ → X) : Prop :=
  IsNearestPoint (range d) (c 0) (d 0)

/-- The Busemann function of an oriented line, expressed as the infimum of the
distance deficits. For a unit-speed line the deficits decrease with time. -/
def axisBusemann (c : ℝ → X) (x : X) : ℝ :=
  ⨅ t : ℝ, dist x (c t) - t

/-- The time-zero cross-section of the minimum set. -/
def axisCrossSection (a : X ≃ᵢ X) (c : ℝ → X) : Set X :=
  {x | x ∈ minset a ∧ axisBusemann c x = 0}

private abbrev half : I := ⟨1 / 2, by norm_num⟩

private theorem length_le_displacement (a : X ≃ᵢ X) (x : X) :
    translationLength a ≤ dist x (a x) :=
  ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact dist_nonneg⟩ x

private def lineSegment {c : ℝ → X} (hc : Isometry c) (s t : ℝ) :
    GeodesicSegment (c s) (c t) := by
  refine ⟨⟨⟨fun u => c ((1 - (u : ℝ)) * s + (u : ℝ) * t),
      hc.continuous.comp (by fun_prop)⟩, by simp, by simp⟩, ?_⟩
  intro u v
  change dist (c _) (c _) = _
  rw [hc.dist_eq, hc.dist_eq s t]
  simp only [Real.dist_eq, Subtype.dist_eq]
  rw [show (1 - (u : ℝ)) * s + (u : ℝ) * t -
      ((1 - (v : ℝ)) * s + (v : ℝ) * t) = ((u : ℝ) - (v : ℝ)) * (t - s) by ring,
    abs_mul, abs_sub_comm t s]

private theorem lineSegment_apply {c : ℝ → X} (hc : Isometry c) (s t : ℝ) (u : I) :
    (lineSegment hc s t).val u = c ((1 - (u : ℝ)) * s + (u : ℝ) * t) := rfl

private theorem line_convex (hX : CAT0 X) {c : ℝ → X} (hc : Isometry c) :
    GeodesicConvex (range c) := by
  rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩ p u
  have h := (hX.uniquelyGeodesic.2 (c s) (c t)).elim p (lineSegment hc s t)
  rw [h, lineSegment_apply]
  exact mem_range_self _

private theorem line_complete {c : ℝ → X} (hc : Isometry c) : CompleteSpace (range c) :=
  hc.isometryEquivOnRange.symm.completeSpace

/-- A positively translated unit-speed line realizes the translation length. -/
theorem IsAxis.translationLength_eq (hX : CAT0 X) {a : X ≃ᵢ X}
    {L : ℝ} {c : ℝ → X} (hc : IsAxis a L c) (hL : 0 < L) :
    translationLength a = L := by
  have hdisp (t : ℝ) : dist (c t) (a (c t)) = L := by
    rw [hc.2, hc.1.dist_eq, Real.dist_eq, show t - (t + L) = -L by ring, abs_neg,
      abs_of_pos hL]
  apply le_antisymm ((length_le_displacement a (c 0)).trans_eq (hdisp 0))
  have hr : a '' range c = range c := by
    ext y
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      rw [hc.2]
      exact mem_range_self _
    · rintro ⟨t, rfl⟩
      exact ⟨c (t - L), mem_range_self _, by rw [hc.2, sub_add_cancel]⟩
  let := line_complete hc.1
  have hn : (range c).Nonempty := ⟨c 0, mem_range_self 0⟩
  have hv := line_convex hX hc.1
  let : Nonempty X := ⟨c 0⟩
  apply le_ciInf
  intro x
  obtain ⟨t, ht⟩ := (hX.isNearestPoint_nearestPoint hn hv x).1
  have h := (hX.lipschitzWith_nearestPoint hn hv).dist_le_mul x (a x)
  rw [hX.nearestPoint_isometry hn hv a hr, ← ht, hdisp, NNReal.coe_one, one_mul] at h
  exact h

theorem IsAxis.mem_minset {a : X ≃ᵢ X} {c : ℝ → X}
    (hc : IsAxis a (translationLength a) c) (hL : 0 < translationLength a) (t : ℝ) :
    c t ∈ minset a := by
  change dist (c t) (a (c t)) = translationLength a
  rw [hc.2, hc.1.dist_eq, Real.dist_eq, show t - (t + translationLength a) =
    -translationLength a by ring, abs_neg, abs_of_pos hL]

private theorem dist_apply_apply_of_mem_minset (hX : CAT0 X) {a : X ≃ᵢ X} {x : X}
    (hx : x ∈ minset a) : dist x (a (a x)) = 2 * translationLength a := by
  obtain ⟨p⟩ := hX.1.2 x (a x)
  let m := p.val half
  have hu := hX.distAlongSegments p.reverse (p.mapIsometry a.isometry) half
  change dist (p.val (σ half)) (a m) ≤
    (1 - (1 / 2 : ℝ)) * dist (a x) (a x) + (1 / 2 : ℝ) * dist x (a (a x)) at hu
  have hs : σ half = half := by
    apply Subtype.ext
    norm_num [unitInterval.coe_symm_eq]
  rw [hs, dist_self, mul_zero, zero_add] at hu
  change dist x (a x) = translationLength a at hx
  have hv := dist_triangle x (a x) (a (a x))
  rw [a.isometry.dist_eq, hx] at hv
  linarith only [hu, hv, length_le_displacement a m]

private theorem midpoint_of_dist_eq (hX : CAT0 X) {u v w : X}
    (p : GeodesicSegment u w) (h₁ : dist u v = dist v w)
    (h₂ : dist u w = 2 * dist v w) : p.val half = v := by
  have h := hX.squaredDistanceComparison.midpointComparison v p
  change dist v (p.val half) ^ 2 ≤ _ at h
  rw [dist_comm v u, h₁, h₂] at h
  exact (dist_eq_zero.mp (by nlinarith only [h, dist_nonneg (x := v) (y := p.val half)])).symm

private theorem dist_nat_orbit (hX : CAT0 X) {a : X ≃ᵢ X} {x : X}
    (hx : x ∈ minset a) (hL : 0 < translationLength a) (n : ℕ) :
    dist x ((a ^ n) x) = n * translationLength a := by
  have hx1 : dist x (a x) = translationLength a := hx
  have hstep (k : ℕ) : dist ((a ^ k) x) ((a ^ (k + 1)) x) = translationLength a := by
    rw [pow_succ, IsometryEquiv.mul_apply, (a ^ k).isometry.dist_eq, hx1]
  have hstep2 (k : ℕ) : dist ((a ^ k) x) ((a ^ (k + 2)) x) = 2 * translationLength a := by
    rw [pow_add, IsometryEquiv.mul_apply, (a ^ k).isometry.dist_eq]
    simpa only [pow_two, IsometryEquiv.mul_apply] using dist_apply_apply_of_mem_minset hX hx
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using hx1
  | more k hk hk1 =>
    obtain ⟨p⟩ := hX.1.2 ((a ^ k) x) ((a ^ (k + 2)) x)
    have hm : p.val half = (a ^ (k + 1)) x :=
      midpoint_of_dist_eq hX p ((hstep k).trans (hstep (k + 1)).symm)
        ((hstep2 k).trans (congrArg (2 * ·) (hstep (k + 1)).symm))
    have hcn := hX.squaredDistanceComparison.midpointComparison x p
    change dist x (p.val half) ^ 2 ≤ _ at hcn
    rw [hm, hk1, hk, hstep2] at hcn
    have hu := dist_triangle x ((a ^ (k + 1)) x) ((a ^ (k + 2)) x)
    rw [hk1, hstep (k + 1)] at hu
    push_cast at hcn hu ⊢
    apply le_antisymm (by linarith only [hu])
    apply (sq_le_sq₀ (mul_nonneg (by positivity) hL.le) dist_nonneg).mp
    nlinarith only [hcn]

private theorem dist_int_orbit (hX : CAT0 X) {a : X ≃ᵢ X} {x : X}
    (hx : x ∈ minset a) (hL : 0 < translationLength a) {i j : ℤ} (hij : i ≤ j) :
    dist ((a ^ i) x) ((a ^ j) x) = ((j : ℝ) - (i : ℝ)) * translationLength a := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hij)
  have hj : j = i + (n : ℤ) := by omega
  rw [hj, zpow_add, IsometryEquiv.mul_apply, (a ^ i).isometry.dist_eq, zpow_natCast,
    dist_nat_orbit hX hx hL]
  push_cast
  ring

private def fractionalTime (t : ℝ) : I :=
  ⟨t - ⌊t⌋, sub_nonneg.mpr (Int.floor_le t), by linarith [Int.lt_floor_add_one t]⟩

private theorem fractionalTime_add_one (t : ℝ) : fractionalTime (t + 1) = fractionalTime t := by
  apply Subtype.ext
  change t + 1 - (⌊t + 1⌋ : ℝ) = t - (⌊t⌋ : ℝ)
  push_cast [Int.floor_add_one]
  ring

private theorem dist_interpolated_orbit (hX : CAT0 X) {a : X ≃ᵢ X} {x : X}
    (hx : x ∈ minset a) (hL : 0 < translationLength a)
    (p : GeodesicSegment x (a x)) {s t : ℝ} (hst : s ≤ t) :
    dist ((a ^ ⌊s⌋) (p.val (fractionalTime s)))
      ((a ^ ⌊t⌋) (p.val (fractionalTime t))) = (t - s) * translationLength a := by
  let q (i : ℤ) := (a ^ i) x
  let R (i : ℤ) (u : I) := (a ^ i) (p.val u)
  let i := ⌊s⌋
  let j := ⌊t⌋
  let u := fractionalTime s
  let v := fractionalTime t
  have hx1 : dist x (a x) = translationLength a := hx
  have hq (k l : ℤ) (hkl : k ≤ l) :
      dist (q k) (q l) = ((l : ℝ) - (k : ℝ)) * translationLength a :=
    dist_int_orbit hX hx hL hkl
  have hleft (k : ℤ) (w : I) : dist (q k) (R k w) = (w : ℝ) * translationLength a := by
    dsimp [q, R]
    rw [(a ^ k).isometry.dist_eq, p.dist_source, hx1]
  have hright (k : ℤ) (w : I) :
      dist (R k w) (q (k + 1)) = (1 - (w : ℝ)) * translationLength a := by
    dsimp [R, q]
    rw [zpow_add, zpow_one, IsometryEquiv.mul_apply, (a ^ k).isometry.dist_eq,
      p.dist_target, hx1]
  have hij : i ≤ j := Int.floor_mono hst
  have hu : (u : ℝ) = s - (i : ℝ) := rfl
  have hv : (v : ℝ) = t - (j : ℝ) := rfl
  change dist (R i u) (R j v) = _
  rcases hij.eq_or_lt with heq | hlt
  · rw [← heq]
    dsimp [R]
    rw [(a ^ i).isometry.dist_eq, p.prop, hx1, Subtype.dist_eq, Real.dist_eq,
      hu, hv, ← heq, abs_of_nonpos (by linarith)]
    ring
  · have h₁ := dist_triangle4 (R i u) (q (i + 1)) (q j) (R j v)
    rw [hright, hq _ _ (by omega), hleft, hu, hv] at h₁
    have h₂ := dist_triangle4 (q i) (R i u) (R j v) (q (j + 1))
    rw [hq _ _ (by omega), hleft, hright, hu, hv] at h₂
    push_cast at h₁ h₂
    apply le_antisymm <;> linarith only [h₁, h₂]

/-- Every point of the minimum set of a positive-length isometry lies on an axis. -/
theorem CAT0.exists_axis (hX : CAT0 X) {a : X ≃ᵢ X} (hL : 0 < translationLength a)
    {x : X} (hx : x ∈ minset a) :
    ∃ c : ℝ → X, IsAxis a (translationLength a) c ∧ c 0 = x := by
  obtain ⟨p⟩ := hX.1.2 x (a x)
  let L := translationLength a
  let c (t : ℝ) := (a ^ ⌊t / L⌋) (p.val (fractionalTime (t / L)))
  have hd (s t : ℝ) (hst : s ≤ t) : dist (c s) (c t) = t - s := by
    dsimp [c]
    rw [dist_interpolated_orbit hX hx hL p ((div_le_div_iff_of_pos_right hL).mpr hst),
      ← sub_div, div_mul_cancel₀ _ hL.ne']
  refine ⟨c, ⟨Isometry.of_dist_eq (fun s t => ?_), fun t => ?_⟩, ?_⟩
  · rcases le_total s t with hst | hts
    · rw [hd s t hst, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    · rw [dist_comm (c s), hd t s hts, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
  · have ht : (t + L) / L = t / L + 1 := by rw [add_div, div_self hL.ne']
    dsimp [c]
    rw [ht, fractionalTime_add_one, Int.floor_add_one, add_comm _ (1 : ℤ), zpow_add,
      zpow_one, IsometryEquiv.mul_apply]
  · have hzero : fractionalTime 0 = 0 := by
      apply Subtype.ext
      change (0 : ℝ) - (⌊(0 : ℝ)⌋ : ℝ) = 0
      simp
    simp [c, hzero]

private theorem IsAxis.shift {a : X ≃ᵢ X} {L : ℝ} {c : ℝ → X}
    (hc : IsAxis a L c) (r : ℝ) : IsAxis a L (fun t => c (t + r)) := by
  refine ⟨Isometry.of_dist_eq (fun s t => ?_), fun t => ?_⟩
  · rw [hc.1.dist_eq, Real.dist_eq, Real.dist_eq, add_sub_add_right_eq_sub]
  · rw [hc.2, add_right_comm t r L]

private theorem IsAxis.map {a b : X ≃ᵢ X} {L : ℝ} {c : ℝ → X}
    (hc : IsAxis a L c) (hab : Function.Commute a b) : IsAxis a L (fun t => b (c t)) :=
  ⟨b.isometry.comp hc.1, fun t => (hab (c t)).trans (congrArg b (hc.2 t))⟩

/-- The distance between two axes at a fixed offset is constant. -/
theorem CAT0.axis_dist_offset (hX : CAT0 X) {a : X ≃ᵢ X} {L : ℝ} (hL : 0 < L)
    {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d) (r s t : ℝ) :
    dist (c s) (d (s + r)) = dist (c t) (d (t + r)) := by
  let f (x : ℝ) := dist (c x) (d (x + r))
  have hper : Function.Periodic f L := fun x => by
    dsimp [f]
    rw [add_right_comm x L r, ← hc.2, ← hd.2, a.dist_eq]
  have hle (x y : ℝ) : f y ≤ f x := by
    let n : ℤ := ⌊(y - x) / L⌋
    let u := fractionalTime ((y - x) / L)
    let A := x + (n : ℝ) * L
    let B := A + L
    have hA : f A = f x := hper.int_mul n x
    have hB : f B = f x := (hper A).trans hA
    have hu : (u : ℝ) = (y - x) / L - (n : ℝ) := rfl
    have hcoord : (1 - (u : ℝ)) * A + (u : ℝ) * B = y := by
      dsimp [A, B]
      rw [hu]
      linear_combination div_mul_cancel₀ (y - x) hL.ne'
    have hcoord' : (1 - (u : ℝ)) * (A + r) + (u : ℝ) * (B + r) = y + r := by
      linear_combination hcoord
    have h := hX.distAlongSegments (lineSegment hc.1 A B)
      (lineSegment hd.1 (A + r) (B + r)) u
    rw [lineSegment_apply, lineSegment_apply, hcoord, hcoord'] at h
    change f y ≤ (1 - (u : ℝ)) * f A + (u : ℝ) * f B at h
    rw [hA, hB] at h
    linarith only [h]
  exact (hle t s).antisymm (hle s t)

private theorem axis_dist_cross_zero (hX : CAT0 X) {a : X ≃ᵢ X} {L : ℝ}
    (hL : 0 < L) {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d) (s t : ℝ) :
    dist (c s) (d t) = dist (c 0) (d (t - s)) := by
  simpa only [add_sub_cancel, zero_add] using hX.axis_dist_offset hL hc hd (t - s) s 0

/-- Synchronously aligned points are mutual nearest points. -/
theorem CAT0.axis_nearestPoints (hX : CAT0 X) {a : X ≃ᵢ X} {L : ℝ}
    (hL : 0 < L) {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d)
    (hcd : AxesAligned c d) (t : ℝ) :
    IsNearestPoint (range d) (c t) (d t) ∧ IsNearestPoint (range c) (d t) (c t) := by
  have he (s r : ℝ) := axis_dist_cross_zero hX hL hc hd s r
  have hdiag : dist (c t) (d t) = dist (c 0) (d 0) := by rw [he, sub_self]
  constructor
  · refine ⟨mem_range_self _, ?_⟩
    rintro _ ⟨u, rfl⟩
    rw [hdiag, he t u]
    exact hcd.2 _ (mem_range_self _)
  · refine ⟨mem_range_self _, ?_⟩
    rintro _ ⟨u, rfl⟩
    rw [dist_comm (d t) (c t), dist_comm (d t) (c u), hdiag, he u t]
    exact hcd.2 _ (mem_range_self _)

/-- The squared distance between points of aligned axes is Euclidean. -/
theorem CAT0.aligned_axis_dist_sq (hX : CAT0 X) {a : X ≃ᵢ X} {L : ℝ}
    (hL : 0 < L) {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d)
    (hcd : AxesAligned c d) (s t : ℝ) :
    dist (c s) (d t) ^ 2 = dist (c 0) (d 0) ^ 2 + (s - t) ^ 2 := by
  have hnear (u : ℝ) := hX.axis_nearestPoints hL hc hd hcd u
  have hd₁ := hX.dist_sq_add_dist_sq_le_of_isNearestPoint (line_convex hX hd.1)
    (hnear s).1 (mem_range_self t)
  have hd₂ := hX.dist_sq_add_dist_sq_le_of_isNearestPoint (line_convex hX hd.1)
    (hnear t).1 (mem_range_self s)
  have hquad := hX.quadrilateral (c s) (c t) (d t) (d s)
  have hdiag (u : ℝ) : dist (c u) (d u) = dist (c 0) (d 0) := by
    rw [axis_dist_cross_zero hX hL hc hd, sub_self]
  rw [hdiag, hd.1.dist_eq, Real.dist_eq, sq_abs] at hd₁ hd₂
  rw [dist_comm (d s) (c s), hc.1.dist_eq s t,
    hd.1.dist_eq t s, hdiag s, hdiag t, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs] at hquad
  apply le_antisymm _ hd₁
  nlinarith only [hquad, hd₂]

private theorem axis_bddBelow {c : ℝ → X} (hc : Isometry c) (x : X) :
    BddBelow (range (fun t : ℝ => dist x (c t) - t)) := by
  refine ⟨-dist x (c 0), ?_⟩
  rintro _ ⟨t, rfl⟩
  have h := dist_triangle (c t) x (c 0)
  rw [dist_comm (c t) x, hc.dist_eq, Real.dist_eq, sub_zero] at h
  linarith only [h, le_abs_self t]

private theorem axisBusemann_le {c : ℝ → X} (hc : Isometry c) (x : X) (t : ℝ) :
    axisBusemann c x ≤ dist x (c t) - t :=
  ciInf_le (axis_bddBelow hc x) t

theorem axisBusemann_self {c : ℝ → X} (hc : Isometry c) (s : ℝ) :
    axisBusemann c (c s) = -s := by
  apply le_antisymm
  · simpa using axisBusemann_le hc (c s) s
  · apply le_ciInf
    intro t
    rw [hc.dist_eq, Real.dist_eq, abs_sub_comm s t]
    linarith only [le_abs_self (t - s)]

/-- The distance deficit infimum is the forward Busemann limit. -/
theorem tendsto_axisBusemann {c : ℝ → X} (hc : Isometry c) (x : X) :
    Filter.Tendsto (fun t : ℝ => dist x (c t) - t) Filter.atTop (𝓝 (axisBusemann c x)) := by
  apply tendsto_atTop_ciInf
  · intro s t hst
    have h := dist_triangle x (c s) (c t)
    rw [hc.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] at h
    linarith only [h]
  · exact axis_bddBelow hc x

theorem lipschitzWith_axisBusemann {c : ℝ → X} (hc : Isometry c) :
    LipschitzWith 1 (axisBusemann c) := by
  have h (x y : X) : axisBusemann c x - axisBusemann c y ≤ dist x y := by
    suffices axisBusemann c x - dist x y ≤ axisBusemann c y by linarith only [this]
    apply le_ciInf
    intro t
    linarith only [axisBusemann_le hc x t, dist_triangle x y (c t)]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_le]
  constructor
  · have hyx := h y x
    rw [dist_comm y x] at hyx
    linarith only [hyx]
  · exact h x y

private theorem axisBusemann_shift {c : ℝ → X} (hc : Isometry c) (r : ℝ) (x : X) :
    axisBusemann (fun t => c (t + r)) x = axisBusemann c x + r := by
  have hshift : Isometry (fun t => c (t + r)) := Isometry.of_dist_eq fun s t => by
    rw [hc.dist_eq, Real.dist_eq, Real.dist_eq, add_sub_add_right_eq_sub]
  apply le_antisymm
  · suffices axisBusemann (fun t => c (t + r)) x - r ≤ axisBusemann c x by
      linarith only [this]
    apply le_ciInf
    intro t
    have h := axisBusemann_le hshift x (t - r)
    simp only [sub_add_cancel] at h
    linarith only [h]
  · apply le_ciInf
    intro t
    linarith only [axisBusemann_le hc x (t + r)]

/-- Aligned axes have the same Busemann function on the entire ambient space. -/
theorem CAT0.axisBusemann_eq_of_aligned (hX : CAT0 X) {a : X ≃ᵢ X} {L : ℝ}
    (hL : 0 < L) {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d)
    (hcd : AxesAligned c d) : axisBusemann c = axisBusemann d := by
  have hle {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d)
      (hcd : AxesAligned c d) (x : X) : axisBusemann d x ≤ axisBusemann c x := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let D := dist (c 0) (d 0)
    let h := (D ^ 2 + 1) / ε
    have hh : 0 < h := div_pos (by positivity) hε
    have hhε : h * ε = D ^ 2 + 1 := div_mul_cancel₀ _ hε.ne'
    suffices axisBusemann d x - ε ≤ axisBusemann c x by linarith only [this]
    apply le_ciInf
    intro t
    have he := hX.aligned_axis_dist_sq hL hc hd hcd t (t + h)
    have hv : dist (c t) (d (t + h)) ≤ h + ε := by
      apply (sq_le_sq₀ dist_nonneg (add_nonneg hh.le hε.le)).mp
      change dist (c t) (d (t + h)) ^ 2 = D ^ 2 + (t - (t + h)) ^ 2 at he
      nlinarith only [he, hhε, sq_nonneg ε, sq_nonneg D]
    linarith only [axisBusemann_le hd.1 x (t + h), dist_triangle x (c t) (d (t + h)), hv]
  funext x
  exact (hle hd hc (hX.axis_nearestPoints hL hc hd hcd 0).2 x).antisymm (hle hc hd hcd x)

private theorem exists_aligned_shift (hX : CAT0 X) {c d : ℝ → X} (hd : Isometry d) :
    ∃ r : ℝ, AxesAligned c (fun t => d (t + r)) := by
  let := line_complete hd
  have hn : (range d).Nonempty := ⟨d 0, mem_range_self 0⟩
  have hp := hX.isNearestPoint_nearestPoint hn (line_convex hX hd) (c 0)
  obtain ⟨r, hr⟩ := hp.1
  refine ⟨r, ?_⟩
  have hshiftRange : range (fun t => d (t + r)) = range d := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact mem_range_self _
    · rintro ⟨s, rfl⟩
      exact ⟨s - r, by simp⟩
  change IsNearestPoint (range (fun t => d (t + r))) (c 0) (d (0 + r))
  rwa [hshiftRange, zero_add, hr]

/-- The Busemann functions of two axes differ by their time-origin offset. -/
theorem CAT0.axisBusemann_eq_add (hX : CAT0 X) {a : X ≃ᵢ X} {L : ℝ}
    (hL : 0 < L) {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d) (x : X) :
    axisBusemann c x = axisBusemann d x + axisBusemann c (d 0) := by
  obtain ⟨r, hr⟩ := exists_aligned_shift (c := c) hX hd.1
  have h (y : X) := congrFun (hX.axisBusemann_eq_of_aligned hL hc (hd.shift r) hr) y
  have h₀ := h (d 0)
  rw [axisBusemann_shift hd.1, axisBusemann_self hd.1, neg_zero, zero_add] at h₀
  rw [h x, axisBusemann_shift hd.1, h₀]

theorem CAT0.axesAligned_iff_axisBusemann_eq (hX : CAT0 X) {a : X ≃ᵢ X} {L : ℝ}
    (hL : 0 < L) {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d) :
    AxesAligned c d ↔ axisBusemann c = axisBusemann d := by
  refine ⟨hX.axisBusemann_eq_of_aligned hL hc hd, fun he => ?_⟩
  obtain ⟨r, hr⟩ := exists_aligned_shift (c := c) hX hd.1
  have he' := hX.axisBusemann_eq_of_aligned hL hc (hd.shift r) hr
  have hz := congrFun he' (d 0)
  rw [axisBusemann_shift hd.1, he] at hz
  have hzero : r = 0 := by linarith only [hz]
  simpa [hzero] using hr

private theorem axis_eq_of_same_origin (hX : CAT0 X) {a : X ≃ᵢ X} {L : ℝ}
    (hL : 0 < L) {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d)
    (hzero : c 0 = d 0) : c = d := by
  funext t
  apply dist_eq_zero.mp
  simpa [hzero] using hX.axis_dist_offset hL hc hd 0 t 0

private theorem geodesic_map_apply_eq (hX : CAT0 X) (a : X ≃ᵢ X)
    {x y x' y' : X} (hx : a x = x') (hy : a y = y') (p : GeodesicSegment x y)
    (q : GeodesicSegment x' y') (u : I) : a (p.val u) = q.val u := by
  subst x' y'
  exact congrArg (fun r : GeodesicSegment (a x) (a y) => r.val u)
    ((hX.uniquelyGeodesic.2 _ _).elim (p.mapIsometry a.isometry) q)

private theorem connector_isAxis (hX : CAT0 X) {a : X ≃ᵢ X} {L : ℝ}
    (hL : 0 < L) {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d)
    (hcd : AxesAligned c d) (p : ∀ t, GeodesicSegment (c t) (d t)) (u : I) :
    IsAxis a L (fun t => (p t).val u) ∧
      ∀ t, IsNearestPoint (range c) ((p t).val u) (c t) := by
  let D := dist (c 0) (d 0)
  have hdiag (t : ℝ) : dist (c t) (d t) = D := by
    rw [axis_dist_cross_zero hX hL hc hd, sub_self]
  have hp (t : ℝ) : IsNearestPoint (range c) ((p t).val u) (c t) := by
    refine ⟨mem_range_self _, fun q hq => ?_⟩
    have hnear := (hX.axis_nearestPoints hL hc hd hcd t).2.2 q hq
    have htri := dist_triangle (d t) ((p t).val u) q
    rw [dist_comm (d t) (c t), hdiag] at hnear
    rw [dist_comm (d t) ((p t).val u), (p t).dist_target, hdiag] at htri
    rw [dist_comm ((p t).val u) (c t), (p t).dist_source, hdiag]
    linarith only [hnear, htri]
  refine ⟨⟨Isometry.of_dist_eq (fun s t => ?_), fun t => ?_⟩, hp⟩
  · have hn : (range c).Nonempty := ⟨c 0, mem_range_self 0⟩
    let := line_complete hc.1
    have hv := line_convex hX hc.1
    have hprojection (t : ℝ) : nearestPoint (range c) ((p t).val u) = c t :=
      hX.isNearestPoint_unique hv (hX.isNearestPoint_nearestPoint hn hv _) (hp t)
    have hlo := (hX.lipschitzWith_nearestPoint hn hv).dist_le_mul ((p s).val u) ((p t).val u)
    rw [hprojection s, hprojection t, hc.1.dist_eq, NNReal.coe_one, one_mul] at hlo
    have hhi := hX.distAlongSegments (p s) (p t) u
    rw [hc.1.dist_eq, hd.1.dist_eq] at hhi
    exact (show dist ((p s).val u) ((p t).val u) ≤ dist s t by linarith only [hhi]).antisymm hlo
  · exact geodesic_map_apply_eq hX a (hc.2 t) (hd.2 t) (p t) (p (t + L)) u

/-- The interpolating segments of two aligned axes form a Euclidean strip. -/
theorem CAT0.aligned_axis_strip_dist_sq (hX : CAT0 X) {a : X ≃ᵢ X} {L : ℝ}
    (hL : 0 < L) {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d)
    (hcd : AxesAligned c d) (p : ∀ t, GeodesicSegment (c t) (d t))
    (s t : ℝ) (u v : I) :
    dist ((p s).val u) ((p t).val v) ^ 2 =
      ((u : ℝ) - (v : ℝ)) ^ 2 * dist (c 0) (d 0) ^ 2 + (s - t) ^ 2 := by
  let D := dist (c 0) (d 0)
  let F (w : I) (r : ℝ) := (p r).val w
  have hdiag (r : ℝ) : dist (c r) (d r) = D := by
    rw [axis_dist_cross_zero hX hL hc hd, sub_self]
  have hcross (r q : ℝ) : D ≤ dist (c r) (d q) := by
    rw [axis_dist_cross_zero hX hL hc hd]
    exact hcd.2 _ (mem_range_self _)
  have hleft (w : I) (r : ℝ) : dist (c r) (F w r) = (w : ℝ) * D :=
    ((p r).dist_source w).trans (by rw [hdiag])
  have hright (w : I) (r : ℝ) : dist (F w r) (d r) = (1 - (w : ℝ)) * D :=
    ((p r).dist_target w).trans (by rw [hdiag])
  have hwidth : dist (F u 0) (F v 0) = |(u : ℝ) - (v : ℝ)| * D := by
    exact ((p 0).prop u v).trans (by rw [Subtype.dist_eq, Real.dist_eq, hdiag])
  have halign : AxesAligned (F u) (F v) := by
    refine ⟨mem_range_self _, ?_⟩
    rintro _ ⟨r, rfl⟩
    rcases le_total (u : ℝ) (v : ℝ) with huv | hvu
    · have htriangle := dist_triangle4 (c 0) (F u 0) (F v r) (d r)
      rw [hleft, hright] at htriangle
      rw [hwidth, abs_of_nonpos (sub_nonpos.mpr huv)]
      linarith only [htriangle, hcross 0 r]
    · have htriangle := dist_triangle4 (c r) (F v r) (F u 0) (d 0)
      rw [hleft, hright, dist_comm (F v r) (F u 0)] at htriangle
      rw [hwidth, abs_of_nonneg (sub_nonneg.mpr hvu)]
      linarith only [htriangle, hcross r 0]
  have h := hX.aligned_axis_dist_sq hL (connector_isAxis hX hL hc hd hcd p u).1
    (connector_isAxis hX hL hc hd hcd p v).1 halign s t
  change dist (F u s) (F v t) ^ 2 = dist (F u 0) (F v 0) ^ 2 + (s - t) ^ 2 at h
  rw [hwidth, mul_pow, sq_abs] at h
  exact h

/-- The connecting strip, with its intrinsic width coordinate, embeds
isometrically even when the width is zero. -/
theorem CAT0.exists_axis_flat_strip (hX : CAT0 X) {a : X ≃ᵢ X} {L : ℝ}
    (hL : 0 < L) {c d : ℝ → X} (hc : IsAxis a L c) (hd : IsAxis a L d)
    (hcd : AxesAligned c d) :
    let D := dist (c 0) (d 0)
    ∃ F : EuclideanProduct ℝ (Set.Icc 0 D) → X,
      Isometry F ∧
      (∀ t : ℝ, F (WithLp.toLp 2 (t, ⟨0, le_rfl, dist_nonneg⟩)) = c t ∧
        F (WithLp.toLp 2 (t, ⟨D, dist_nonneg, le_rfl⟩)) = d t) ∧
      ∀ p, a (F p) = F (WithLp.toLp 2 (p.fst + L, p.snd)) := by
  intro D
  have hD₀ : 0 ≤ D := dist_nonneg
  rcases hD₀.eq_or_lt with hzero | hD
  · have he : c = d := axis_eq_of_same_origin hX hL hc hd (dist_eq_zero.mp hzero.symm)
    refine ⟨fun p => c p.fst, Isometry.of_dist_eq (fun p q => ?_),
      fun t => ⟨rfl, congrFun he t⟩, fun p => hc.2 p.fst⟩
    have hr (r : Set.Icc 0 D) : (r : ℝ) = 0 := r.2.1.antisymm' (r.2.2.trans hzero.ge)
    have hq : p.snd = q.snd := Subtype.ext ((hr p.snd).trans (hr q.snd).symm)
    rw [hc.1.dist_eq, euclideanProduct_dist, hq, dist_self, zero_pow (by decide : 2 ≠ 0),
      add_zero, Real.sqrt_sq dist_nonneg]
  · let p (t : ℝ) : GeodesicSegment (c t) (d t) := Classical.choice (hX.1.2 _ _)
    let u (r : Set.Icc 0 D) : I :=
      ⟨(r : ℝ) / D, div_nonneg r.2.1 hD.le, (div_le_one₀ hD).mpr r.2.2⟩
    let F (q : EuclideanProduct ℝ (Set.Icc 0 D)) : X := (p q.fst).val (u q.snd)
    refine ⟨F, Isometry.of_dist_eq (fun q r => ?_), fun t => ?_, fun q => ?_⟩
    · rw [euclideanProduct_dist]
      apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
      change dist ((p q.fst).val (u q.snd)) ((p r.fst).val (u r.snd)) ^ 2 = _
      rw [hX.aligned_axis_strip_dist_sq hL hc hd hcd, Real.sq_sqrt
        (add_nonneg (sq_nonneg _) (sq_nonneg _)), Subtype.dist_eq, Real.dist_eq, Real.dist_eq,
        sq_abs, sq_abs]
      change (((q.snd : ℝ) / D - (r.snd : ℝ) / D) ^ 2) * D ^ 2 + (q.fst - r.fst) ^ 2 =
        (q.fst - r.fst) ^ 2 + ((q.snd : ℝ) - (r.snd : ℝ)) ^ 2
      rw [← sub_div, ← mul_pow, div_mul_cancel₀ _ hD.ne', add_comm]
    · have h₀ : u ⟨0, le_rfl, hD₀⟩ = 0 := Subtype.ext (zero_div D)
      have h₁ : u ⟨D, hD₀, le_rfl⟩ = 1 := Subtype.ext (div_self hD.ne')
      change (p t).val (u ⟨0, le_rfl, hD₀⟩) = c t ∧ (p t).val (u ⟨D, hD₀, le_rfl⟩) = d t
      rw [h₀, h₁, Path.source, Path.target]
      exact ⟨rfl, rfl⟩
    · exact (connector_isAxis hX hL hc hd hcd p (u q.snd)).1.2 q.fst

private theorem axisCrossSection_convex (hX : CAT0 X) {a : X ≃ᵢ X}
    (hL : 0 < translationLength a) {c : ℝ → X} (hc : IsAxis a (translationLength a) c) :
    GeodesicConvex (axisCrossSection a c) := by
  intro x y hx hy p u
  obtain ⟨d, hd, hd0⟩ := hX.exists_axis hL hx.1
  obtain ⟨e, he, he0⟩ := hX.exists_axis hL hy.1
  subst x y
  have hB {d : ℝ → X} (hd : IsAxis a (translationLength a) d)
      (hzero : axisBusemann c (d 0) = 0) : axisBusemann c = axisBusemann d := by
    funext z
    rw [hX.axisBusemann_eq_add hL hc hd z, hzero, add_zero]
  have hBd := hB hd hx.2
  have hBe := hB he hy.2
  have halign := (hX.axesAligned_iff_axisBusemann_eq hL hd he).mpr (hBd.symm.trans hBe)
  let q (t : ℝ) : GeodesicSegment (d t) (e t) := Classical.choice (hX.1.2 _ _)
  have hpoint := congrArg (fun r : GeodesicSegment (d 0) (e 0) => r.val u)
    ((hX.uniquelyGeodesic.2 _ _).elim (q 0) p)
  have hq := connector_isAxis hX hL hd he halign q u
  have hBq := hX.axisBusemann_eq_of_aligned hL hq.1 hd (hq.2 0)
  refine ⟨hX.geodesicConvex_minset a hx.1 hy.1 p u, ?_⟩
  rw [← hpoint, hBd, ← hBq]
  exact (axisBusemann_self hq.1.1 0).trans neg_zero


private theorem commute_mem_minset_iff {a b : X ≃ᵢ X} (hab : Function.Commute a b)
    (x : X) : b x ∈ minset a ↔ x ∈ minset a := by
  change dist (b x) (a (b x)) = translationLength a ↔ dist x (a x) = translationLength a
  rw [hab x, b.dist_eq]

private theorem axis_product_dist_sq {a : X ≃ᵢ X} {Z : Type*} [MetricSpace Z]
    (e : EuclideanProduct Z ℝ ≃ᵢ minset a) (z w : Z) (s t : ℝ) :
    dist (e (WithLp.toLp 2 (z, s)) : X) (e (WithLp.toLp 2 (w, t)) : X) ^ 2 =
      dist z w ^ 2 + (s - t) ^ 2 := by
  rw [← Subtype.dist_eq, e.dist_eq, euclideanProduct_dist]
  simp [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), Real.dist_eq]

private theorem axis_product_centralizer (hX : CAT0 X) {a : X ≃ᵢ X} {Z : Type*}
    [MetricSpace Z] [Nonempty Z] (hL : 0 < translationLength a)
    (e : EuclideanProduct Z ℝ ≃ᵢ minset a)
    (haxis : ∀ z : Z, IsAxis a (translationLength a) (fun t => (e (WithLp.toLp 2 (z, t)) : X)))
    (b : X ≃ᵢ X) (hab : Function.Commute a b) :
    ∃ (f : Z ≃ᵢ Z) (τ : ℝ), ∀ p : EuclideanProduct Z ℝ,
      b (e p) = (e (WithLp.toLp 2 (f p.fst, p.snd + τ)) : X) := by
  let c (z : Z) (t : ℝ) : X := e (WithLp.toLp 2 (z, t))
  let q (z : Z) := e.symm ⟨b (c z 0), (commute_mem_minset_iff hab _).mpr (e _).2⟩
  let f (z : Z) := (q z).fst
  let shift (z : Z) := (q z).snd
  have hcoord (z : Z) (t : ℝ) : b (c z t) = c (f z) (t + shift z) := by
    have hzero : b (c z 0) = c (f z) (0 + shift z) := by
      rw [zero_add]
      change b (c z 0) = (e (q z) : X)
      exact (congrArg Subtype.val
        (e.apply_symm_apply ⟨b (c z 0), (commute_mem_minset_iff hab _).mpr (e _).2⟩)).symm
    exact congrFun (axis_eq_of_same_origin hX hL ((haxis z).map hab)
      ((haxis (f z)).shift (shift z)) hzero) t
  have hdist (z w : Z) (s t : ℝ) :
      dist z w ^ 2 + (s - t) ^ 2 =
        dist (f z) (f w) ^ 2 + (s + shift z - (t + shift w)) ^ 2 := by
    calc
      _ = dist (c z s) (c w t) ^ 2 := (axis_product_dist_sq e z w s t).symm
      _ = dist (b (c z s)) (b (c w t)) ^ 2 := by rw [b.dist_eq]
      _ = _ := by rw [hcoord, hcoord]; exact axis_product_dist_sq e _ _ _ _
  have heq (z w : Z) :
      dist z w ^ 2 = dist (f z) (f w) ^ 2 ∧ shift z = shift w := by
    have h₁ := hdist z w 0 0
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), add_zero, zero_add] at h₁
    have h₂ := hdist z w (shift w - shift z) 0
    rw [sub_zero, sub_add_cancel, zero_add, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero] at h₂
    have hshift : shift z = shift w := by nlinarith only [h₁, h₂, sq_nonneg (shift z - shift w)]
    exact ⟨by simpa [hshift] using h₁, hshift⟩
  have hf : Isometry f := Isometry.of_dist_eq fun z w =>
    (sq_eq_sq₀ dist_nonneg dist_nonneg).mp (heq z w).1.symm
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨x, hx⟩ := b.surjective (c w 0)
    have hxmem : x ∈ minset a := (commute_mem_minset_iff hab x).mp (hx ▸ (e _).2)
    let p := e.symm ⟨x, hxmem⟩
    have hp : c p.fst p.snd = x := by
      change (e p : X) = x
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hxmem⟩)
    have h := hcoord p.fst p.snd
    rw [hp, hx] at h
    have h' : WithLp.toLp 2 (w, (0 : ℝ)) =
        WithLp.toLp 2 (f p.fst, p.snd + shift p.fst) := e.injective (Subtype.ext h)
    exact ⟨p.fst, (congrArg WithLp.fst h').symm⟩
  let z₀ : Z := Classical.choice ‹Nonempty Z›
  refine ⟨⟨Equiv.ofBijective f ⟨hf.injective, hsurj⟩, hf⟩, shift z₀, fun p => ?_⟩
  have h := hcoord p.fst p.snd
  rw [(heq p.fst z₀).2] at h
  exact h

/-- A minimum set of positive length splits into a closed convex time-zero slice
and the translation line, with the Euclidean product distance. -/
theorem CAT0.axis_minset_splitting [CompleteSpace X] (hX : CAT0 X) (a : X ≃ᵢ X)
    (ha : IsSemisimple a) (hL : 0 < translationLength a) :
    ∃ c : ℝ → X, IsAxis a (translationLength a) c ∧
      IsClosed (axisCrossSection a c) ∧ GeodesicConvex (axisCrossSection a c) ∧
      CAT0 (axisCrossSection a c) ∧ CompleteSpace (axisCrossSection a c) ∧
      ∃ e : EuclideanProduct (axisCrossSection a c) ℝ ≃ᵢ minset a,
        (∀ z : axisCrossSection a c, (e (WithLp.toLp 2 (z, 0)) : X) = z) ∧
        (∀ p, axisBusemann c (e p) = -p.snd) ∧
        (∀ z : axisCrossSection a c,
          IsAxis a (translationLength a) (fun t => (e (WithLp.toLp 2 (z, t)) : X))) ∧
        (∀ p, a (e p) = (e (WithLp.toLp 2 (p.fst, p.snd + translationLength a)) : X)) ∧
        ∀ b : X ≃ᵢ X, Function.Commute a b →
          ∃ (f : axisCrossSection a c ≃ᵢ axisCrossSection a c) (τ : ℝ),
            ∀ p, b (e p) = (e (WithLp.toLp 2 (f p.fst, p.snd + τ)) : X) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨c, hc, _⟩ := hX.exists_axis hL hx
  let Z := axisCrossSection a c
  have hZn : Z.Nonempty := ⟨c 0, hc.mem_minset hL 0,
    (axisBusemann_self hc.1 0).trans neg_zero⟩
  have hZclosed : IsClosed Z :=
    (isClosed_minset a).inter (isClosed_eq (lipschitzWith_axisBusemann hc.1).continuous continuous_const)
  have hZconv : GeodesicConvex Z := axisCrossSection_convex hX hL hc
  obtain ⟨hZcat, hZcomplete⟩ := hX.closedConvexSubtype hZn hZclosed hZconv
  let : Nonempty Z := hZn.to_subtype
  let d (z : Z) := Classical.choose (hX.exists_axis hL z.2.1)
  have hd (z : Z) : IsAxis a (translationLength a) (d z) ∧ d z 0 = (z : X) :=
    Classical.choose_spec (hX.exists_axis hL z.2.1)
  have hBc (z : Z) : axisBusemann c = axisBusemann (d z) := by
    funext y
    calc
      _ = axisBusemann (d z) y + axisBusemann c (d z 0) :=
        hX.axisBusemann_eq_add hL hc (hd z).1 y
      _ = _ := by
        have hz : axisBusemann c (d z 0) = 0 := ((congrArg (axisBusemann c) (hd z).2).trans z.2.2)
        rw [hz, add_zero]
  let F (p : EuclideanProduct Z ℝ) : minset a :=
    ⟨d p.fst p.snd, (hd p.fst).1.mem_minset hL p.snd⟩
  have hF : Isometry F := Isometry.of_dist_eq fun p q => by
    rw [euclideanProduct_dist]
    apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
    change dist (d p.fst p.snd) (d q.fst q.snd) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), Real.dist_eq, sq_abs]
    have hAlign := (hX.axesAligned_iff_axisBusemann_eq hL (hd p.fst).1 (hd q.fst).1).mpr
      ((hBc p.fst).symm.trans (hBc q.fst))
    rw [hX.aligned_axis_dist_sq hL (hd p.fst).1 (hd q.fst).1 hAlign,
      (hd p.fst).2, (hd q.fst).2, Subtype.dist_eq]
  have hFs : Function.Surjective F := by
    intro y
    obtain ⟨γ, hγ, hγ0⟩ := hX.exists_axis hL y.2
    let r := axisBusemann c (y : X)
    have hzero : axisBusemann c (γ r) = 0 := by
      rw [hX.axisBusemann_eq_add hL hc hγ, axisBusemann_self hγ.1, hγ0]
      exact neg_add_cancel r
    let z : Z := ⟨γ r, hγ.mem_minset hL r, hzero⟩
    have hz : d z = fun t => γ (t + r) :=
      axis_eq_of_same_origin hX hL (hd z).1 (hγ.shift r) (by simpa [z] using (hd z).2)
    refine ⟨WithLp.toLp 2 (z, -r), Subtype.ext ?_⟩
    change d z (-r) = _
    simpa only [hz, neg_add_cancel] using hγ0
  let e : EuclideanProduct Z ℝ ≃ᵢ minset a :=
    ⟨Equiv.ofBijective F ⟨hF.injective, hFs⟩, hF⟩
  refine ⟨c, hc, hZclosed, hZconv, hZcat, hZcomplete, e, fun z => (hd z).2,
    fun p => ?_, fun z => (hd z).1, fun p => (hd p.fst).1.2 p.snd,
    fun b hab => axis_product_centralizer hX hL e (fun z => (hd z).1) b hab⟩
  change axisBusemann c (d p.fst p.snd) = -p.snd
  rw [hBc p.fst, axisBusemann_self (hd p.fst).1.1]

end LinearAlgebraicGroups.Geometry
