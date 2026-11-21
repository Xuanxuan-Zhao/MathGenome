import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.HomotopicAttachments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set Topology
universe u v w z

namespace P202.Attachments

section Adjunction
variable {X : Type u} [TopologicalSpace X] {J : Type v}
  {A B : J → Type w} [∀ j, TopologicalSpace (A j)] [∀ j, TopologicalSpace (B j)]
  (i : ∀ j, C(A j, B j)) (a : ∀ j, C(A j, X))

@[simp] theorem cell_boundary (j : J) (x : A j) :
    cell i a j (i j x) = base i a (a j x) :=
  (Quot.sound (Relation.boundary j x)).symm

/-- The universal map out of the adjunction, with its quotient topology. -/
def descend {Y : Type z} [TopologicalSpace Y] (f : C(X, Y)) (g : ∀ j, C(B j, Y))
    (h : ∀ j x, f (a j x) = g j (i j x)) : C(Adjunction i a, Y) where
  toFun := Quot.lift (Sum.elim f (fun p => g p.1 p.2)) (by
    intro x y r
    cases r with
    | boundary j x => exact h j x)
  continuous_toFun := continuous_quot_lift _
    (continuous_sum_dom.mpr ⟨f.continuous, continuous_sigma (fun j => (g j).continuous)⟩)

@[simp] theorem descend_base {Y : Type z} [TopologicalSpace Y]
    (f : C(X, Y)) (g : ∀ j, C(B j, Y)) (h) (x : X) :
    descend i a f g h (base i a x) = f x := rfl

@[simp] theorem descend_cell {Y : Type z} [TopologicalSpace Y]
    (f : C(X, Y)) (g : ∀ j, C(B j, Y)) (h) (j : J) (x : B j) :
    descend i a f g h (cell i a j x) = g j x := rfl

@[ext] theorem hom_ext {Y : Type z} [TopologicalSpace Y] {f g : C(Adjunction i a, Y)}
    (hb : ∀ x, f (base i a x) = g (base i a x))
    (hc : ∀ j x, f (cell i a j x) = g (cell i a j x)) : f = g := by
  ext p
  refine Quot.inductionOn p ?_
  intro p
  cases p with
  | inl x => exact hb x
  | inr p => exact hc p.1 p.2

end Adjunction
end P202.Attachments

namespace P202.Attachments
open P202.Cellular

/-- The disk cylinder, with the ordinary product topology. -/
abbrev Cylinder (n : ℕ) := Interval × Disk n

/-- Its bottom together with its side. -/
abbrev BottomSide (n : ℕ) := {p : Cylinder n // p.1 = 0 ∨ ‖p.2.1‖ = 1}

private def rayScale (n : ℕ) (p : Cylinder n) : ℝ :=
  2 / max (2 - (p.1 : ℝ)) (2 * ‖p.2.1‖)

private theorem rayScale_bounds (n : ℕ) (p : Cylinder n) :
    1 ≤ rayScale n p ∧ rayScale n p * (2 - (p.1 : ℝ)) ≤ 2 ∧
      rayScale n p * ‖p.2.1‖ ≤ 1 := by
  rcases p.1.2 with ⟨ht0, ht1⟩
  have hx : ‖p.2.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using p.2.2
  have hd : 0 < max (2 - (p.1 : ℝ)) (2 * ‖p.2.1‖) :=
    lt_of_lt_of_le (by linarith : 0 < 2 - (p.1 : ℝ)) (le_max_left _ _)
  have hd₂ : max (2 - (p.1 : ℝ)) (2 * ‖p.2.1‖) ≤ 2 :=
    max_le (by linarith) (by linarith)
  unfold rayScale
  refine ⟨(le_div_iff₀ hd).2 (by simpa using hd₂), ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith [le_max_left (2 - (p.1 : ℝ)) (2 * ‖p.2.1‖)]
  · rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    simpa using le_max_right (2 - (p.1 : ℝ)) (2 * ‖p.2.1‖)

private theorem continuous_rayScale (n : ℕ) : Continuous (rayScale n) := by
  apply Continuous.div continuous_const
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).max
      (continuous_const.mul (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))))
  intro p
  have ht := p.1.2.2
  exact ne_of_gt (lt_of_lt_of_le (by linarith : 0 < 2 - (p.1 : ℝ)) (le_max_left _ _))

/-- Follow the ray from `(2,0)` towards the bottom or side. At parameter one
this is the standard cylinder retraction. It fixes the bottom and side at
all intermediate parameters, so it descends through arbitrary attaching maps. -/
def cylinderSqueeze (n : ℕ) : C(Interval × Cylinder n, Cylinder n) where
  toFun q := by
    let k := 1 + (q.1 : ℝ) * (rayScale n q.2 - 1)
    have hk : 1 ≤ k ∧ k ≤ rayScale n q.2 := by
      have h := (rayScale_bounds n q.2).1
      rcases q.1.2 with ⟨hs0, hs1⟩
      constructor <;> dsimp [k] <;> nlinarith
    rcases q.2.1.2 with ⟨ht0, ht1⟩
    have hb := rayScale_bounds n q.2
    have hx := norm_nonneg q.2.2.1
    exact (⟨2 - k * (2 - (q.2.1 : ℝ)), by constructor <;> nlinarith⟩,
      ⟨k • q.2.2.1, by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : 0 ≤ k)]
        nlinarith⟩)
  continuous_toFun := by
    have hk : Continuous (fun q : Interval × Cylinder n =>
        1 + (q.1 : ℝ) * (rayScale n q.2 - 1)) :=
      continuous_const.add ((continuous_subtype_val.comp continuous_fst).mul
        (((continuous_rayScale n).comp continuous_snd).sub continuous_const))
    exact ((continuous_const.sub (hk.mul
      (continuous_const.sub (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))))).subtype_mk _).prodMk ((hk.smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))).subtype_mk _)

@[simp] theorem cylinderSqueeze_zero (n : ℕ) (p : Cylinder n) :
    cylinderSqueeze n (0, p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    simp [cylinderSqueeze]
  · apply Subtype.ext
    simp [cylinderSqueeze]

private theorem rayScale_eq_one (n : ℕ) (p : Cylinder n)
    (hp : p.1 = 0 ∨ ‖p.2.1‖ = 1) : rayScale n p = 1 := by
  have hx : ‖p.2.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using p.2.2
  rcases p.1.2 with ⟨ht0, ht1⟩
  rcases hp with hp | hp
  · simp [rayScale, hp, max_eq_left (by linarith : 2 * ‖p.2.1‖ ≤ 2)]
  · simp [rayScale, hp, max_eq_right (by linarith : 2 - (p.1 : ℝ) ≤ 2)]

theorem cylinderSqueeze_fixed (n : ℕ) (s : Interval) (p : Cylinder n)
    (hp : p.1 = 0 ∨ ‖p.2.1‖ = 1) : cylinderSqueeze n (s, p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    simp [cylinderSqueeze, rayScale_eq_one n p hp]
  · apply Subtype.ext
    simp [cylinderSqueeze, rayScale_eq_one n p hp]

/-- The endpoint lies in the bottom or the side, including for `n = 0`. -/
theorem cylinderSqueeze_lands (n : ℕ) (p : Cylinder n) :
    (cylinderSqueeze n (1, p)).1 = 0 ∨ ‖(cylinderSqueeze n (1, p)).2.1‖ = 1 := by
  rcases p.1.2 with ⟨ht0, ht1⟩
  have hr := (rayScale_bounds n p).1
  have hd : 0 < max (2 - (p.1 : ℝ)) (2 * ‖p.2.1‖) :=
    lt_of_lt_of_le (by linarith : 0 < 2 - (p.1 : ℝ)) (le_max_left _ _)
  by_cases h : 2 * ‖p.2.1‖ ≤ 2 - (p.1 : ℝ)
  · left
    apply Subtype.ext
    change 2 - (1 + (1 : ℝ) * (rayScale n p - 1)) * (2 - (p.1 : ℝ)) = 0
    have hne : 2 - (p.1 : ℝ) ≠ 0 := by linarith
    simp only [rayScale, max_eq_left h, one_mul, add_sub_cancel]
    field_simp
    ring
  · right
    have hx : ‖p.2.1‖ ≠ 0 := by
      have := lt_of_not_ge h
      linarith
    change ‖(1 + (1 : ℝ) * (rayScale n p - 1)) • p.2.1‖ = 1
    simp only [one_mul, add_sub_cancel, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ rayScale n p)]
    rw [rayScale, max_eq_right (le_of_lt (lt_of_not_ge h))]
    field_simp

/-- The endpoint retraction, bundled with its actual subspace target. -/
def cylinderRetract (n : ℕ) : C(Cylinder n, BottomSide n) where
  toFun p := ⟨cylinderSqueeze n (1, p), cylinderSqueeze_lands n p⟩
  continuous_toFun := ((cylinderSqueeze n).continuous.comp
    (continuous_const.prodMk continuous_id)).subtype_mk _

end P202.Attachments

namespace P202.Attachments

section ClosedPasting
variable {T : Type*} {Y : Type*} [TopologicalSpace T] [TopologicalSpace Y]
  (S U : Set T) (cover : S ∪ U = univ)
  (f : C(S, Y)) (g : C(U, Y))
  (agree : ∀ x (hs : x ∈ S) (hu : x ∈ U), f ⟨x, hs⟩ = g ⟨x, hu⟩)

private def closedPasteFun (x : T) : Y := by
  classical
  exact if hs : x ∈ S then f ⟨x, hs⟩ else
    g ⟨x, (show x ∈ S ∪ U by rw [cover]; trivial).resolve_left hs⟩

private theorem closedPasteFun_left (x : T) (hx : x ∈ S) :
    closedPasteFun S U cover f g x = f ⟨x, hx⟩ := by
  simp [closedPasteFun, hx]

include agree in
private theorem closedPasteFun_right (x : T) (hx : x ∈ U) :
    closedPasteFun S U cover f g x = g ⟨x, hx⟩ := by
  classical
  by_cases hs : x ∈ S
  · simp [closedPasteFun, hs, agree x hs hx]
  · simp [closedPasteFun, hs]

/-- Pasting maps defined on two closed subspaces covering the domain. -/
def closedPaste (hS : IsClosed S) (hU : IsClosed U) : C(T, Y) where
  toFun := closedPasteFun S U cover f g
  continuous_toFun := by
    have hf : ContinuousOn (closedPasteFun S U cover f g) S := by
      rw [continuousOn_iff_continuous_domRestrict]
      convert f.continuous using 1
      ext x
      exact closedPasteFun_left S U cover f g x x.2
    have hg : ContinuousOn (closedPasteFun S U cover f g) U := by
      rw [continuousOn_iff_continuous_domRestrict]
      convert g.continuous using 1
      ext x
      exact closedPasteFun_right S U cover f g agree x x.2
    rw [← continuousOn_univ, ← cover]
    exact hf.union_of_isClosed hg hS hU

@[simp] theorem closedPaste_left (hS : IsClosed S) (hU : IsClosed U) (x : T) (hx : x ∈ S) :
    closedPaste S U cover f g agree hS hU x = f ⟨x, hx⟩ :=
  closedPasteFun_left S U cover f g x hx

@[simp] theorem closedPaste_right (hS : IsClosed S) (hU : IsClosed U) (x : T) (hx : x ∈ U) :
    closedPaste S U cover f g agree hS hU x = g ⟨x, hx⟩ :=
  closedPasteFun_right S U cover f g agree x hx

end ClosedPasting

section ParametrizedAdjunction
variable {X : Type u} [TopologicalSpace X] {J : Type v}
  {A B : J → Type w} [∀ j, TopologicalSpace (A j)] [∀ j, TopologicalSpace (B j)]
  (i : ∀ j, C(A j, B j)) (a : ∀ j, C(A j, X))
  {Y : Type z} [TopologicalSpace Y]

/-- Pasting a continuous family through an adjunction in the ordinary product
with the compact interval. Currying uses the compact-open exponential law. -/
def descendFamily (f : C(unitInterval × X, Y)) (g : ∀ j, C(unitInterval × B j, Y))
    (h : ∀ t j x, f (t, a j x) = g j (t, i j x)) :
    C(unitInterval × Adjunction i a, Y) :=
  ((descend i a (f.comp ContinuousMap.prodSwap).curry
    (fun j => ((g j).comp ContinuousMap.prodSwap).curry) (by
      intro j x
      ext t
      exact h t j x)).uncurry).comp ContinuousMap.prodSwap

@[simp] theorem descendFamily_base (f : C(unitInterval × X, Y))
    (g : ∀ j, C(unitInterval × B j, Y)) (h) (t : unitInterval) (x : X) :
    descendFamily i a f g h (t, base i a x) = f (t, x) := rfl

@[simp] theorem descendFamily_cell (f : C(unitInterval × X, Y))
    (g : ∀ j, C(unitInterval × B j, Y)) (h) (t : unitInterval) (j : J) (x : B j) :
    descendFamily i a f g h (t, cell i a j x) = g j (t, x) := rfl

end ParametrizedAdjunction

open P202.Cellular

/-- The collapse data needed for the common-cylinder proof. This structure
is constructed below for each endpoint; it is never a theorem hypothesis. -/
structure CylinderCollapse (n : ℕ) (e : Interval) where
  motion : C(Interval × Cylinder n, Cylinder n)
  start : ∀ p, motion (0, p) = p
  lands : ∀ p, (motion (1, p)).1 = e ∨ ‖(motion (1, p)).2.1‖ = 1
  fixed : ∀ s p, p.1 = e ∨ ‖p.2.1‖ = 1 → motion (s, p) = p

/-- Retraction to the bottom together with the side. -/
def collapseZero (n : ℕ) : CylinderCollapse n 0 where
  motion := cylinderSqueeze n
  start := cylinderSqueeze_zero n
  lands := cylinderSqueeze_lands n
  fixed := cylinderSqueeze_fixed n

/-- Reverse the cylinder time coordinate, leaving the disk unchanged. -/
def flipCylinder (n : ℕ) : C(Cylinder n, Cylinder n) :=
  ⟨fun p => (unitInterval.symm p.1, p.2),
    (unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd⟩

@[simp] theorem flipCylinder_flip (n : ℕ) (p : Cylinder n) :
    flipCylinder n (flipCylinder n p) = p := by
  simp [flipCylinder]

/-- The same ray retraction applied from the other end. -/
def collapseOne (n : ℕ) : CylinderCollapse n 1 where
  motion := (flipCylinder n).comp ((cylinderSqueeze n).comp
    (ContinuousMap.fst.prodMk ((flipCylinder n).comp ContinuousMap.snd)))
  start p := by simp
  lands p := by
    rcases cylinderSqueeze_lands n (flipCylinder n p) with h | h
    · left
      change unitInterval.symm ((cylinderSqueeze n) (1, flipCylinder n p)).1 = 1
      rw [h, unitInterval.symm_zero]
    · exact Or.inr h
  fixed s p hp := by
    have hf : (flipCylinder n p).1 = 0 ∨ ‖(flipCylinder n p).2.1‖ = 1 := by
      rcases hp with hp | hp
      · left
        change unitInterval.symm p.1 = 0
        rw [hp, unitInterval.symm_one]
      · exact Or.inr hp
    change flipCylinder n (cylinderSqueeze n (s, flipCylinder n p)) = p
    rw [cylinderSqueeze_fixed n s _ hf, flipCylinder_flip]

end P202.Attachments

namespace P202.Attachments
open P202.Cellular

abbrev EndSide (n : ℕ) (e : Interval) :=
  {p : Cylinder n // p.1 = e ∨ ‖p.2.1‖ = 1}

private def bottomPiece (n : ℕ) (e : Interval) :=
  {p : EndSide n e | p.1.1 = e}

private def sidePiece (n : ℕ) (e : Interval) :=
  {p : EndSide n e | ‖p.1.2.1‖ = 1}

private def bottomCoordinate (n : ℕ) (e : Interval) :
    C(bottomPiece n e, Disk n) := ⟨fun p => p.1.1.2, by fun_prop⟩

private def sideCoordinate (n : ℕ) (e : Interval) :
    C(sidePiece n e, Interval × Sphere n) where
  toFun p := (p.1.1.1, ⟨p.1.1.2.1, by
    simpa only [sidePiece, mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using p.2⟩)
  continuous_toFun := (by fun_prop : Continuous (fun p : sidePiece n e => p.1.1.1)).prodMk
    ((by fun_prop : Continuous (fun p : sidePiece n e => p.1.1.2.1)).subtype_mk _)

/-- Pasting prescribed values on the end disk and the side of a cylinder,
using their actual closed-subspace topologies. -/
def boundaryPasting {Y : Type*} [TopologicalSpace Y] (n : ℕ) (e : Interval)
    (d : C(Disk n, Y)) (b : C(Interval × Sphere n, Y))
    (h : ∀ z, d (boundaryInclusion n z) = b (e, z)) : C(EndSide n e, Y) :=
  closedPaste (bottomPiece n e) (sidePiece n e) (by
    ext p
    simp only [mem_union, mem_univ, iff_true]
    exact p.2)
    (d.comp (bottomCoordinate n e)) (b.comp (sideCoordinate n e)) (by
      intro p hs hu
      let z : Sphere n := ⟨p.1.2.1, by
        simpa only [sidePiece, mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using hu⟩
      change d p.1.2 = b (p.1.1, z)
      rw [hs]
      exact h z)
    (isClosed_eq (by fun_prop) continuous_const)
    (isClosed_eq (by fun_prop) continuous_const)

@[simp] theorem boundaryPasting_bottom {Y : Type*} [TopologicalSpace Y]
    (n : ℕ) (e : Interval) (d : C(Disk n, Y)) (b : C(Interval × Sphere n, Y))
    (h) (x : Disk n) :
    boundaryPasting n e d b h ⟨(e, x), Or.inl rfl⟩ = d x := by
  apply closedPaste_left
  rfl

@[simp] theorem boundaryPasting_side {Y : Type*} [TopologicalSpace Y]
    (n : ℕ) (e : Interval) (d : C(Disk n, Y)) (b : C(Interval × Sphere n, Y))
    (h) (t : Interval) (z : Sphere n) :
    boundaryPasting n e d b h
      ⟨(t, boundaryInclusion n z), Or.inr (by
        simpa only [boundaryInclusion, Metric.mem_sphere, dist_zero_right] using z.2)⟩ = b (t, z) := by
  apply closedPaste_right
  change ‖z.1‖ = 1
  simpa only [Metric.mem_sphere, dist_zero_right] using z.2

/-- The side inclusion into a disk cylinder. -/
def cylinderBoundary (n : ℕ) : C(Interval × Sphere n, Cylinder n) :=
  ContinuousMap.id Interval |>.prodMap (diskBoundary n)

/-- The end-disk inclusion into a disk cylinder. -/
def cylinderEnd (n : ℕ) (e : Interval) : C(Disk n, Cylinder n) :=
  (ContinuousMap.const _ e).prodMk (ContinuousMap.id _)

section CommonAttachment
variable {X : Type u} [TopologicalSpace X] {J : Type v} (n : J → ℕ)
  (h : ∀ j, C(Interval × Sphere (n j), X))

/-- Attach whole disk cylinders by the specified family on their sides. -/
abbrev Track := Adjunction (fun j => cylinderBoundary (n j)) h

abbrev trackBase : C(X, Track n h) := base (fun j => cylinderBoundary (n j)) h
abbrev trackCell (j : J) : C(Cylinder (n j), Track n h) :=
  cell (fun j => cylinderBoundary (n j)) h j

variable (e : Interval) (a : ∀ j, C(Sphere (n j), X))
  (ha : ∀ j z, h j (e, z) = a j z)

/-- Map from the end attachment into the common cylinder attachment. -/
def endInclusion : C(Attached n a, Track n h) :=
  descend (fun j => diskBoundary (n j)) a (trackBase n h)
    (fun j => (trackCell n h j).comp (cylinderEnd (n j) e)) (by
      intro j z
      change trackBase n h (a j z) = trackCell n h j (cylinderBoundary (n j) (e, z))
      rw [cell_boundary, ha])

@[simp] theorem endInclusion_base (x : X) :
    endInclusion n h e a ha (inclusion n a x) = trackBase n h x := rfl

@[simp] theorem endInclusion_cell (j : J) (x : Disk (n j)) :
    endInclusion n h e a ha (cell (fun j => diskBoundary (n j)) a j x) =
      trackCell n h j (e, x) := rfl

/-- Read the bottom-or-side boundary in the end attachment. -/
def endBoundaryValue (j : J) : C(EndSide (n j) e, Attached n a) :=
  boundaryPasting (n j) e (cell (fun j => diskBoundary (n j)) a j)
    ((inclusion n a).comp (h j)) (by
      intro z
      change cell (fun j => diskBoundary (n j)) a j (diskBoundary (n j) z) =
        inclusion n a (h j (e, z))
      rw [cell_boundary, ha])

@[simp] theorem endBoundaryValue_bottom (j : J) (x : Disk (n j)) :
    endBoundaryValue n h e a ha j ⟨(e, x), Or.inl rfl⟩ =
      cell (fun j => diskBoundary (n j)) a j x := by
  apply boundaryPasting_bottom

@[simp] theorem endBoundaryValue_side (j : J) (t : Interval) (z : Sphere (n j)) :
    endBoundaryValue n h e a ha j
      ⟨(t, boundaryInclusion (n j) z), Or.inr (by
        simpa only [boundaryInclusion, Metric.mem_sphere, dist_zero_right] using z.2)⟩ =
      inclusion n a (h j (t, z)) := by
  apply boundaryPasting_side

/-- The boundary-value map is the identity after inclusion into the common space. -/
theorem endBoundaryValue_inclusion (j : J) (p : EndSide (n j) e) :
    endInclusion n h e a ha (endBoundaryValue n h e a ha j p) = trackCell n h j p.1 := by
  rcases p with ⟨⟨t, x⟩, hp⟩
  rcases hp with hp | hp
  · change t = e at hp
    subst t
    simp
  · let z : Sphere (n j) := ⟨x.1, by
      simpa only [Metric.mem_sphere, dist_zero_right] using hp⟩
    change endInclusion n h e a ha
      (endBoundaryValue n h e a ha j
        ⟨(t, boundaryInclusion (n j) z), Or.inr hp⟩) = _
    rw [endBoundaryValue_side, endInclusion_base]
    exact (cell_boundary (fun j => cylinderBoundary (n j)) h j (t, z)).symm

variable (R : ∀ j, CylinderCollapse (n j) e)

/-- Retraction from the common space onto an end attachment. -/
def endRetraction : C(Track n h, Attached n a) :=
  descend (fun j => cylinderBoundary (n j)) h (inclusion n a)
    (fun j => (endBoundaryValue n h e a ha j).comp
      ⟨fun p => ⟨(R j).motion (1, p), (R j).lands p⟩,
        (((R j).motion.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _⟩)
    (by
      intro j p
      change inclusion n a (h j p) = endBoundaryValue n h e a ha j
        ⟨(R j).motion (1, cylinderBoundary (n j) p), (R j).lands _⟩
      have hp : ‖(cylinderBoundary (n j) p).2.1‖ = 1 := by
        change ‖p.2.1‖ = 1
        simpa only [Metric.mem_sphere, dist_zero_right] using p.2.2
      have hr := (R j).fixed 1 (cylinderBoundary (n j) p) (Or.inr hp)
      simp only [hr]
      exact (endBoundaryValue_side n h e a ha j p.1 p.2).symm)

@[simp] theorem endRetraction_base (x : X) :
    endRetraction n h e a ha R (trackBase n h x) = inclusion n a x := rfl

@[simp] theorem endRetraction_cell (j : J) (p : Cylinder (n j)) :
    endRetraction n h e a ha R (trackCell n h j p) =
      endBoundaryValue n h e a ha j ⟨(R j).motion (1, p), (R j).lands p⟩ := rfl

/-- The retraction is the identity on its end attachment. -/
theorem endRetraction_inclusion :
    (endRetraction n h e a ha R).comp (endInclusion n h e a ha) = ContinuousMap.id _ := by
  apply hom_ext (fun j => diskBoundary (n j)) a
  · intro x
    simp
  · intro j x
    simp only [ContinuousMap.comp_apply, endInclusion_cell, endRetraction_cell]
    have hr := (R j).fixed 1 (e, x) (Or.inl rfl)
    simp only [hr, endBoundaryValue_bottom, ContinuousMap.id_apply]

/-- Deform the common space to this end, stationary on the original `X`. -/
def trackDeformation :
    (ContinuousMap.id (Track n h)).HomotopyRel
      ((endInclusion n h e a ha).comp (endRetraction n h e a ha R)) (range (trackBase n h)) where
  toContinuousMap := descendFamily (fun j => cylinderBoundary (n j)) h
    ((trackBase n h).comp ContinuousMap.snd)
    (fun j => (trackCell n h j).comp (R j).motion) (by
      intro s j p
      change trackBase n h (h j p) = trackCell n h j ((R j).motion (s, cylinderBoundary (n j) p))
      have hp : ‖(cylinderBoundary (n j) p).2.1‖ = 1 := by
        change ‖p.2.1‖ = 1
        simpa only [Metric.mem_sphere, dist_zero_right] using p.2.2
      rw [(R j).fixed s _ (Or.inr hp), cell_boundary])
  map_zero_left := by
    intro p
    refine Quot.inductionOn p ?_
    intro p
    cases p with
    | inl x => rfl
    | inr p =>
      change trackCell n h p.1 ((R p.1).motion (0, p.2)) = trackCell n h p.1 p.2
      rw [(R p.1).start]
  map_one_left := by
    intro p
    refine Quot.inductionOn p ?_
    intro p
    cases p with
    | inl x => rfl
    | inr p =>
      change trackCell n h p.1 ((R p.1).motion (1, p.2)) =
        endInclusion n h e a ha (endBoundaryValue n h e a ha p.1 _)
      exact (endBoundaryValue_inclusion n h e a ha p.1
        ⟨(R p.1).motion (1, p.2), (R p.1).lands p.2⟩).symm
  prop' := by
    intro s p hp
    rcases hp with ⟨x, rfl⟩
    rfl

/-- Each end attachment is homotopy equivalent under `X` to the common space. -/
def endEquivalence : RelativeEquivalence (inclusion n a) (trackBase n h) where
  forward := endInclusion n h e a ha
  backward := endRetraction n h e a ha R
  forward_base := endInclusion_base n h e a ha
  backward_base := endRetraction_base n h e a ha R
  left := (ContinuousMap.HomotopyRel.refl (ContinuousMap.id _) _).cast
    (endRetraction_inclusion n h e a ha R).symm rfl
  right := (trackDeformation n h e a ha R).symm

end CommonAttachment
end P202.Attachments

namespace P202.Attachments

section RelativeComposition
variable {X : Type*} {Y : Type*} {Z : Type*} {W : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
  {i : C(X, Y)} {j : C(X, Z)} {k : C(X, W)}

/-- Reverse an equivalence under the original space. -/
def RelativeEquivalence.symm (E : RelativeEquivalence i j) : RelativeEquivalence j i where
  forward := E.backward
  backward := E.forward
  forward_base := E.backward_base
  backward_base := E.forward_base
  left := E.right
  right := E.left

/-- Pre- and postcompose a relative homotopy; the precomposition maps the
specified base into the set on which the original homotopy is stationary. -/
def sandwichHomotopy {f g : C(Z, Z)} (H : f.HomotopyRel g (range j))
    (a : C(Y, Z)) (b : C(Z, Y)) (ha : ∀ x, a (i x) = j x) :
    (b.comp (f.comp a)).HomotopyRel (b.comp (g.comp a)) (range i) where
  toHomotopy := (ContinuousMap.Homotopy.refl b).comp (H.toHomotopy.compContinuousMap a)
  prop' := by
    intro t y hy
    rcases hy with ⟨x, rfl⟩
    change b (H (t, a (i x))) = b (f (a (i x)))
    rw [ha]
    exact congrArg b (H.eq_fst t (mem_range_self x))

/-- Compose equivalences whose maps and inverse homotopies all fix the base. -/
def RelativeEquivalence.trans (E : RelativeEquivalence i j) (F : RelativeEquivalence j k) :
    RelativeEquivalence i k where
  forward := F.forward.comp E.forward
  backward := E.backward.comp F.backward
  forward_base x := by simp [E.forward_base, F.forward_base]
  backward_base x := by simp [E.backward_base, F.backward_base]
  left := ((sandwichHomotopy F.left E.forward E.backward E.forward_base).cast
    (by ext; rfl) (by ext; rfl)).trans E.left
  right := ((sandwichHomotopy E.right F.backward F.forward F.backward_base).cast
    (by ext; rfl) (by ext; rfl)).trans F.right

end RelativeComposition

open P202.Cellular

/-- The common-cylinder proof works for any topological base space and any
family of disks. No CW or embedding property is used by the construction. -/
def homotopicAttachmentEquivalence {X : Type u} [TopologicalSpace X] {J : Type v}
    (n : J → ℕ) (a₀ a₁ : ∀ j, C(Sphere (n j), X))
    (H : ∀ j, (a₀ j).Homotopy (a₁ j)) :
    RelativeEquivalence (inclusion n a₀) (inclusion n a₁) :=
  (endEquivalence n (fun j => (H j).toContinuousMap) 0 a₀
    (fun j z => (H j).map_zero_left z) (fun j => collapseZero (n j))).trans
  (endEquivalence n (fun j => (H j).toContinuousMap) 1 a₁
    (fun j z => (H j).map_one_left z) (fun j => collapseOne (n j))).symm

end P202.Attachments

namespace P202.Topology

/-- Homotopic disk attachments are homotopy equivalent relative to the original
space, for arbitrary families and including zero-dimensional disks. -/
theorem homotopicAttachments    : P202Specs.Topology.HomotopicAttachments.homotopicAttachments.{u,v} := by
  intro X _ _ J n a₀ a₁ H
  exact ⟨P202.Attachments.homotopicAttachmentEquivalence n a₀ a₁ H⟩

end P202.Topology
