import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneTurningData
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Module.Ray
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Finset.Sort
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionCornerCollar
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Tangent data for paper.tex, lem:p202-plane-turning.
Construct finite smooth presentations and filled unit-tangent circuits of the
original curve. Establish angle lifts, corner bounds, reversal, the winding
formula, and arbitrarily fine partitions for the polygonal reduction.
-/
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped BigOperators unitInterval ContDiff

namespace P202.PlaneTurning
open P202Specs.PlaneTurning
open P202Specs.PlanarRegionTopology (Plane RegularJordanCurve)

/-- A point of a finite real interval lies in one of its unit subintervals. -/
lemma exists_unit_slot (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) n) :
    ∃ j : Fin n, (j : ℝ) ≤ x ∧ x ≤ (j : ℝ) + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, by simpa using hx⟩
    · by_cases hxn : x ≤ n
      · obtain ⟨j, hj⟩ := ih (by omega) ⟨hx.1, hxn⟩
        exact ⟨j.castSucc, by simpa using hj⟩
      · exact ⟨Fin.last n, by simpa using (show (n : ℝ) ≤ x ∧ x ≤ n + 1 from
          ⟨le_of_lt (lt_of_not_ge hxn), by simpa using hx.2⟩)⟩

lemma uniformSlot_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun z : (j : Fin n) × unitInterval => uniformSlot n hn z.1 z.2) := by
  intro t
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨j, hj0, hj1⟩ := exists_unit_slot n hn (n * (t : ℝ))
    ⟨mul_nonneg hn'.le t.property.1, by nlinarith [t.property.2]⟩
  refine ⟨⟨j, ⟨n * (t : ℝ) - j, by constructor <;> linarith⟩⟩, ?_⟩
  apply Subtype.ext
  dsimp [uniformSlot]
  field_simp
  ring

/-- Finite gluing on equal slots, proved by descent along the compact quotient
of the disjoint union of closed unit intervals. -/
lemma glue_uniform_slots {E : Type*} [TopologicalSpace E] [Nonempty E]
    (n : ℕ) (hn : 0 < n) (f : Fin n → C(unitInterval, E))
    (hjoin : ∀ j k : Fin n, j.val + 1 = k.val → f j 1 = f k 0) :
    ∃ M : C(unitInterval, E), ∀ j t, M (uniformSlot n hn j t) = f j t := by
  let q : ((j : Fin n) × unitInterval) → unitInterval :=
    fun z => uniformSlot n hn z.1 z.2
  let g : ((j : Fin n) × unitInterval) → E := fun z => f z.1 z.2
  have hq : Continuous q := by
    apply continuous_sigma
    intro j
    apply Continuous.subtype_mk
    change Continuous (fun t : unitInterval => ((j : ℝ) + t) / n)
    fun_prop
  have hg : Continuous g := continuous_sigma (fun j => (f j).continuous)
  have hquot := hq.isClosedMap.isQuotientMap hq (uniformSlot_surjective n hn)
  have hfactor : g.FactorsThrough q := by
    rintro ⟨j, t⟩ ⟨k, s⟩ h
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have he : (j : ℝ) + t = (k : ℝ) + s := by
      have he := congrArg (fun z : unitInterval => (z : ℝ)) h
      exact (div_left_inj' hn').mp he
    rcases lt_trichotomy j.val k.val with hjk | hjk | hjk
    · have hle : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
      have ht : t = 1 := Subtype.ext (by change (t : ℝ) = 1; linarith [s.property.1, t.property.2])
      have hs : s = 0 := Subtype.ext (by change (s : ℝ) = 0; linarith [s.property.1, t.property.2])
      have hk : j.val + 1 = k.val := by
        have he' : (j : ℝ) + 1 = k := by linarith [s.property.1, t.property.2]
        exact_mod_cast he'
      exact ht ▸ hs ▸ hjoin j k hk
    · have hj : j = k := Fin.ext hjk
      subst k
      have ht : t = s := Subtype.ext (by linarith)
      exact congrArg (f j) ht
    · have hle : (k : ℝ) + 1 ≤ j := by exact_mod_cast hjk
      have ht : t = 0 := Subtype.ext (by change (t : ℝ) = 0; linarith [t.property.1, s.property.2])
      have hs : s = 1 := Subtype.ext (by change (s : ℝ) = 1; linarith [t.property.1, s.property.2])
      have hk : k.val + 1 = j.val := by
        have he' : (k : ℝ) + 1 = j := by linarith [t.property.1, s.property.2]
        exact_mod_cast he'
      exact ht ▸ hs ▸ (hjoin k j hk).symm
  let M := Function.extend q g (fun _ => Classical.arbitrary E)
  have hM : ∀ z, M (q z) = g z := hfactor.extend_apply _
  refine ⟨⟨M, hquot.continuous_iff.mpr ?_⟩, fun j t => hM ⟨j, t⟩⟩
  convert hg using 1
  exact funext hM

lemma reference_ne_zero : reference ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Plane => v 0) h
  norm_num [reference] at h0

lemma velocity_continuous {c : RegularJordanCurve} (A : ArcPresentation c)
    (i : Fin A.count) : Continuous (fun t : unitInterval => velocity A i t) := by
  obtain ⟨δ, hδ, hs⟩ := A.smooth i
  have hd := hs.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht : (t : ℝ) ∈ Ioo (-δ) (1 + δ) := by
    constructor <;> linarith [t.property.1, t.property.2]
  exact (hd.continuousAt (isOpen_Ioo.mem_nhds ht)).comp
    continuous_subtype_val.continuousAt

lemma direction_continuous (o : Orientation ℝ Plane (Fin 2))
    {X : Type*} [TopologicalSpace X] {v : X → Plane} (hv : Continuous v)
    (h0 : ∀ t, v t ≠ 0) : Continuous (fun t => direction o (v t)) := by
  change Continuous (fun t => o.oangle reference (v t))
  have hh : Continuous (fun t : X => (reference, v t)) := continuous_const.prodMk hv
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht : ContinuousAt (fun p : Plane × Plane => o.oangle p.1 p.2)
      (reference, v t) :=
    o.continuousAt_oangle (x := (reference, v t)) reference_ne_zero (h0 t)
  exact ContinuousAt.comp (f := fun t : X => (reference, v t)) ht hh.continuousAt

def arcDirection {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (i : Fin A.count) : C(unitInterval, Real.Angle) :=
  ⟨fun t => direction o (velocity A i t),
    direction_continuous o (velocity_continuous A i) (fun t => A.regular i t t.property)⟩

lemma radianCovering : IsCoveringMap ((↑) : ℝ → Real.Angle) :=
  AddCircle.isCoveringMap_coe (2 * Real.pi)

/-- Every tangent arc has a continuous real angle. Its initial angle can be
chosen independently of the other arcs. -/
theorem choicesExist : Expected.choicesExist := by
  intro c o A
  have hex (i : Fin A.count) : ∃ L : C(unitInterval, ℝ),
      ∀ t, (L t : Real.Angle) = direction o (velocity A i t) := by
    let f := arcDirection o A i
    obtain ⟨L, hL, _⟩ := radianCovering.exists_path_lifts f (f 0).toReal
      (Real.Angle.coe_toReal _).symm
    exact ⟨L, fun t => congrFun hL t⟩
  choose L hL using hex
  exact ⟨⟨L, hL⟩⟩

/-- Continuous lifts of any angle path have the same endpoint increment.
The difference has constant image zero under the covering map, so it is
constant by uniqueness of lifts on the connected unit interval. -/
lemma angle_increment_eq {f g : C(unitInterval, ℝ)}
    (h : ∀ t, (f t : Real.Angle) = (g t : Real.Angle)) :
    f 1 - f 0 = g 1 - g 0 := by
  have hc : Continuous (fun t => f t - g t) := f.continuous.sub g.continuous
  have hz (t : unitInterval) : ((f t - g t : ℝ) : Real.Angle) = 0 := by
    rw [Real.Angle.coe_sub, h t, sub_self]
  have hconst := radianCovering.const_of_comp hc (fun t s => (hz t).trans (hz s).symm)
    (1 : unitInterval) 0
  linarith

/-- The source sum is independent of every separate arc-angle choice. -/
theorem choiceIndependence : Expected.choiceIndependence := by
  intro c o A θ φ
  have h (i : Fin A.count) : θ.angle i 1 - θ.angle i 0 =
      φ.angle i 1 - φ.angle i 0 :=
    angle_increment_eq (fun t => (θ.lifts i t).trans (φ.lifts i t).symm)
  exact ⟨h, Finset.sum_congr rfl (fun i _ => by rw [h i])⟩

lemma corner_not_pi {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (i : Fin A.count) :
    o.oangle (velocity A i 1) (velocity A (finRotate A.count i) 0) ≠
      (Real.pi : Real.Angle) := by
  intro h
  have hs := (o.oangle_eq_pi_iff_sameRay_neg.mp h).2.2
  have h1 := A.regular i 1 (by simp)
  have h0 := A.regular (finRotate A.count i) 0 (by simp)
  have hn := hs.inv_norm_smul_eq h1 (neg_ne_zero.mpr h0)
  exact A.noncuspidal i (by
    simpa only [NormedSpace.normalize, velocity, norm_neg, smul_neg] using hn)

/-- The strict range is exactly where real short rotations reverse sign;
reflex corners remain permitted. -/
theorem cornerBounds : Expected.cornerBounds := by
  intro c o A i
  refine ⟨Real.Angle.neg_pi_lt_toReal _, ?_⟩
  exact (Real.Angle.toReal_le_pi _).lt_of_ne
    (fun h => corner_not_pi o A i (Real.Angle.toReal_eq_pi_iff.mp h))

lemma corner_reversed {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (i : Fin A.count) :
    (o.oangle (-velocity A i 0)
      (-velocity A ((finRotate A.count).symm i) 1)).toReal =
        -cornerAngle o A ((finRotate A.count).symm i) := by
  rw [o.oangle_neg_neg, o.oangle_rev]
  have h := Real.Angle.toReal_neg_eq_neg_toReal_iff.mpr
    (corner_not_pi o A ((finRotate A.count).symm i))
  simpa only [cornerAngle, Equiv.apply_symm_apply] using h

lemma reversedArc_hasDerivAt {c : RegularJordanCurve} (A : ArcPresentation c)
    (i : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (reversedArc A i) (-velocity A i (1 - t)) t := by
  obtain ⟨δ, hδ, hs⟩ := A.smooth i
  have ht' : 1 - t ∈ Ioo (-δ) (1 + δ) := by
    constructor <;> linarith [ht.1, ht.2]
  have hd : DifferentiableAt ℝ (A.arc i) (1 - t) :=
    (hs.contDiffAt (isOpen_Ioo.mem_nhds ht')).differentiableAt (by simp)
  convert! hd.hasDerivAt.scomp t (HasDerivAt.const_sub 1 (hasDerivAt_id t)) using 1
  simp [velocity]

lemma reversedAngle_lifts {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    {A : ArcPresentation c} (θ : AngleChoices o A) (i : Fin A.count)
    (t : unitInterval) :
    (reversedAngle θ i t : Real.Angle) = direction o (-velocity A i (1 - t)) := by
  change ((θ.angle i (unitInterval.symm t) + Real.pi : ℝ) : Real.Angle) = _
  rw [Real.Angle.coe_add, θ.lifts]
  unfold direction
  have ht : 1 - (t : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [t.property.1, t.property.2]
  exact (o.oangle_neg_right reference_ne_zero (A.regular i (1 - t) ht)).symm

/-- Physical reversal of the smooth arcs and all signed corner rotations,
including every independent choice of continuous reversed arc angles. -/
theorem reversal : Expected.reversal := by
  intro c o A θ
  have hr : reversedTotalTurning θ = -totalTurning θ := by
    unfold reversedTotalTurning totalTurning
    simp only [reversedAngle, ContinuousMap.coe_mk,
      unitInterval.symm_zero, unitInterval.symm_one]
    simp_rw [corner_reversed]
    have hsum : (∑ i : Fin A.count, cornerAngle o A ((finRotate A.count).symm i)) =
        ∑ i : Fin A.count, cornerAngle o A i :=
      Equiv.sum_comp (finRotate A.count).symm (cornerAngle o A)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rw [hsum]
    ring
  refine ⟨fun i t ht => reversedArc_hasDerivAt A i ht, reversedAngle_lifts θ, hr, ?_⟩
  intro ψ hψ
  have hinc (i : Fin A.count) : ψ i 1 - ψ i 0 =
      reversedAngle θ i 1 - reversedAngle θ i 0 :=
    angle_increment_eq (fun t => (hψ i t).trans (reversedAngle_lifts θ i t).symm)
  calc
    reversedTurningWith o A ψ = reversedTotalTurning θ :=
      Finset.sum_congr rfl (fun i _ => by rw [hinc i])
    _ = -totalTurning θ := hr

lemma direction_normalize (o : Orientation ℝ Plane (Fin 2)) {v : Plane} (hv : v ≠ 0) :
    direction o (NormedSpace.normalize v) = direction o v := by
  exact o.oangle_smul_right_of_pos reference v (inv_pos.mpr (norm_pos_iff.mpr hv))

def slotMap {c : RegularJordanCurve} (A : ArcPresentation c)
    (j : Fin (2 * A.count)) : C(unitInterval, unitInterval) :=
  ⟨slot A j, by
    apply Continuous.subtype_mk
    change Continuous (fun t : unitInterval => ((j : ℝ) + t) / (2 * A.count))
    fun_prop⟩

/-- The common endpoints of the pair of slots belonging to each arc. -/
def grid {c : RegularJordanCurve} (A : ArcPresentation c)
    (i : Fin (A.count + 1)) : unitInterval :=
  ⟨(i : ℝ) / A.count, by
    have hn : (0 : ℝ) < A.count := by exact_mod_cast A.positive
    constructor
    · positivity
    · apply (div_le_one hn).mpr
      exact_mod_cast Nat.lt_succ_iff.mp i.isLt⟩

lemma grid_first {c : RegularJordanCurve} (A : ArcPresentation c) : grid A 0 = 0 := by
  apply Subtype.ext
  simp [grid]

lemma grid_last {c : RegularJordanCurve} (A : ArcPresentation c) :
    grid A (Fin.last A.count) = 1 := by
  apply Subtype.ext
  simp [grid, ne_of_gt A.positive]

lemma slot_arc_start {c : RegularJordanCurve} (A : ArcPresentation c) (i : Fin A.count) :
    slot A ⟨2 * i.val, by omega⟩ 0 = grid A i.castSucc := by
  apply Subtype.ext
  dsimp [slot, grid]
  push_cast
  ring

lemma slot_arc_corner {c : RegularJordanCurve} (A : ArcPresentation c) (i : Fin A.count) :
    slot A ⟨2 * i.val, by omega⟩ 1 = slot A ⟨2 * i.val + 1, by omega⟩ 0 := by
  apply Subtype.ext
  simp [slot, Nat.cast_add, Nat.cast_mul]

lemma slot_corner_end {c : RegularJordanCurve} (A : ArcPresentation c) (i : Fin A.count) :
    slot A ⟨2 * i.val + 1, by omega⟩ 1 = grid A i.succ := by
  apply Subtype.ext
  dsimp [slot, grid]
  push_cast
  ring

/-- Angle change of a restriction of an actual global lift along one smooth
arc agrees with every independently chosen continuous arc angle. -/
lemma circuit_arc_increment {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    {A : ArcPresentation c} (T : TangentCircuit o A) (θ : AngleChoices o A)
    (L : C(unitInterval, ℝ)) (hL : IsCircuitLift T L) (i : Fin A.count) :
    L (slot A ⟨2 * i.val, by omega⟩ 1) - L (slot A ⟨2 * i.val, by omega⟩ 0) =
      θ.angle i 1 - θ.angle i 0 := by
  apply angle_increment_eq (f := L.comp (slotMap A ⟨2 * i.val, by omega⟩))
    (g := θ.angle i)
  intro t
  change (L (slot A ⟨2 * i.val, by omega⟩ t) : Real.Angle) = (θ.angle i t : Real.Angle)
  rw [hL, T.on_arc]
  exact (direction_normalize o (A.regular i t t.property)).trans (θ.lifts i t).symm

/-- The literal short rotation has real angle change equal to its signed
exterior angle, rather than an unspecified integer translate. -/
lemma circuit_corner_increment {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    {A : ArcPresentation c} (T : TangentCircuit o A) (θ : AngleChoices o A)
    (L : C(unitInterval, ℝ)) (hL : IsCircuitLift T L) (i : Fin A.count) :
    L (slot A ⟨2 * i.val + 1, by omega⟩ 1) -
      L (slot A ⟨2 * i.val + 1, by omega⟩ 0) = cornerAngle o A i := by
  let f : C(unitInterval, ℝ) :=
    ⟨fun t => θ.angle i 1 + (t : ℝ) * cornerAngle o A i, by fun_prop⟩
  have heq := angle_increment_eq
    (f := L.comp (slotMap A ⟨2 * i.val + 1, by omega⟩)) (g := f) (fun t => by
      change (L (slot A ⟨2 * i.val + 1, by omega⟩ t) : Real.Angle) =
        (θ.angle i 1 + (t : ℝ) * cornerAngle o A i : ℝ)
      rw [hL, T.on_corner, Real.Angle.coe_add, θ.lifts]
      unfold direction
      have hv : velocity A i 1 ≠ 0 := A.regular i 1 (by simp)
      rw [o.oangle_rotation_right (x := reference)
        (y := NormedSpace.normalize (velocity A i 1)) reference_ne_zero
        ((NormedSpace.normalize_eq_zero_iff _).not.mpr hv)]
      exact congrArg (fun d : Real.Angle => d + ((t : ℝ) * cornerAngle o A i : ℝ))
        (direction_normalize o (v := velocity A i 1) (A.regular i 1 (by simp))))
  simpa [f, slotMap] using heq

/-- Finite telescoping, with the actual circuit slots, identifies the source
sum with the endpoint increment of every global angle lift. -/
theorem circuit_increment_eq_total {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} {A : ArcPresentation c}
    (T : TangentCircuit o A) (θ : AngleChoices o A) (L : C(unitInterval, ℝ))
    (hL : IsCircuitLift T L) : totalTurning θ = L 1 - L 0 := by
  let F : Fin (A.count + 1) → ℝ := fun i => L (grid A i)
  have hstep (i : Fin A.count) : θ.angle i 1 - θ.angle i 0 + cornerAngle o A i =
      F i.succ - F i.castSucc := by
    rw [← circuit_arc_increment T θ L hL i, ← circuit_corner_increment T θ L hL i,
      slot_arc_corner, slot_arc_start, slot_corner_end]
    dsimp [F]
    ring
  unfold totalTurning
  simp_rw [hstep]
  rw [Finset.sum_sub_distrib]
  have hs := (Fin.sum_univ_succ F).symm.trans (Fin.sum_univ_castSucc F)
  have htel : (∑ i : Fin A.count, F i.succ) - (∑ i : Fin A.count, F i.castSucc) =
      F (Fin.last A.count) - F 0 := by linarith
  simpa [F, grid_first, grid_last] using htel

/-- The circle covering provides global lifts of the actual filled loop. -/
lemma circuit_lift_exists {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    {A : ArcPresentation c} (T : TangentCircuit o A) :
    ∃ L : C(unitInterval, ℝ), IsCircuitLift T L := by
  obtain ⟨L, hL, _⟩ := radianCovering.exists_path_lifts T.angleLoop.toContinuousMap
    (direction o (T.map 0)).toReal (Real.Angle.coe_toReal _).symm
  exact ⟨L, fun t => congrFun hL t⟩

/-- The integer here is the genuine Mathlib fundamental-group winding,
with the radian period 2π and an arbitrary initial lift value. -/
lemma circuit_increment_eq_winding {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} {A : ArcPresentation c}
    (T : TangentCircuit o A) (L : C(unitInterval, ℝ)) (hL : IsCircuitLift T L) :
    L 1 - L 0 = 2 * Real.pi * (T.winding : ℝ) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hw := AddCircle.windingNumber_eq_div (p := 2 * Real.pi) T.angleLoop L
    (funext hL)
  change (T.winding : ℝ) = (L 1 - L 0) / (2 * Real.pi) at hw
  exact ((eq_div_iff (by positivity : (2 * Real.pi : ℝ) ≠ 0)).mp hw).symm.trans
    (mul_comm _ _)

/-- Continuity of the genuine normalized derivative on each closed arc. -/
def tangentArc {c : RegularJordanCurve} (A : ArcPresentation c)
    (i : Fin A.count) : C(unitInterval, Plane) :=
  ⟨fun t => NormedSpace.normalize (velocity A i t), by
    unfold NormedSpace.normalize
    exact ((velocity_continuous A i).norm.inv₀
      (fun t => norm_ne_zero_iff.mpr (A.regular i t t.property))).smul
        (velocity_continuous A i)⟩

/-- The literal corner rotation; zero and negative angles are retained. -/
def cornerPath {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (i : Fin A.count) : C(unitInterval, Plane) :=
  ⟨fun t => o.rotation ((t : ℝ) * cornerAngle o A i : ℝ)
      (NormedSpace.normalize (velocity A i 1)), by
    simp only [Orientation.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
    fun_prop⟩

lemma cornerPath_start {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (i : Fin A.count) : cornerPath o A i 0 = tangentArc A i 1 := by
  simp [cornerPath, tangentArc, o.rotation_zero]

lemma cornerPath_end {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (i : Fin A.count) :
    cornerPath o A i 1 = tangentArc A (finRotate A.count i) 0 := by
  have hv : velocity A i 1 ≠ 0 := A.regular i 1 (by simp)
  have hw : velocity A (finRotate A.count i) 0 ≠ 0 := A.regular (finRotate A.count i) 0 (by simp)
  have hangle : o.oangle (NormedSpace.normalize (velocity A i 1))
      (NormedSpace.normalize (velocity A (finRotate A.count i) 0)) =
      o.oangle (velocity A i 1) (velocity A (finRotate A.count i) 0) := by
    rw [NormedSpace.normalize, NormedSpace.normalize]
    rw [o.oangle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hv)),
      o.oangle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hw))]
  change o.rotation ((1 : ℝ) * cornerAngle o A i : ℝ) _ = _
  rw [one_mul, cornerAngle, Real.Angle.coe_toReal, ← hangle]
  exact (o.rotation_oangle_eq_iff_norm_eq _ _).mpr
    ((NormedSpace.norm_normalize hv).trans (NormedSpace.norm_normalize hw).symm)

/-- Alternating smooth and corner pieces in the prescribed order. -/
def tangentPiece {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (j : Fin (2 * A.count)) : C(unitInterval, Plane) :=
  if j.val % 2 = 0 then tangentArc A ⟨j.val / 2, by omega⟩
  else cornerPath o A ⟨j.val / 2, by omega⟩

lemma tangentPiece_even {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (i : Fin A.count) :
    tangentPiece o A ⟨2 * i.val, by omega⟩ = tangentArc A i := by
  simp [tangentPiece, Nat.mul_div_right]

lemma tangentPiece_odd {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (i : Fin A.count) :
    tangentPiece o A ⟨2 * i.val + 1, by omega⟩ = cornerPath o A i := by
  simp [tangentPiece, Nat.add_div, Nat.mul_div_right]

lemma tangentPiece_join {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (j k : Fin (2 * A.count)) (hjk : j.val + 1 = k.val) :
    tangentPiece o A j 1 = tangentPiece o A k 0 := by
  by_cases hj : j.val % 2 = 0
  · let i : Fin A.count := ⟨j.val / 2, by omega⟩
    have hj' : j = ⟨2 * i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
    have hk' : k = ⟨2 * i.val + 1, by omega⟩ := Fin.ext (by dsimp [i]; omega)
    simp only [hj', hk', tangentPiece_even, tangentPiece_odd, cornerPath_start]
  · let i : Fin A.count := ⟨j.val / 2, by omega⟩
    let l : Fin A.count := ⟨k.val / 2, by omega⟩
    have hj' : j = ⟨2 * i.val + 1, by omega⟩ := Fin.ext (by dsimp [i]; omega)
    have hk' : k = ⟨2 * l.val, by omega⟩ := Fin.ext (by dsimp [l]; omega)
    have hrot : finRotate A.count i = l := by
      rw [finRotate_apply]
      apply Fin.ext
      letI : NeZero A.count := ⟨ne_of_gt A.positive⟩
      simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      rw [Nat.mod_eq_of_lt (by dsimp [i]; omega)]
      dsimp [i, l]
      omega
    simp only [hj', hk', tangentPiece_odd, tangentPiece_even, cornerPath_end, hrot]

/-- Construction of the filled unit-tangent circuit, including its actual
short rotations and uniform parametrization. No turning theorem is used. -/
theorem circuitExists : Expected.circuitExists := by
  intro c o A
  have hn : 0 < 2 * A.count := by have := A.positive; omega
  obtain ⟨M, hM⟩ := glue_uniform_slots (2 * A.count) hn (tangentPiece o A)
    (tangentPiece_join o A)
  have hslot (j : Fin (2 * A.count)) (t : unitInterval) :
      M (slot A j t) = tangentPiece o A j t := by
        simpa only [slot, uniformSlot, Nat.cast_mul, Nat.cast_ofNat] using hM j t
  have harc (i : Fin A.count) (t : unitInterval) :
      M (slot A ⟨2 * i.val, by omega⟩ t) = NormedSpace.normalize (velocity A i t) := by
    rw [hslot, tangentPiece_even]
    rfl
  have hcorner (i : Fin A.count) (t : unitInterval) :
      M (slot A ⟨2 * i.val + 1, by omega⟩ t) =
        o.rotation ((t : ℝ) * cornerAngle o A i : ℝ)
          (NormedSpace.normalize (velocity A i 1)) := by
    rw [hslot, tangentPiece_odd]
    rfl
  refine ⟨⟨M, ?_, ?_, harc, hcorner⟩⟩
  · intro t
    obtain ⟨⟨j, s⟩, rfl⟩ := uniformSlot_surjective (2 * A.count) hn t
    rw [hM]
    unfold tangentPiece
    split_ifs
    · exact NormedSpace.norm_normalize (A.regular _ s s.property)
    · change ‖o.rotation _ _‖ = 1
      rw [LinearIsometryEquiv.norm_map]
      exact NormedSpace.norm_normalize (A.regular _ 1 (by simp))
  · let i : Fin A.count := ⟨A.count - 1, by omega⟩
    let z : Fin A.count := ⟨0, A.positive⟩
    have hlast : slot A ⟨2 * i.val + 1, by dsimp [i]; omega⟩ 1 = 1 := by
      apply Subtype.ext
      change ((2 * i.val + 1 : ℕ) + (1 : ℝ)) / (2 * A.count) = 1
      have he : 2 * i.val + 1 = 2 * A.count - 1 := by dsimp [i]; omega
      have hi : i.val + 1 = A.count := by dsimp [i]; omega
      apply (div_eq_one_iff_eq (by exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (ne_of_gt A.positive)) : (2 * (A.count : ℝ)) ≠ 0)).mpr
      push_cast
      have hi' : (i.val : ℝ) + 1 = A.count := by exact_mod_cast hi
      linarith
    have hfirst : slot A ⟨2 * z.val, by dsimp [z]; omega⟩ 0 = 0 := by
      apply Subtype.ext
      simp [slot, z]
    have hrot : finRotate A.count i = z := by
      rw [finRotate_apply]
      apply Fin.ext
      letI : NeZero A.count := ⟨ne_of_gt A.positive⟩
      change (i + 1).val = 0
      simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      have hi : i.val + 1 = A.count := by dsimp [i]; omega
      rw [hi, Nat.mod_self]
    calc
      M 1 = M (slot A ⟨2 * i.val + 1, by dsimp [i]; omega⟩ 1) := congrArg M hlast.symm
      _ = cornerPath o A i 1 := by rw [hslot, tangentPiece_odd]
      _ = tangentArc A z 0 := by rw [cornerPath_end, hrot]
      _ = M 0 := by simpa only [hfirst, tangentArc, ContinuousMap.coe_mk] using (harc z 0).symm

/-- Complete arithmetic and winding comparison for the actual circuit. -/
theorem circuitLiftFormula : Expected.circuitLiftFormula := by
  intro c o A T
  exact ⟨circuit_lift_exists T, fun θ L hL =>
    ⟨circuit_increment_eq_total T θ L hL, circuit_increment_eq_winding T L hL⟩⟩

lemma exists_unit_slot_lt (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) n) :
    ∃ j : Fin n, (j : ℝ) ≤ x ∧ x < (j : ℝ) + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, by simpa using hx⟩
    · by_cases hxn : x < n
      · obtain ⟨j, hj⟩ := ih (by omega) ⟨hx.1, hxn⟩
        exact ⟨j.castSucc, by simpa using hj⟩
      · exact ⟨Fin.last n, by simpa using (show (n : ℝ) ≤ x ∧ x < n + 1 from
          ⟨le_of_not_gt hxn, by simpa using hx.2⟩)⟩

/-- Sorted enumeration of a finite set of at least four parameters containing
both endpoints, with no geometric assumptions. -/
lemma partition_of_finset (S : Finset ℝ) (hcard : 4 ≤ S.card)
    (hS : ∀ x ∈ S, x ∈ Icc (0 : ℝ) 1) (h0 : 0 ∈ S) (h1 : 1 ∈ S) :
    ∃ Q : Partition, Set.range Q.time = (S : Set ℝ) := by
  let n := S.card - 1
  have hc : S.card = n + 1 := by dsimp [n]; omega
  let e := S.orderEmbOfFin hc
  have hr : Set.range e = (S : Set ℝ) := Finset.range_orderEmbOfFin S hc
  have hm : StrictMono e := e.strictMono
  have ht (i : Fin (n + 1)) : e i ∈ Icc (0 : ℝ) 1 := hS _ (by simp [e])
  have he0 : e 0 = 0 := by
    obtain ⟨i, hi⟩ : (0 : ℝ) ∈ Set.range e := by rw [hr]; exact h0
    exact le_antisymm (by simpa [hi] using hm.monotone (show (0 : Fin (n+1)) ≤ i from Fin.zero_le i)) (ht 0).1
  have he1 : e (Fin.last n) = 1 := by
    obtain ⟨i, hi⟩ : (1 : ℝ) ∈ Set.range e := by rw [hr]; exact h1
    exact le_antisymm (ht _).2 (by simpa [hi] using hm.monotone (Fin.le_last i))
  exact ⟨⟨n, by dsimp [n]; omega, e, hm, he0, he1⟩, hr⟩

/-- The partition parameters all lie in the closed unit interval. -/
lemma partition_time_mem (Q : Partition) (i : Fin (Q.count + 1)) :
    Q.time i ∈ Icc (0 : ℝ) 1 := by
  constructor
  · simpa only [Q.first] using Q.strictMono.monotone (Fin.zero_le i)
  · simpa only [Q.last] using Q.strictMono.monotone (Fin.le_last i)

/-- No parameter of a strictly increasing partition lies strictly between
consecutive knots. -/
lemma partition_no_between (Q : Partition) (i : Fin Q.count) (j : Fin (Q.count + 1)) :
    ¬ (Q.time i.castSucc < Q.time j ∧ Q.time j < Q.time i.succ) := by
  intro h
  have h0 := Q.strictMono.lt_iff_lt.mp h.1
  have h1 := Q.strictMono.lt_iff_lt.mp h.2
  have := j.isLt
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h0 h1
  omega

/-- Insert all prescribed knots into a sufficiently fine uniform grid and
sort the union. Adding knots cannot enlarge the mesh. -/
theorem finePartitions : Expected.finePartitions := by
  classical
  intro c A δ hδ
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  let N := m + 3
  have hN : 0 < N := by dsimp [N]; omega
  have hN3 : 3 ≤ N := by dsimp [N]; omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep : 1 / (N : ℝ) < δ := by
    apply (div_lt_iff₀ hN').mpr
    have hm' : 1 / δ < (N : ℝ) := by dsimp [N]; push_cast; linarith
    have := (div_lt_iff₀ hδ).mp hm'
    nlinarith
  let g : Fin (N + 1) → ℝ := fun j => (j : ℝ) / N
  have hginj : Function.Injective g := by
    intro i j hij
    have hij' : (i : ℝ) = j := (div_left_inj' (ne_of_gt hN')).mp hij
    apply Fin.ext
    exact_mod_cast hij'
  let G : Finset ℝ := Finset.univ.image g
  let S : Finset ℝ := G ∪ Finset.univ.image A.time
  have hG : G ⊆ S := Finset.subset_union_left
  have hgmem (j : Fin (N + 1)) : g j ∈ S := hG (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hcard : 4 ≤ S.card := by
    have hGc : G.card = N + 1 := by simp [G, Finset.card_image_of_injective _ hginj]
    have := Finset.card_le_card hG
    omega
  have hS : ∀ x ∈ S, x ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      constructor
      · exact div_nonneg (by positivity) hN'.le
      · apply (div_le_one hN').mpr
        exact_mod_cast (show j.val ≤ N by omega)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      constructor
      · simpa only [A.first] using A.strictMono.monotone (Fin.zero_le i)
      · simpa only [A.last] using A.strictMono.monotone (Fin.le_last i)
  have h0 : 0 ∈ S := by simpa [g] using hgmem 0
  have h1 : 1 ∈ S := by simpa [g, ne_of_gt hN'] using hgmem (Fin.last N)
  obtain ⟨Q, hQ⟩ := partition_of_finset S hcard hS h0 h1
  refine ⟨Q, ?_, ?_⟩
  · intro i
    have hi : A.time i ∈ S := Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have hi' : A.time i ∈ Set.range Q.time := by rw [hQ]; exact hi
    exact hi'
  · intro i
    by_contra hi
    have hgap : δ ≤ Q.time i.succ - Q.time i.castSucc := le_of_not_gt hi
    let a := Q.time i.castSucc
    let b := Q.time i.succ
    have ha := partition_time_mem Q i.castSucc
    have hb := partition_time_mem Q i.succ
    change a ∈ Icc (0 : ℝ) 1 at ha
    change b ∈ Icc (0 : ℝ) 1 at hb
    have hab : a < b := Q.strictMono (by simp [Fin.lt_def])
    obtain ⟨j, hj0, hj1⟩ := exists_unit_slot_lt N hN (N * a)
      ⟨mul_nonneg hN'.le ha.1, by nlinarith [hb.2]⟩
    let k : Fin (N + 1) := j.succ
    have hka : a < g k := by
      apply (lt_div_iff₀ hN').mpr
      simpa [k, g, mul_comm] using hj1
    have hkb : g k < b := by
      have hg : g k ≤ a + 1 / (N : ℝ) := by
        apply (div_le_iff₀ hN').mpr
        have hdiv : (1 / (N : ℝ)) * N = 1 := by field_simp
        dsimp [g, k]
        push_cast
        nlinarith
      dsimp [a, b] at *
      linarith
    obtain ⟨l, hl⟩ : g k ∈ Set.range Q.time := by rw [hQ]; exact hgmem k
    exact partition_no_between Q i l (by simpa only [hl] using And.intro hka hkb)

/-- Patch the original restriction with its genuine right germ at a and
left germ at b. Endpoint smoothness follows from local agreement with those
germs; no assertion about the derivative of a nonsmooth curve is used. -/
lemma closed_arc_extension (c : RegularJordanCurve) (a b : ℝ) (hab : a < b)
    (hno : ∀ t ∈ Ioo a b, (t : P202Specs.PlanarRegionTopology.ParameterCircle) ∉ c.joins) :
    ∃ (F : ℝ → Plane) (ε : ℝ), 0 < ε ∧
      EqOn F (P202Specs.PlanarRegionTopology.realLift c.parametrization) (Icc a b) ∧
      ContDiffOn ℝ ∞ F (Ioo (a - ε) (b + ε)) := by
  classical
  obtain ⟨δa, la, ra, hδa, hla, hra, hela, hera, hnla, hnra, hna⟩ := c.regular_joins a
  obtain ⟨δb, lb, rb, hδb, hlb, hrb, helb, herb, hnlb, hnrb, hnb⟩ := c.regular_joins b
  let f := P202Specs.PlanarRegionTopology.realLift c.parametrization
  let F : ℝ → Plane := fun t => if t < a then ra t else if b < t then lb t else f t
  let ε := min δa δb / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεa : ε < δa := by dsimp [ε]; linarith [min_le_left δa δb]
  have hεb : ε < δb := by dsimp [ε]; linarith [min_le_right δa δb]
  have heq : EqOn F f (Icc a b) := by
    intro t ht
    simp [F, not_lt.mpr ht.1, not_lt.mpr ht.2]
  have hFa : F =ᶠ[nhds a] ra := by
    filter_upwards [Ioo_mem_nhds (by linarith : a - δa < a)
      (show a < min (a + δa) b by exact lt_min (by linarith) hab)] with t ht
    dsimp [F]
    split_ifs with hta hbt
    · rfl
    · exfalso; linarith [ht.2, min_le_right (a + δa) b]
    · exact (hera ⟨by linarith, by linarith [ht.2, min_le_left (a + δa) b]⟩).symm
  have hFb : F =ᶠ[nhds b] lb := by
    filter_upwards [Ioo_mem_nhds
      (show max a (b - δb) < b by exact max_lt hab (by linarith))
      (by linarith : b < b + δb)] with t ht
    dsimp [F]
    split_ifs with hta hbt
    · exfalso; linarith [ht.1, le_max_left a (b - δb)]
    · rfl
    · exact (helb ⟨by linarith [ht.1, le_max_right a (b - δb)], by linarith⟩).symm
  refine ⟨F, ε, hε, heq, ?_⟩
  apply isOpen_Ioo.contDiffOn_iff.mpr
  intro t ht
  rcases lt_trichotomy t a with hta | rfl | hat
  · have hs : ContDiffAt ℝ ∞ ra t := hra.contDiffAt
      (isOpen_Ioo.mem_nhds ⟨by linarith [ht.1], by linarith⟩)
    apply hs.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hta] with s hs
    simp [F, hs]
  · exact (hra.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).congr_of_eventuallyEq hFa
  · rcases lt_trichotomy t b with htb | rfl | hbt
    · apply (c.smooth_off_joins t (hno t ⟨hat, htb⟩)).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hat htb] with s hs
      simp [F, not_lt.mpr hs.1.le, not_lt.mpr hs.2.le, f]
    · exact (hlb.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).congr_of_eventuallyEq hFb
    · have hs : ContDiffAt ℝ ∞ lb t := hlb.contDiffAt
        (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith [ht.2]⟩)
      apply hs.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hbt] with s hs
      simp [F, not_lt.mpr (by linarith : a ≤ s), hs]

/-- Any smooth extension of a nondegenerate subarc without internal joins
has nonzero derivative on its whole closed parameter interval. -/
lemma closed_arc_regular (c : RegularJordanCurve) {a b ε : ℝ} (hab : a < b)
    (hε : 0 < ε) {F : ℝ → Plane}
    (he : EqOn F (P202Specs.PlanarRegionTopology.realLift c.parametrization) (Icc a b))
    (hs : ContDiffOn ℝ ∞ F (Ioo (a - ε) (b + ε)))
    (hno : ∀ t ∈ Ioo a b, (t : P202Specs.PlanarRegionTopology.ParameterCircle) ∉ c.joins) :
    ∀ t ∈ Icc a b, deriv F t ≠ 0 := by
  intro t ht
  have hd : DifferentiableAt ℝ F t :=
    (hs.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith [ht.1], by linarith [ht.2]⟩)).differentiableAt (by simp)
  by_cases hta : t = a
  · subst t
    obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hn⟩ := c.regular_joins a
    have hdr : DifferentiableAt ℝ r a :=
      (hr.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).differentiableAt (by simp)
    have hF := he.eventuallyEq_of_mem (Icc_mem_nhdsGE hab)
    have hR := her.eventuallyEq_of_mem (Icc_mem_nhdsGE (by linarith : a < a + δ))
    rw [P202.PlanarRegionTopology.deriv_eq_of_eventuallyEq_ge hd hdr (hF.trans hR.symm)]
    exact hnr
  by_cases htb : t = b
  · subst t
    obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hn⟩ := c.regular_joins b
    have hdl : DifferentiableAt ℝ l b :=
      (hl.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).differentiableAt (by simp)
    have hF := he.eventuallyEq_of_mem (Icc_mem_nhdsLE hab)
    have hL := hel.eventuallyEq_of_mem (Icc_mem_nhdsLE (by linarith : b - δ < b))
    rw [P202.PlanarRegionTopology.deriv_eq_of_eventuallyEq_le hd hdl (hF.trans hL.symm)]
    exact hnl
  · have hi : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
    have hf := he.eventuallyEq_of_mem (Icc_mem_nhds hi.1 hi.2)
    rw [hf.deriv_eq]
    exact P202.PlanarRegionTopology.regular_nonjoin_deriv_ne_zero c (hno t hi)

/-- Noncuspidality passes from the original one-sided germs to any two actual
smooth restrictions on adjacent parameter intervals. -/
lemma adjacent_arc_noncuspidal (c : RegularJordanCurve) {a b d : ℝ}
    (hab : a < b) (hbd : b < d) {F G : ℝ → Plane}
    (hF : DifferentiableAt ℝ F b) (hG : DifferentiableAt ℝ G b)
    (heF : EqOn F (P202Specs.PlanarRegionTopology.realLift c.parametrization) (Icc a b))
    (heG : EqOn G (P202Specs.PlanarRegionTopology.realLift c.parametrization) (Icc b d)) :
    NormedSpace.normalize (deriv F b) ≠ -NormedSpace.normalize (deriv G b) := by
  obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hn⟩ := c.regular_joins b
  have hdl : DifferentiableAt ℝ l b :=
    (hl.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).differentiableAt (by simp)
  have hdr : DifferentiableAt ℝ r b :=
    (hr.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).differentiableAt (by simp)
  have hlF := heF.eventuallyEq_of_mem (Icc_mem_nhdsLE hab)
  have hlc := hel.eventuallyEq_of_mem (Icc_mem_nhdsLE (by linarith : b - δ < b))
  have hrG := heG.eventuallyEq_of_mem (Icc_mem_nhdsGE hbd)
  have hrc := her.eventuallyEq_of_mem (Icc_mem_nhdsGE (by linarith : b < b + δ))
  rwa [P202.PlanarRegionTopology.deriv_eq_of_eventuallyEq_le hF hdl (hlF.trans hlc.symm),
    P202.PlanarRegionTopology.deriv_eq_of_eventuallyEq_ge hG hdr (hrG.trans hrc.symm)]

/-- Positive affine reparametrization has the actual positively scaled derivative. -/
lemma affine_arc_deriv {F : ℝ → Plane} {a b ε t : ℝ} (hab : a < b) (hε : 0 < ε)
    (hF : ContDiffOn ℝ ∞ F (Ioo (a - ε) (b + ε))) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => F (a + (b - a) * s))
      ((b - a) • deriv F (a + (b - a) * t)) t := by
  have hmem : a + (b - a) * t ∈ Ioo (a - ε) (b + ε) := by
    constructor <;> nlinarith [ht.1, ht.2]
  have hd := (hF.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp)
  convert! hd.hasDerivAt.scomp t (((hasDerivAt_id t).const_mul (b - a)).const_add a) using 1
  simp

/-- The affine restriction retains an honest smooth neighborhood of [0,1]. -/
lemma affine_arc_smooth {F : ℝ → Plane} {a b ε : ℝ} (hab : a < b) (hε : 0 < ε)
    (hF : ContDiffOn ℝ ∞ F (Ioo (a - ε) (b + ε))) :
    ∃ η : ℝ, 0 < η ∧ ContDiffOn ℝ ∞ (fun s => F (a + (b - a) * s))
      (Ioo (-η) (1 + η)) := by
  let η := ε / (b - a)
  have hη : 0 < η := div_pos hε (sub_pos.mpr hab)
  have he : η * (b - a) = ε := by dsimp [η]; field_simp
  refine ⟨η, hη, ?_⟩
  have haff : ContDiff ℝ ∞ (fun t : ℝ => a + (b - a) * t) := by fun_prop
  apply hF.comp haff.contDiffOn
  intro t ht
  constructor <;> nlinarith [ht.1, ht.2]

/-- A finite join set admits a strictly increasing partition with no join in
any open subinterval. Representatives are taken in [0,1), so the cyclic seam
is retained as an endpoint rather than discarded. -/
lemma join_partition (c : RegularJordanCurve) :
    ∃ Q : Partition, ∀ (i : Fin Q.count) (t : ℝ),
      t ∈ Ioo (Q.time i.castSucc) (Q.time i.succ) →
      (t : P202Specs.PlanarRegionTopology.ParameterCircle) ∉ c.joins := by
  classical
  let r : P202Specs.PlanarRegionTopology.ParameterCircle → ℝ :=
    fun q => (AddCircle.equivIco (1 : ℝ) 0 q).val
  let B : Finset ℝ := {0, 1 / 3, 2 / 3, 1}
  let S := B ∪ c.joins.image r
  have hB : B ⊆ S := Finset.subset_union_left
  have hcard : 4 ≤ S.card := by
    have hBc : B.card = 4 := by norm_num [B]
    have := Finset.card_le_card hB
    omega
  have hS : ∀ x ∈ S, x ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simp only [B, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx
      have h := (AddCircle.equivIco (1 : ℝ) 0 q).property
      exact ⟨h.1, by simpa using h.2.le⟩
  obtain ⟨Q, hQ⟩ := partition_of_finset S hcard hS
    (hB (by simp [B])) (hB (by simp [B]))
  refine ⟨Q, ?_⟩
  intro i t ht hj
  have ha := partition_time_mem Q i.castSucc
  have hb := partition_time_mem Q i.succ
  have ht01 : t ∈ Ico (0 : ℝ) (0 + 1) := ⟨by linarith [ha.1, ht.1], by linarith [hb.2, ht.2]⟩
  have hr : r (t : P202Specs.PlanarRegionTopology.ParameterCircle) = t :=
    AddCircle.equivIco_coe_of_mem ht01
  have htS : t ∈ S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hj, hr⟩)
  obtain ⟨j, hj⟩ : t ∈ Set.range Q.time := by rw [hQ]; exact htS
  exact partition_no_between Q i j (by rw [hj]; exact ⟨ht.1, ht.2⟩)

/-- The cyclic join is checked on the actual original curve using its period,
not by imposing agreement of arbitrarily chosen endpoint extensions. -/
lemma closing_arc_noncuspidal (c : RegularJordanCurve) {a b : ℝ}
    (ha : a < 1) (hb : 0 < b) {F G : ℝ → Plane}
    (hF : DifferentiableAt ℝ F 1) (hG : DifferentiableAt ℝ G 0)
    (heF : EqOn F (P202Specs.PlanarRegionTopology.realLift c.parametrization) (Icc a 1))
    (heG : EqOn G (P202Specs.PlanarRegionTopology.realLift c.parametrization) (Icc 0 b)) :
    NormedSpace.normalize (deriv F 1) ≠ -NormedSpace.normalize (deriv G 0) := by
  let H : ℝ → Plane := fun t => G (t - 1)
  have hG' : DifferentiableAt ℝ G ((1 : ℝ) - 1) := by simpa using hG
  have hH : DifferentiableAt ℝ H 1 := hG'.comp (f := fun t : ℝ => t - 1) 1 (differentiableAt_id.sub_const (1 : ℝ))
  have hdH : deriv H 1 = deriv G 0 := by simp [H, deriv_comp_sub_const]
  have heH : EqOn H (P202Specs.PlanarRegionTopology.realLift c.parametrization) (Icc 1 (1 + b)) := by
    intro t ht
    change G (t - 1) = _
    rw [heG ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    unfold P202Specs.PlanarRegionTopology.realLift
    congr 1
    simp only [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
  have h := adjacent_arc_noncuspidal c ha (by linarith : (1 : ℝ) < 1 + b) hF hH heF heH
  simpa only [hdH] using h

/-- Every original regular Jordan curve admits a finite smooth presentation.
Local one-sided smooth germs supply actual extensions at all endpoints. -/
theorem presentationExists : Expected.presentationExists := by
  intro c
  obtain ⟨Q, hno⟩ := join_partition c
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
    Q.first, Q.last, arc, ?_, ?_, ?_, ?_⟩⟩
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

/-- Unconditional existence and the complete winding formula. -/
theorem tangentWinding : Expected.tangentWinding := ⟨circuitExists, circuitLiftFormula⟩

end P202.PlaneTurning
