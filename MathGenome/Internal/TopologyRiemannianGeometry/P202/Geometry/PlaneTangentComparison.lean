import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneTangentComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlaneTurningData
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Topology
open scoped BigOperators unitInterval

namespace P202.PlaneTangentComparison
open P202Specs.PlaneTurning
open P202Specs.PlaneTangentComparison
open P202Specs.PlanarRegionTopology (Plane RegularJordanCurve realLift ParameterCircle)

lemma partition_time_lt_one (Q : Partition) (i : Fin Q.count) :
    Q.time i.castSucc < 1 := by
  rw [← Q.last]
  exact Q.strictMono (by simpa using i.isLt)

lemma vertex_injective (c : RegularJordanCurve) (Q : Partition) :
    Function.Injective (inscribedVertex c Q) := by
  intro i j hij
  have h := c.injective hij
  have he : Q.time i.castSucc = Q.time j.castSucc :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      ⟨(P202.PlaneTurning.partition_time_mem Q _).1, by simpa using partition_time_lt_one Q i⟩
      ⟨(P202.PlaneTurning.partition_time_mem Q _).1, by simpa using partition_time_lt_one Q j⟩).mp h
  exact Fin.ext (congrArg (fun k : Fin (Q.count + 1) => k.val) (Q.strictMono.injective he))

/-- The closing chord ends at parameter 1, the same point as parameter 0. -/
lemma next_vertex (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count) :
    inscribedVertex c Q (finRotate Q.count i) =
      realLift c.parametrization (Q.time i.succ) := by
  have hn : 0 < Q.count := by have := Q.at_least_three; omega
  letI : NeZero Q.count := ⟨ne_of_gt hn⟩
  by_cases hi : i.val + 1 < Q.count
  · have he : (finRotate Q.count i).castSucc = i.succ := by
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod,
        Fin.val_castSucc, Fin.val_succ]
      exact Nat.mod_eq_of_lt hi
    simp only [inscribedVertex, he]
  · have he : i.succ = Fin.last Q.count := Fin.ext (by simp; omega)
    have hr : finRotate Q.count i = 0 := by
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod,
        Fin.val_zero]
      have hi' : i.val + 1 = Q.count := by omega
      rw [hi', Nat.mod_self]
    rw [hr, he, Q.last]
    simp [inscribedVertex, Q.first, realLift, AddCircle.coe_period]

/-- The edge vectors are the literal secants, also at the cyclic endpoint. -/
lemma polygon_edge (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count) :
    P202Specs.PolygonTurning.edgeVector (polygon c Q) i = inscribedEdge c Q i := by
  change inscribedVertex c Q (finRotate Q.count i) - inscribedVertex c Q i = _
  rw [next_vertex]
  rfl

lemma polygon_sum (c : RegularJordanCurve) (Q : Partition)
    (o : Orientation ℝ Plane (Fin 2)) :
    polygonTurning o c Q = P202Specs.PolygonTurning.totalTurning o (polygon c Q) := by
  have he (i : Fin Q.count) : polygonCornerAngle o c Q i =
      P202Specs.PolygonTurning.exteriorAngle o (polygon c Q) (finRotate Q.count i) := by
    simp only [P202Specs.PolygonTurning.exteriorAngle,
      P202Specs.PolygonTurning.incomingVector, Equiv.symm_apply_apply, polygon_edge]
    rfl
  simp only [polygonTurning, he, P202Specs.PolygonTurning.totalTurning]
  exact Equiv.sum_comp (finRotate Q.count) (fun i : Fin Q.count =>
    P202Specs.PolygonTurning.exteriorAngle o (polygon c Q) i)

theorem polygonEdges : Expected.polygonEdges := by
  intro c Q
  exact ⟨polygon_edge c Q, polygon_sum c Q⟩

theorem nonzeroEdges : Expected.nonzeroEdges := by
  intro c Q i hi
  have he := (sub_eq_zero.mp hi).symm
  rw [← next_vertex] at he
  have hinj := vertex_injective c Q he
  have hn : 0 < Q.count := by have := Q.at_least_three; omega
  letI : NeZero Q.count := ⟨ne_of_gt hn⟩
  have hval := congrArg Fin.val hinj
  simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod] at hval
  have hi' := i.isLt
  have hn' := Q.at_least_three
  by_cases hh : i.val + 1 < Q.count
  · rw [Nat.mod_eq_of_lt hh] at hval
    omega
  · have hh' : i.val + 1 = Q.count := by omega
    rw [hh', Nat.mod_self] at hval
    omega

lemma unit_direction_continuous (o : Orientation ℝ Plane (Fin 2))
    {X : Type*} [TopologicalSpace X] (f : C(X, Plane)) (hf : ∀ t, ‖f t‖ = 1) :
    Continuous (fun t => direction o (f t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hn : f t ≠ 0 := by
    intro h
    have hu := hf t
    simp [h] at hu
  exact ContinuousAt.comp (f := fun t => (reference, f t))
    (o.continuousAt_oangle reference_nonzero hn)
    (continuous_const.prodMk f.continuous).continuousAt

lemma loop_lift_exists (o : Orientation ℝ Plane (Fin 2)) (S : UnitDirectionLoop) :
    ∃ L : C(unitInterval, ℝ), ∀ t, (L t : Real.Angle) = direction o (S.map t) := by
  obtain ⟨L, hL, _⟩ := P202.PlaneTurning.radianCovering.exists_path_lifts
    (angleLoop o S).toContinuousMap (direction o (S.map 0)).toReal
    (Real.Angle.coe_toReal _).symm
  exact ⟨L, fun t => congrFun hL t⟩

lemma loop_increment_eq_winding (o : Orientation ℝ Plane (Fin 2))
    (S : UnitDirectionLoop) (L : C(unitInterval, ℝ))
    (hL : ∀ t, (L t : Real.Angle) = direction o (S.map t)) :
    L 1 - L 0 = 2 * Real.pi * (winding o S : ℝ) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hw := AddCircle.windingNumber_eq_div (p := 2 * Real.pi) (angleLoop o S) L
    (funext hL)
  change (winding o S : ℝ) = (L 1 - L 0) / (2 * Real.pi) at hw
  exact ((eq_div_iff (by positivity : (2 * Real.pi : ℝ) ≠ 0)).mp hw).symm.trans
    (mul_comm _ _)

/-- Lift the entire free homotopy. The difference of its endpoint values has
constant image zero in the angle circle, hence is constant on the interval.
This explicitly handles the moving basepoint. -/
theorem homotopyWinding : Expected.homotopyWinding := by
  intro o S T H
  obtain ⟨L, hL⟩ := loop_lift_exists o S
  let F : C(unitInterval × unitInterval, Real.Angle) :=
    ⟨fun z => direction o (H.map z),
      unit_direction_continuous o H.map (fun z => H.unit z.1 z.2)⟩
  have hF : ∀ t, F (0, t) = (L t : Real.Angle) := by
    intro t
    change direction o (H.map (0, t)) = _
    rw [H.at_zero, hL]
  let K := P202.PlaneTurning.radianCovering.liftHomotopy F L hF
  have hK (s t : unitInterval) : (K (s,t) : Real.Angle) = F (s,t) :=
    congrFun (P202.PlaneTurning.radianCovering.liftHomotopy_lifts F L hF) (s,t)
  have hzero (t : unitInterval) : K (0,t) = L t :=
    P202.PlaneTurning.radianCovering.liftHomotopy_zero F L hF t
  let D : C(unitInterval, ℝ) :=
    ⟨fun s => K (s,1) - K (s,0), by fun_prop⟩
  have hD (s : unitInterval) : (D s : Real.Angle) = 0 := by
    change ((K (s,1) - K (s,0) : ℝ) : Real.Angle) = 0
    rw [Real.Angle.coe_sub, hK, hK]
    change direction o (H.map (s,1)) - direction o (H.map (s,0)) = 0
    rw [H.closed, sub_self]
  have hconst := P202.PlaneTurning.radianCovering.const_of_comp D.continuous
    (fun s t => (hD s).trans (hD t).symm) (0 : unitInterval) 1
  let M : C(unitInterval, ℝ) := ⟨fun t => K (1,t), by fun_prop⟩
  have hM (t : unitInterval) : (M t : Real.Angle) = direction o (T.map t) := by
    change (K (1,t) : Real.Angle) = _
    rw [hK]
    change direction o (H.map (1,t)) = _
    rw [H.at_one]
  have he : L 1 - L 0 = M 1 - M 0 := by
    change K (0,1) - K (0,0) = K (1,1) - K (1,0) at hconst
    simpa only [hzero, M, ContinuousMap.coe_mk] using hconst
  have hs := loop_increment_eq_winding o S L hL
  have ht := loop_increment_eq_winding o T M hM
  have hp : 0 < 2 * Real.pi := by positivity
  have hw : (winding o S : ℝ) = (winding o T : ℝ) := by nlinarith
  exact_mod_cast hw

/-- The terminal short rotation arrives at the next genuine edge direction. -/
lemma polygon_corner_end (c : RegularJordanCurve) (Q : Partition)
    (o : Orientation ℝ Plane (Fin 2)) (i : Fin Q.count) :
    o.rotation (polygonCornerAngle o c Q i : ℝ)
      (NormedSpace.normalize (inscribedEdge c Q i)) =
        NormedSpace.normalize (inscribedEdge c Q (finRotate Q.count i)) := by
  have hv := nonzeroEdges c Q i
  have hw := nonzeroEdges c Q (finRotate Q.count i)
  have hangle : o.oangle (NormedSpace.normalize (inscribedEdge c Q i))
      (NormedSpace.normalize (inscribedEdge c Q (finRotate Q.count i))) =
      o.oangle (inscribedEdge c Q i) (inscribedEdge c Q (finRotate Q.count i)) := by
    rw [NormedSpace.normalize, NormedSpace.normalize]
    rw [o.oangle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hv)),
      o.oangle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hw))]
  rw [polygonCornerAngle, Real.Angle.coe_toReal, ← hangle]
  exact (o.rotation_oangle_eq_iff_norm_eq _ _).mpr
    ((NormedSpace.norm_normalize hv).trans (NormedSpace.norm_normalize hw).symm)

/-- Alternating constant edge directions and literal short vertex rotations. -/
def polygonPiece (c : RegularJordanCurve) (Q : Partition)
    (o : Orientation ℝ Plane (Fin 2)) (j : Fin (2 * Q.count)) : C(unitInterval, Plane) :=
  ⟨fun t => o.rotation
    ((if j.val % 2 = 0 then 0 else
      (t : ℝ) * polygonCornerAngle o c Q ⟨j.val / 2, by omega⟩) : ℝ)
    (NormedSpace.normalize (inscribedEdge c Q ⟨j.val / 2, by omega⟩)), by
      split_ifs <;>
        simp only [Orientation.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe] <;>
        fun_prop⟩

lemma polygonPiece_even (c : RegularJordanCurve) (Q : Partition)
    (o : Orientation ℝ Plane (Fin 2)) (i : Fin Q.count) (t : unitInterval) :
    polygonPiece c Q o ⟨2 * i.val, by omega⟩ t =
      NormedSpace.normalize (inscribedEdge c Q i) := by
  simp [polygonPiece, o.rotation_zero, Nat.mul_div_right]

lemma polygonPiece_odd (c : RegularJordanCurve) (Q : Partition)
    (o : Orientation ℝ Plane (Fin 2)) (i : Fin Q.count) (t : unitInterval) :
    polygonPiece c Q o ⟨2 * i.val + 1, by omega⟩ t =
      o.rotation ((t : ℝ) * polygonCornerAngle o c Q i : ℝ)
        (NormedSpace.normalize (inscribedEdge c Q i)) := by
  simp [polygonPiece, Nat.add_div, Nat.mul_div_right]

lemma polygonPiece_join (c : RegularJordanCurve) (Q : Partition)
    (o : Orientation ℝ Plane (Fin 2)) (j k : Fin (2 * Q.count))
    (hjk : j.val + 1 = k.val) : polygonPiece c Q o j 1 = polygonPiece c Q o k 0 := by
  by_cases hj : j.val % 2 = 0
  · let i : Fin Q.count := ⟨j.val / 2, by omega⟩
    have hj' : j = ⟨2 * i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
    have hk' : k = ⟨2 * i.val + 1, by omega⟩ := Fin.ext (by dsimp [i]; omega)
    simp [hj', hk', polygonPiece_even, polygonPiece_odd, o.rotation_zero]
  · let i : Fin Q.count := ⟨j.val / 2, by omega⟩
    let l : Fin Q.count := ⟨k.val / 2, by omega⟩
    have hj' : j = ⟨2 * i.val + 1, by omega⟩ := Fin.ext (by dsimp [i]; omega)
    have hk' : k = ⟨2 * l.val, by omega⟩ := Fin.ext (by dsimp [l]; omega)
    have hrot : finRotate Q.count i = l := by
      have hn : 0 < Q.count := by have := Q.at_least_three; omega
      letI : NeZero Q.count := ⟨ne_of_gt hn⟩
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      rw [Nat.mod_eq_of_lt (by dsimp [i]; omega)]
      dsimp [i, l]
      omega
    simp only [hj', hk', polygonPiece_odd, polygonPiece_even]
    change o.rotation ((1 : ℝ) * polygonCornerAngle o c Q i : ℝ)
      (NormedSpace.normalize (inscribedEdge c Q i)) =
        NormedSpace.normalize (inscribedEdge c Q l)
    rw [one_mul, polygon_corner_end, hrot]

/-- The polygon circuit exists for every strictly increasing partition of the
Jordan curve, before any fine-mesh or simplicity argument is used. -/
theorem polygonCircuits : Expected.polygonCircuits := by
  intro c o Q
  have hn : 0 < Q.count := by have := Q.at_least_three; omega
  have hn2 : 0 < 2 * Q.count := by omega
  obtain ⟨M, hM⟩ := P202.PlaneTurning.glue_uniform_slots (2 * Q.count) hn2
    (polygonPiece c Q o) (polygonPiece_join c Q o)
  have he (i : Fin Q.count) (t : unitInterval) :
      M (uniformSlot (2 * Q.count) hn2 ⟨2 * i.val, by omega⟩ t) =
        NormedSpace.normalize (inscribedEdge c Q i) := by
    rw [hM, polygonPiece_even]
  have hc (i : Fin Q.count) (t : unitInterval) :
      M (uniformSlot (2 * Q.count) hn2 ⟨2 * i.val + 1, by omega⟩ t) =
        o.rotation ((t : ℝ) * polygonCornerAngle o c Q i : ℝ)
          (NormedSpace.normalize (inscribedEdge c Q i)) := by
    rw [hM, polygonPiece_odd]
  have hu (t : unitInterval) : ‖M t‖ = 1 := by
    obtain ⟨⟨j,s⟩, rfl⟩ := P202.PlaneTurning.uniformSlot_surjective (2 * Q.count) hn2 t
    rw [hM]
    change ‖o.rotation _ _‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact NormedSpace.norm_normalize (nonzeroEdges c Q _)
  have hclosed : M 1 = M 0 := by
    let z : Fin Q.count := ⟨0, hn⟩
    let l : Fin Q.count := ⟨Q.count - 1, by omega⟩
    have hl : l.val + 1 = Q.count := by dsimp [l]; omega
    have hlast : uniformSlot (2 * Q.count) hn2 ⟨2 * l.val + 1, by omega⟩ 1 = 1 := by
      apply Subtype.ext
      change ((2 * l.val + 1 : ℕ) + (1 : ℝ)) / ((2 * Q.count : ℕ) : ℝ) = 1
      push_cast
      apply (div_eq_one_iff_eq (by positivity : (2 * (Q.count : ℝ)) ≠ 0)).mpr
      have hl' : (l.val : ℝ) + 1 = Q.count := by exact_mod_cast hl
      linarith
    have hfirst : uniformSlot (2 * Q.count) hn2 ⟨2 * z.val, by omega⟩ 0 = 0 := by
      apply Subtype.ext
      simp [uniformSlot, z]
    have hrot : finRotate Q.count l = z := by
      letI : NeZero Q.count := ⟨ne_of_gt hn⟩
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      change (l.val + 1) % Q.count = 0
      rw [hl, Nat.mod_self]
    rw [← hlast, hc]
    change o.rotation ((1 : ℝ) * polygonCornerAngle o c Q l : ℝ)
      (NormedSpace.normalize (inscribedEdge c Q l)) = M 0
    rw [one_mul, polygon_corner_end, hrot, ← hfirst, he]
  exact ⟨{ map := M, unit := hu, closed := hclosed, on_edge := he, on_corner := hc }⟩

def uniformSlotMap (n : ℕ) (hn : 0 < n) (j : Fin n) : C(unitInterval, unitInterval) :=
  ⟨uniformSlot n hn j, by
    apply Continuous.subtype_mk
    change Continuous (fun t : unitInterval => ((j : ℝ) + t) / n)
    fun_prop⟩

def polygonGrid (Q : Partition) (i : Fin (Q.count + 1)) : unitInterval :=
  ⟨(i : ℝ) / Q.count, by
    have hn : (0 : ℝ) < Q.count := by exact_mod_cast (show 0 < Q.count by have := Q.at_least_three; omega)
    constructor
    · positivity
    · apply (div_le_one hn).mpr
      exact_mod_cast Nat.lt_succ_iff.mp i.isLt⟩

lemma polygonGrid_first (Q : Partition) : polygonGrid Q 0 = 0 := by
  apply Subtype.ext
  simp [polygonGrid]

lemma polygonGrid_last (Q : Partition) : polygonGrid Q (Fin.last Q.count) = 1 := by
  have hn : Q.count ≠ 0 := by have := Q.at_least_three; omega
  apply Subtype.ext
  simp [polygonGrid, hn]

lemma polygonSlot_start (Q : Partition) (i : Fin Q.count) :
    uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val, by omega⟩ 0 = polygonGrid Q i.castSucc := by
  apply Subtype.ext
  dsimp [uniformSlot, polygonGrid]
  push_cast
  ring

lemma polygonSlot_middle (Q : Partition) (i : Fin Q.count) :
    uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val, by omega⟩ 1 =
    uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val + 1, by omega⟩ 0 := by
  apply Subtype.ext
  simp [uniformSlot, Nat.cast_add, Nat.cast_mul]

lemma polygonSlot_end (Q : Partition) (i : Fin Q.count) :
    uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val + 1, by omega⟩ 1 = polygonGrid Q i.succ := by
  apply Subtype.ext
  dsimp [uniformSlot, polygonGrid]
  push_cast
  ring

lemma polygon_edge_increment {c : RegularJordanCurve} {Q : Partition}
    {o : Orientation ℝ Plane (Fin 2)} (P : PolygonCircuit o c Q)
    (L : C(unitInterval, ℝ))
    (hL : ∀ t, (L t : Real.Angle) = direction o (P.map t)) (i : Fin Q.count) :
    L (uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val, by omega⟩ 1) -
    L (uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val, by omega⟩ 0) = 0 := by
  let g : C(unitInterval, ℝ) :=
    ContinuousMap.const _ (direction o (inscribedEdge c Q i)).toReal
  have he := P202.PlaneTurning.angle_increment_eq
    (f := L.comp (uniformSlotMap (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val, by omega⟩)) (g := g) (fun t => by
        change (L (uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega) ⟨2 * i.val, by omega⟩ t) : Real.Angle) =
          (((direction o (inscribedEdge c Q i)).toReal : ℝ) : Real.Angle)
        rw [hL, P.on_edge, Real.Angle.coe_toReal]
        exact P202.PlaneTurning.direction_normalize o (nonzeroEdges c Q i))
  simpa [uniformSlotMap, g] using he

lemma polygon_corner_increment {c : RegularJordanCurve} {Q : Partition}
    {o : Orientation ℝ Plane (Fin 2)} (P : PolygonCircuit o c Q)
    (L : C(unitInterval, ℝ))
    (hL : ∀ t, (L t : Real.Angle) = direction o (P.map t)) (i : Fin Q.count) :
    L (uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val + 1, by omega⟩ 1) -
    L (uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val + 1, by omega⟩ 0) = polygonCornerAngle o c Q i := by
  let g : C(unitInterval, ℝ) :=
    ⟨fun t => (direction o (inscribedEdge c Q i)).toReal +
      (t : ℝ) * polygonCornerAngle o c Q i, by fun_prop⟩
  have he := P202.PlaneTurning.angle_increment_eq
    (f := L.comp (uniformSlotMap (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val + 1, by omega⟩)) (g := g) (fun t => by
        change (L (uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega) ⟨2 * i.val + 1, by omega⟩ t) : Real.Angle) =
          ((direction o (inscribedEdge c Q i)).toReal +
            (t : ℝ) * polygonCornerAngle o c Q i : ℝ)
        rw [hL, P.on_corner, Real.Angle.coe_add, Real.Angle.coe_toReal]
        unfold direction
        rw [o.oangle_rotation_right (x := reference)
          (y := NormedSpace.normalize (inscribedEdge c Q i)) reference_nonzero
          ((NormedSpace.normalize_eq_zero_iff _).not.mpr (nonzeroEdges c Q i))]
        exact congrArg (fun d : Real.Angle => d + ((t : ℝ) * polygonCornerAngle o c Q i : ℝ))
          (P202.PlaneTurning.direction_normalize o (v := inscribedEdge c Q i) (nonzeroEdges c Q i)))
  simpa [uniformSlotMap, g] using he

lemma polygon_increment_eq_total {c : RegularJordanCurve} {Q : Partition}
    {o : Orientation ℝ Plane (Fin 2)} (P : PolygonCircuit o c Q)
    (L : C(unitInterval, ℝ))
    (hL : ∀ t, (L t : Real.Angle) = direction o (P.map t)) :
    P202Specs.PolygonTurning.totalTurning o (polygon c Q) = L 1 - L 0 := by
  let F : Fin (Q.count + 1) → ℝ := fun i => L (polygonGrid Q i)
  have hstep (i : Fin Q.count) : polygonCornerAngle o c Q i = F i.succ - F i.castSucc := by
    have he := polygon_edge_increment P L hL i
    have hc := polygon_corner_increment P L hL i
    rw [polygonSlot_start, polygonSlot_middle] at he
    rw [polygonSlot_end] at hc
    dsimp [F]
    linarith
  rw [← polygon_sum]
  unfold polygonTurning
  simp_rw [hstep]
  rw [Finset.sum_sub_distrib]
  have hs := (Fin.sum_univ_succ F).symm.trans (Fin.sum_univ_castSucc F)
  have htel : (∑ i : Fin Q.count, F i.succ) - (∑ i : Fin Q.count, F i.castSucc) =
      F (Fin.last Q.count) - F 0 := by linarith
  simpa [F, polygonGrid_first, polygonGrid_last] using htel

/-- Constant edge slots and short corner slots give the literal polygon sum,
with no orientation or convexity restriction and no choice of initial angle. -/
theorem polygonWinding : Expected.polygonWinding := by
  intro c o Q P
  exact ⟨loop_lift_exists o P.toUnitDirectionLoop,
    fun L hL => ⟨polygon_increment_eq_total P L hL,
      loop_increment_eq_winding o P.toUnitDirectionLoop L hL⟩⟩

/-- Once the analytic homotopy has been constructed, the exact turning
comparison follows for all independent angle choices without a basepoint
assumption. -/
lemma turning_eq_of_unit_homotopy {c : RegularJordanCurve} {Q : Partition}
    {o : Orientation ℝ Plane (Fin 2)} {A : ArcPresentation c}
    (T : TangentCircuit o A) (P : PolygonCircuit o c Q)
    (H : UnitDirectionHomotopy T.toUnitLoop P.toUnitDirectionLoop)
    (θ : AngleChoices o A) :
    totalTurning θ = P202Specs.PolygonTurning.totalTurning o (polygon c Q) := by
  obtain ⟨L, hL⟩ := P202.PlaneTurning.circuit_lift_exists T
  obtain ⟨M, hM⟩ := loop_lift_exists o P.toUnitDirectionLoop
  have he := homotopyWinding o T.toUnitLoop P.toUnitDirectionLoop H
  change T.winding = winding o P.toUnitDirectionLoop at he
  rw [P202.PlaneTurning.circuit_increment_eq_total T θ L hL,
    P202.PlaneTurning.circuit_increment_eq_winding T L hL,
    polygon_increment_eq_total P M hM,
    loop_increment_eq_winding o P.toUnitDirectionLoop M hM, he]

/-- A smooth arc's literal secant is the integral of its actual velocity. -/
lemma chord_eq_integral {c : RegularJordanCurve} (A : ArcPresentation c)
    (i : Fin A.count) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) :
    A.arc i b - A.arc i a = ∫ t in a..b, velocity A i t := by
  obtain ⟨δ, hδ, hs⟩ := A.smooth i
  have hsub : uIcc a b ⊆ Ioo (-δ) (1 + δ) := by
    rw [uIcc_of_le hab]
    intro t ht
    constructor <;> linarith [ht.1, ht.2, ha.1, hb.2]
  have hd := hs.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  symm
  apply intervalIntegral.integral_deriv_eq_sub
  · intro t ht
    exact ((hs.contDiffAt (isOpen_Ioo.mem_nhds (hsub ht))).differentiableAt (by simp))
  · exact (hd.mono hsub).intervalIntegrable

/-- The velocity variation controls the error of the actual directed chord.
This estimate uses the vector integral, not a mean-value theorem for vectors. -/
lemma chord_error_le {c : RegularJordanCurve} (A : ArcPresentation c)
    (i : Fin A.count) {a b ε : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) (v : Plane)
    (hε : ∀ t ∈ Icc a b, ‖velocity A i t - v‖ ≤ ε) :
    ‖A.arc i b - A.arc i a - (b - a) • v‖ ≤ ε * (b - a) := by
  obtain ⟨δ, hδ, hs⟩ := A.smooth i
  have hsub : uIcc a b ⊆ Ioo (-δ) (1 + δ) := by
    rw [uIcc_of_le hab]
    intro t ht
    constructor <;> linarith [ht.1, ht.2, ha.1, hb.2]
  have hd := hs.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  have hint : IntervalIntegrable (velocity A i) MeasureTheory.volume a b :=
    (hd.mono hsub).intervalIntegrable
  have he : A.arc i b - A.arc i a - (b-a) • v =
      ∫ t in a..b, velocity A i t - v := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, ← chord_eq_integral A i ha hb hab]
  rw [he]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun t => velocity A i t - v) (fun t ht => by
      rw [uIoc_of_le hab] at ht
      exact hε t ⟨ht.1.le, ht.2⟩)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh

/-- Dividing a positive-length chord by its parameter length gives an
average velocity within the same error bound. -/
lemma average_chord_error_le {c : RegularJordanCurve} (A : ArcPresentation c)
    (i : Fin A.count) {a b ε : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b) (v : Plane)
    (hε : ∀ t ∈ Icc a b, ‖velocity A i t - v‖ ≤ ε) :
    ‖(b-a)⁻¹ • (A.arc i b - A.arc i a) - v‖ ≤ ε := by
  have hp : 0 < b-a := sub_pos.mpr hab
  have he : (b-a)⁻¹ • (A.arc i b - A.arc i a) - v =
      (b-a)⁻¹ • (A.arc i b - A.arc i a - (b-a) • v) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  calc
    (b-a)⁻¹ * ‖A.arc i b - A.arc i a - (b-a) • v‖ ≤
        (b-a)⁻¹ * (ε * (b-a)) :=
      mul_le_mul_of_nonneg_left (chord_error_le A i ha hb hab.le v hε) (inv_nonneg.mpr hp.le)
    _ = ε := by field_simp

/-- Quantitative continuity of direction away from zero. -/
lemma normalize_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * ‖x-y‖ / ‖y‖ := by
  have hp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  apply (le_div_iff₀ hp).mpr
  rw [mul_comm]
  have he : (‖y‖-‖x‖) • NormedSpace.normalize x + (x-y) =
      ‖y‖ • (NormedSpace.normalize x - NormedSpace.normalize y) := by
    rw [sub_smul, smul_sub, NormedSpace.norm_smul_normalize,
      NormedSpace.norm_smul_normalize]
    abel
  calc
    ‖y‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ =
        ‖(‖y‖-‖x‖) • NormedSpace.normalize x + (x-y)‖ := by
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
    _ ≤ ‖(‖y‖-‖x‖) • NormedSpace.normalize x‖ + ‖x-y‖ := norm_add_le _ _
    _ = |‖y‖-‖x‖| + ‖x-y‖ := by
      rw [norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hx, mul_one]
    _ ≤ 2 * ‖x-y‖ := by
      have hh := abs_norm_sub_norm_le y x
      rw [norm_sub_rev y x] at hh
      linarith

/-- Uniform secant-direction approximation on an actual closed smooth arc.
The endpoints may move independently, and every tangent on the small subarc
is covered by the same threshold. -/
lemma small_chord_directions {c : RegularJordanCurve} (A : ArcPresentation c)
    (i : Fin A.count) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ a b : ℝ,
      a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → a < b → b-a < η →
      ∀ t ∈ Icc a b,
        ‖NormedSpace.normalize (A.arc i b - A.arc i a) -
          NormedSpace.normalize (velocity A i t)‖ < ε := by
  obtain ⟨δ, hδ, hs⟩ := A.smooth i
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-δ) (1+δ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hcont : ContinuousOn (velocity A i) (Icc (0 : ℝ) 1) :=
    (hs.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).mono hsub
  obtain ⟨m, hm, hmn⟩ := isCompact_Icc.exists_forall_le' hcont.norm
    (fun t ht => norm_pos_iff.mpr (A.regular i t ht))
  let ζ := min (ε * m / 4) (m / 2)
  have hζ : 0 < ζ := lt_min (by positivity) (by positivity)
  obtain ⟨η, hη, hηv⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont) ζ hζ
  refine ⟨η, hη, ?_⟩
  intro a b ha hb hab hmesh t ht
  have htg : t ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
  have hvar (s : ℝ) (hs : s ∈ Icc a b) : ‖velocity A i s - velocity A i t‖ ≤ ζ := by
    apply le_of_lt
    apply hηv s ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩ t htg
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
  let w := (b-a)⁻¹ • (A.arc i b - A.arc i a)
  have hw : ‖w - velocity A i t‖ ≤ ζ := average_chord_error_le A i ha hb hab _ hvar
  have hzn : ζ ≤ m/2 := min_le_right _ _
  have hze : ζ ≤ ε*m/4 := min_le_left _ _
  have hvt : m ≤ ‖velocity A i t‖ := hmn t htg
  have hw0 : w ≠ 0 := by
    intro he
    rw [he, zero_sub, norm_neg] at hw
    linarith
  have hdir := normalize_sub_le hw0 (A.regular i t htg)
  have hpos : 0 < ‖velocity A i t‖ := norm_pos_iff.mpr (A.regular i t htg)
  have hsmall : 2 * ‖w - velocity A i t‖ < ε * ‖velocity A i t‖ := by
    nlinarith
  have hfinal := lt_of_le_of_lt hdir ((div_lt_iff₀ hpos).mpr hsmall)
  change ‖NormedSpace.normalize ((b-a)⁻¹ • (A.arc i b - A.arc i a)) -
    NormedSpace.normalize (velocity A i t)‖ < ε at hfinal
  rw [NormedSpace.normalize_smul_of_pos (inv_pos.mpr (sub_pos.mpr hab))] at hfinal
  exact hfinal

/-- One threshold works simultaneously for all finitely many original arcs. -/
lemma all_small_chord_directions {c : RegularJordanCurve} (A : ArcPresentation c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (i : Fin A.count) (a b : ℝ),
      a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → a < b → b-a < η →
      ∀ t ∈ Icc a b,
        ‖NormedSpace.normalize (A.arc i b - A.arc i a) -
          NormedSpace.normalize (velocity A i t)‖ < ε := by
  choose η hη hprop using fun i : Fin A.count => small_chord_directions A i ε hε
  have hne : (Finset.univ : Finset (Fin A.count)).Nonempty :=
    ⟨⟨0, A.positive⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne η, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff hne).mpr (fun i _ => hη i)
  · intro i a b ha hb hab hmesh t ht
    exact hprop i a b ha hb hab
      (lt_of_lt_of_le hmesh (Finset.inf'_le η (Finset.mem_univ i))) t ht

lemma rotation_direction_eq (o : Orientation ℝ Plane (Fin 2))
    {v : Plane} (hv : ‖v‖ = 1) :
    o.rotation (direction o v) (NormedSpace.normalize reference) = v := by
  have hangle : o.oangle (NormedSpace.normalize reference) v = direction o v := by
    exact o.oangle_smul_left_of_pos reference v (inv_pos.mpr (norm_pos_iff.mpr reference_nonzero))
  rw [← hangle]
  exact (o.rotation_oangle_eq_iff_norm_eq _ _).mpr
    ((NormedSpace.norm_normalize reference_nonzero).trans hv.symm)

/-- Equality of actual circle winding constructs a free homotopy through unit
loops by interpolation of real lifts with the same endpoint displacement.
The lift starting values are independent. -/
lemma unit_homotopy_of_winding_eq (o : Orientation ℝ Plane (Fin 2))
    (S T : UnitDirectionLoop) (he : winding o S = winding o T) :
    Nonempty (UnitDirectionHomotopy S T) := by
  obtain ⟨L, hL⟩ := loop_lift_exists o S
  obtain ⟨M, hM⟩ := loop_lift_exists o T
  have hdiff : L 1 - L 0 = M 1 - M 0 := by
    rw [loop_increment_eq_winding o S L hL, loop_increment_eq_winding o T M hM, he]
  let phase (s t : unitInterval) : ℝ := (1-s)*L t + s*M t
  let F : C(unitInterval × unitInterval, Plane) :=
    ⟨fun z => o.rotation (phase z.1 z.2 : ℝ) (NormedSpace.normalize reference), by
      simp only [Orientation.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
      dsimp [phase]
      fun_prop⟩
  refine ⟨⟨F, ?_, ?_, ?_, ?_⟩⟩
  · intro s t
    change ‖o.rotation _ _‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact NormedSpace.norm_normalize reference_nonzero
  · intro t
    change o.rotation (phase 0 t : ℝ) _ = S.map t
    have hp : phase 0 t = L t := by simp [phase]
    rw [hp, hL]
    exact rotation_direction_eq o (S.unit t)
  · intro t
    change o.rotation (phase 1 t : ℝ) _ = T.map t
    have hp : phase 1 t = M t := by simp [phase]
    rw [hp, hM]
    exact rotation_direction_eq o (T.unit t)
  · intro s
    change o.rotation (phase s 1 : ℝ) _ = o.rotation (phase s 0 : ℝ) _
    have hphase : phase s 1 = phase s 0 + (L 1 - L 0) := by
      dsimp [phase]
      linear_combination -(s : ℝ) * hdiff
    have hz : ((L 1 - L 0 : ℝ) : Real.Angle) = 0 := by
      rw [Real.Angle.coe_sub, hL, hL, S.closed, sub_self]
    rw [hphase, Real.Angle.coe_add, hz, add_zero]

lemma unit_homotopy_iff_winding (o : Orientation ℝ Plane (Fin 2))
    (S T : UnitDirectionLoop) :
    Nonempty (UnitDirectionHomotopy S T) ↔ winding o S = winding o T :=
  ⟨fun ⟨H⟩ => homotopyWinding o S T H, unit_homotopy_of_winding_eq o S T⟩

theorem homotopyClassification : Expected.homotopyClassification :=
  unit_homotopy_iff_winding

theorem smallChordDirections : Expected.smallChordDirections := by
  intro c A ε hε
  exact all_small_chord_directions A ε hε


lemma angle_toReal_continuousAt {θ : Real.Angle} (hθ : θ ≠ (Real.pi : Real.Angle)) :
    ContinuousAt Real.Angle.toReal θ := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hne : θ ≠ ((-Real.pi : ℝ) : AddCircle (2 * Real.pi)) := by
    change θ ≠ ((-Real.pi : ℝ) : Real.Angle)
    rw [Real.Angle.coe_neg, Real.Angle.neg_coe_pi]
    exact hθ
  have hc := continuous_subtype_val.continuousAt.comp
    (AddCircle.continuousAt_equivIoc (p := 2 * Real.pi) (a := -Real.pi) hne)
  exact hc

lemma short_angle_continuousAt (o : Orientation ℝ Plane (Fin 2))
    {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0)
    (ha : o.oangle u v ≠ (Real.pi : Real.Angle)) :
    ContinuousAt (fun z : Plane × Plane => (o.oangle z.1 z.2).toReal) (u,v) := by
  have hc : ContinuousAt (fun z : Plane × Plane => o.oangle z.1 z.2) (u,v) :=
    o.continuousAt_oangle hu hv
  exact ContinuousAt.comp (f := fun z : Plane × Plane => o.oangle z.1 z.2)
    (angle_toReal_continuousAt ha) hc

lemma corner_stability {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (i : Fin A.count) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ u v : Plane,
      ‖u - NormedSpace.normalize (velocity A i 1)‖ < η →
      ‖v - NormedSpace.normalize (velocity A (finRotate A.count i) 0)‖ < η →
      -Real.pi < (o.oangle u v).toReal ∧ (o.oangle u v).toReal < Real.pi ∧
      |(o.oangle u v).toReal - cornerAngle o A i| < ε := by
  let u0 := NormedSpace.normalize (velocity A i 1)
  let v0 := NormedSpace.normalize (velocity A (finRotate A.count i) 0)
  have hu : velocity A i 1 ≠ 0 := A.regular i 1 (by simp)
  have hv : velocity A (finRotate A.count i) 0 ≠ 0 := A.regular (finRotate A.count i) 0 (by simp)
  have hangle : o.oangle u0 v0 = o.oangle (velocity A i 1) (velocity A (finRotate A.count i) 0) := by
    dsimp [u0,v0, NormedSpace.normalize]
    rw [o.oangle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hu)),
      o.oangle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hv))]
  have hc := short_angle_continuousAt o
    ((NormedSpace.normalize_eq_zero_iff _).not.mpr hu)
    ((NormedSpace.normalize_eq_zero_iff _).not.mpr hv)
    (by rw [hangle]; exact P202.PlaneTurning.corner_not_pi o A i)
  have hb := (P202.PlaneTurning.cornerBounds c o A i).2
  let κ := min ε ((Real.pi - cornerAngle o A i) / 2)
  have hκ : 0 < κ := lt_min hε (by positivity)
  obtain ⟨η,hη,hηa⟩ := Metric.continuousAt_iff.mp hc κ hκ
  refine ⟨η,hη, ?_⟩
  intro u v huu hvv
  have hd : dist (u,v) (u0,v0) < η := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨huu,hvv⟩
  have he := hηa hd
  have he' : |(o.oangle u v).toReal - cornerAngle o A i| < κ := by
    change |(o.oangle u v).toReal - (o.oangle u0 v0).toReal| < κ at he
    rw [hangle] at he
    exact he
  refine ⟨Real.Angle.neg_pi_lt_toReal _, ?_, he'.trans_le (min_le_left _ _)⟩
  have he'' := (abs_lt.mp he').2
  have hk := min_le_right ε ((Real.pi - cornerAngle o A i) / 2)
  dsimp [κ] at he''
  linarith



lemma presentation_interval {c : RegularJordanCurve} (A : ArcPresentation c)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∃ i : Fin A.count, A.time i.castSucc ≤ x ∧ x < A.time i.succ := by
  let S := Finset.univ.filter (fun j : Fin (A.count+1) => A.time j ≤ x)
  have hz : (0 : Fin (A.count+1)) ∈ S := by simp [S, A.first, hx0]
  let k := S.max' ⟨0,hz⟩
  have hk : k ∈ S := Finset.max'_mem _ _
  have hk0 : A.time k ≤ x := (Finset.mem_filter.mp hk).2
  have hkn : k.val < A.count := by
    by_contra! hh
    have he : k = Fin.last A.count := Fin.ext (by simp; omega)
    rw [he,A.last] at hk0
    linarith
  let i : Fin A.count := ⟨k.val,hkn⟩
  have hi : i.castSucc = k := Fin.ext rfl
  refine ⟨i, by simpa [hi] using hk0, ?_⟩
  by_contra! hh
  have his : i.succ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
  have hle : i.succ ≤ k := Finset.le_max' S i.succ his
  have hval := (show i.val+1 ≤ k.val from hle)
  dsimp [i] at hval
  omega

lemma refining_edge_interval {c : RegularJordanCurve} (A : ArcPresentation c)
    (Q : Partition) (hQ : Q.Refines A) (j : Fin Q.count) :
    ∃ i : Fin A.count,
      A.time i.castSucc ≤ Q.time j.castSucc ∧ Q.time j.succ ≤ A.time i.succ := by
  obtain ⟨i,hi0,hi1⟩ := presentation_interval A
    (P202.PlaneTurning.partition_time_mem Q _).1 (partition_time_lt_one Q j)
  refine ⟨i,hi0, ?_⟩
  by_contra! hh
  obtain ⟨k,hk⟩ := hQ i.succ
  exact P202.PlaneTurning.partition_no_between Q j k (by rw [hk]; exact ⟨hi1,hh⟩)

/-- Every literal edge in a knot-preserving refinement lies entirely in one
original smooth arc, with positive affine local parameters. -/
lemma refining_edge_coordinates {c : RegularJordanCurve} (A : ArcPresentation c)
    (Q : Partition) (hQ : Q.Refines A) (j : Fin Q.count) :
    ∃ (i : Fin A.count) (a b : ℝ),
      a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a < b ∧
      Q.time j.castSucc = A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*a ∧
      Q.time j.succ = A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*b ∧
      inscribedEdge c Q j = A.arc i b - A.arc i a := by
  obtain ⟨i,hi0,hi1⟩ := refining_edge_interval A Q hQ j
  have hd : 0 < A.time i.succ - A.time i.castSucc :=
    sub_pos.mpr (A.strictMono (by simp))
  have hj : Q.time j.castSucc < Q.time j.succ := Q.strictMono (by simp)
  let a := (Q.time j.castSucc - A.time i.castSucc) / (A.time i.succ-A.time i.castSucc)
  let b := (Q.time j.succ - A.time i.castSucc) / (A.time i.succ-A.time i.castSucc)
  have ha : a ∈ Icc (0 : ℝ) 1 := by
    dsimp [a]
    constructor
    · exact div_nonneg (sub_nonneg.mpr hi0) hd.le
    · exact (div_le_one hd).mpr (by linarith)
  have hb : b ∈ Icc (0 : ℝ) 1 := by
    dsimp [b]
    constructor
    · exact div_nonneg (by linarith) hd.le
    · exact (div_le_one hd).mpr (by linarith)
  have hab : a < b := by dsimp [a,b]; exact (div_lt_div_iff_of_pos_right hd).mpr (by linarith)
  have hsa : Q.time j.castSucc = A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*a := by
    dsimp [a]
    field_simp
    ring
  have hsb : Q.time j.succ = A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*b := by
    dsimp [b]
    field_simp
    ring
  refine ⟨i,a,b,ha,hb,hab,hsa,hsb, ?_⟩
  rw [A.agrees i b hb, A.agrees i a ha, ← hsa, ← hsb]
  rfl

/-- A global mesh threshold controls all literal chords of every refining
partition, including very uneven refinements. Affine arc speeds are accounted
for by the positive minimum of the original parameter interval lengths. -/
lemma refined_chord_directions {c : RegularJordanCurve} (A : ArcPresentation c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.Refines A → Q.MeshLT δ →
      ∀ j : Fin Q.count, ∃ (i : Fin A.count) (a b : ℝ),
        a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a < b ∧
        Q.time j.castSucc = A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*a ∧
        Q.time j.succ = A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*b ∧
        ∀ t ∈ Icc a b,
          ‖NormedSpace.normalize (inscribedEdge c Q j) -
            NormedSpace.normalize (velocity A i t)‖ < ε := by
  obtain ⟨η,hη,hdir⟩ := all_small_chord_directions A ε hε
  let d : Fin A.count → ℝ := fun i => A.time i.succ - A.time i.castSucc
  have hd (i : Fin A.count) : 0 < d i := sub_pos.mpr (A.strictMono (by simp))
  have hne : (Finset.univ : Finset (Fin A.count)).Nonempty :=
    ⟨⟨0,A.positive⟩, Finset.mem_univ _⟩
  let m := Finset.univ.inf' hne d
  have hm : 0 < m := (Finset.lt_inf'_iff hne).mpr (fun i _ => hd i)
  refine ⟨η*m, mul_pos hη hm, ?_⟩
  intro Q hQ hmesh j
  obtain ⟨i,a,b,ha,hb,hab,hsa,hsb,he⟩ := refining_edge_coordinates A Q hQ j
  refine ⟨i,a,b,ha,hb,hab,hsa,hsb, ?_⟩
  have hgap : Q.time j.succ - Q.time j.castSucc = d i * (b-a) := by
    dsimp [d]
    rw [hsa,hsb]
    ring
  have hdm : m ≤ d i := Finset.inf'_le d (Finset.mem_univ i)
  have hsmall : b-a < η := by
    have hh := hmesh j
    rw [hgap] at hh
    have hdi := hd i
    nlinarith
  intro t ht
  rw [he]
  exact hdir i a b ha hb hab hsmall t ht


theorem cornerStability : Expected.cornerStability := by
  intro c o A i ε hε
  exact corner_stability o A i ε hε

theorem refiningEdges : Expected.refiningEdges := by
  intro c A Q hQ j
  exact refining_edge_coordinates A Q hQ j

theorem refinedChordDirections : Expected.refinedChordDirections := by
  intro c A ε hε
  exact refined_chord_directions A ε hε


lemma positive_projection_nonopposite {u v a : Plane}
    (hu : 0 < inner ℝ a u) (hv : 0 < inner ℝ a v) :
    NormedSpace.normalize u ≠ -NormedSpace.normalize v := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hu' : 0 < inner ℝ a (NormedSpace.normalize u) := by
    rw [NormedSpace.normalize, real_inner_smul_right]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hu0)) hu
  have hv' : 0 < inner ℝ a (NormedSpace.normalize v) := by
    rw [NormedSpace.normalize, real_inner_smul_right]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hv0)) hv
  intro h
  rw [h, inner_neg_right] at hu'
  linarith

/-- Compactness makes the existing strict graph projections uniform over a
whole period. The projections themselves may vary with the central point. -/
lemma uniform_parameter_projection (c : RegularJordanCurve) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ a : Plane, StrictMonoOn (fun s => inner ℝ a (realLift c.parametrization s))
        (Metric.ball t δ) := by
  choose ε a hε ha hm using P202.PlanarRegionTopology.cornerProjection c
  let U (t : ℝ) := Ioo (t-ε t) (t+ε t)
  have hcover : Icc (0 : ℝ) 1 ⊆ ⋃ t, U t := by
    intro t ht
    exact mem_iUnion.mpr ⟨t, by dsimp [U]; constructor <;> linarith [hε t]⟩
  obtain ⟨δ,hδ,hδU⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun t => isOpen_Ioo : ∀ t, IsOpen (U t)) hcover
  refine ⟨δ,hδ, ?_⟩
  intro t ht
  obtain ⟨s,hs⟩ := hδU t ht
  exact ⟨a s,(hm s).mono (fun x hx => Ioo_subset_Icc_self (hs hx))⟩

lemma next_time_shift (Q : Partition) (i : Fin Q.count) :
    Q.time i.succ = Q.time (finRotate Q.count i).castSucc +
      (if i.val+1 < Q.count then (0 : ℝ) else 1) := by
  have hn : 0 < Q.count := by have := Q.at_least_three; omega
  letI : NeZero Q.count := ⟨ne_of_gt hn⟩
  by_cases hi : i.val+1 < Q.count
  · have he : (finRotate Q.count i).castSucc = i.succ := by
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod,
        Fin.val_castSucc, Fin.val_succ]
      exact Nat.mod_eq_of_lt hi
    simp only [if_pos hi, add_zero, he]
  · have he : i.succ = Fin.last Q.count := Fin.ext (by simp; omega)
    have hr : finRotate Q.count i = 0 := by
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod, Fin.val_zero]
      have hi' : i.val+1 = Q.count := by omega
      rw [hi',Nat.mod_self]
    simp [hi,he,hr,Q.last,Q.first]

/-- No cusp can appear in any sufficiently fine inscribed polygon. This
uses local strictly increasing projections across original noncuspidal joins;
it does not require knot preservation or positive boundary orientation. -/
lemma fine_polygon_noncuspidal (c : RegularJordanCurve) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
      P202Specs.PolygonTurning.Noncuspidal (P202Specs.PlaneTangentComparison.polygon c Q) := by
  obtain ⟨δ,hδ,hproj⟩ := uniform_parameter_projection c
  refine ⟨δ,hδ, ?_⟩
  intro Q hmesh j
  let i := (finRotate Q.count).symm j
  have hj : finRotate Q.count i = j := Equiv.apply_symm_apply _ _
  let x := Q.time i.castSucc
  let y := Q.time i.succ
  let k : ℝ := if i.val+1 < Q.count then 0 else 1
  let z := Q.time j.succ + k
  have hxy : x < y := Q.strictMono (by simp)
  have hy : y = Q.time j.castSucc + k := by simpa only [hj] using next_time_shift Q i
  have hyz : y < z := by
    have hh : Q.time j.castSucc < Q.time j.succ := Q.strictMono (by simp)
    dsimp [z]
    linarith
  have hxball : x ∈ Metric.ball y δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hxy)]
    have hh := hmesh i
    dsimp [x,y] at *
    linarith
  have hyball : y ∈ Metric.ball y δ := Metric.mem_ball_self hδ
  have hzball : z ∈ Metric.ball y δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hyz)]
    have hh := hmesh j
    dsimp [z]
    linarith
  obtain ⟨a,ha⟩ := hproj y (P202.PlaneTurning.partition_time_mem Q _)
  have hpos1 : 0 < inner ℝ a (inscribedEdge c Q i) := by
    change 0 < inner ℝ a (realLift c.parametrization y - realLift c.parametrization x)
    rw [inner_sub_right]
    exact sub_pos.mpr (ha hxball hyball hxy)
  have hzcurve : realLift c.parametrization z = realLift c.parametrization (Q.time j.succ) := by
    dsimp [z,k]
    split_ifs <;> simp [realLift, AddCircle.coe_add, AddCircle.coe_period]
  have hycurve : realLift c.parametrization y = inscribedVertex c Q j := by
    simpa only [hj] using (next_vertex c Q i).symm
  have hpos2 : 0 < inner ℝ a (inscribedEdge c Q j) := by
    change 0 < inner ℝ a (realLift c.parametrization (Q.time j.succ) - inscribedVertex c Q j)
    rw [← hzcurve, ← hycurve, inner_sub_right]
    exact sub_pos.mpr (ha hyball hzball hyz)
  change NormedSpace.normalize (P202Specs.PolygonTurning.edgeVector
      (P202Specs.PlaneTangentComparison.polygon c Q) i) ≠
    -NormedSpace.normalize (P202Specs.PolygonTurning.edgeVector
      (P202Specs.PlaneTangentComparison.polygon c Q) j)
  rw [polygon_edge,polygon_edge]
  exact positive_projection_nonopposite hpos1 hpos2


theorem fineNoncuspidal : Expected.fineNoncuspidal := fine_polygon_noncuspidal


/-- A scalar turning equality already constructs the required unit-circle
homotopy, using arbitrary real lifts and no fixed-basepoint assumption. -/
lemma unit_homotopy_of_turning_eq {c : RegularJordanCurve} {Q : Partition}
    {o : Orientation ℝ Plane (Fin 2)} {A : ArcPresentation c}
    (T : TangentCircuit o A) (P : PolygonCircuit o c Q) (θ : AngleChoices o A)
    (he : totalTurning θ = P202Specs.PolygonTurning.totalTurning o (polygon c Q)) :
    Nonempty (UnitDirectionHomotopy T.toUnitLoop P.toUnitDirectionLoop) := by
  obtain ⟨L,hL⟩ := P202.PlaneTurning.circuit_lift_exists T
  obtain ⟨M,hM⟩ := loop_lift_exists o P.toUnitDirectionLoop
  rw [P202.PlaneTurning.circuit_increment_eq_total T θ L hL,
    P202.PlaneTurning.circuit_increment_eq_winding T L hL,
    polygon_increment_eq_total P M hM,
    loop_increment_eq_winding o P.toUnitDirectionLoop M hM] at he
  have hp : 0 < 2 * Real.pi := by positivity
  have hw : T.winding = winding o P.toUnitDirectionLoop := by
    have hh : (T.winding : ℝ) = (winding o P.toUnitDirectionLoop : ℝ) := by nlinarith
    exact_mod_cast hh
  exact unit_homotopy_of_winding_eq o T.toUnitLoop P.toUnitDirectionLoop hw

/-- Assemble the scalar comparison into actual polygon circuits, unit-circle
homotopies, and the equality of their genuine winding numbers. -/
lemma comparison_of_uniformTurningEquality
    (h : Expected.uniformTurningEquality) : Expected.comparison := by
  intro c o A
  obtain ⟨δ,hδ,heq⟩ := h c o A
  obtain ⟨η,hη,hn⟩ := fineNoncuspidal c
  refine ⟨min δ η,lt_min hδ hη, ?_⟩
  intro Q hQ hmesh
  have hmeshδ : Q.MeshLT δ := fun i => (hmesh i).trans_le (min_le_left _ _)
  have hmeshη : Q.MeshLT η := fun i => (hmesh i).trans_le (min_le_right _ _)
  obtain ⟨P⟩ := polygonCircuits c o Q
  obtain ⟨θ⟩ := P202.PlaneTurning.choicesExist c o A
  refine ⟨hn Q hmeshη,P, ?_,heq Q hQ hmeshδ⟩
  intro T
  obtain ⟨H⟩ := unit_homotopy_of_turning_eq T P θ (heq Q hQ hmeshδ θ)
  exact ⟨⟨H⟩,homotopyWinding o T.toUnitLoop P.toUnitDirectionLoop H⟩



lemma uniform_short_angle_small (o : Orientation ℝ Plane (Fin 2))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ u v : Plane, ‖u‖ = 1 → ‖v‖ = 1 →
      ‖u-v‖ < η → |(o.oangle u v).toReal| < ε := by
  let a : Plane := NormedSpace.normalize reference
  have ha : ‖a‖ = 1 := NormedSpace.norm_normalize reference_nonzero
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hc := short_angle_continuousAt o ha0 ha0
    (by simpa only [o.oangle_self] using (Ne.symm Real.Angle.pi_ne_zero))
  obtain ⟨η, hη, hηa⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨η, hη, ?_⟩
  intro u v hu hv huv
  let R := o.rotation (o.oangle u a)
  have hRu : R u = a := (o.rotation_oangle_eq_iff_norm_eq u a).mpr (hu.trans ha.symm)
  have hd : dist (R u,R v) (a,a) < η := by
    rw [Prod.dist_eq, hRu, dist_self, max_eq_right (dist_nonneg)]
    rw [← hRu, R.dist_map, dist_eq_norm]
    simpa only [norm_sub_rev] using huv
  have hh := hηa hd
  simpa only [R, o.oangle_rotation, o.oangle_self, Real.Angle.toReal_zero, sub_zero,
    Real.dist_eq] using hh

lemma corrected_angle_lifts (o : Orientation ℝ Plane (Fin 2))
    {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) {r : ℝ}
    (hr : (r : Real.Angle) = direction o u) :
    ((r + (o.oangle u v).toReal : ℝ) : Real.Angle) = direction o v := by
  rw [Real.Angle.coe_add, hr, Real.Angle.coe_toReal]
  exact o.oangle_add reference_nonzero hu hv

lemma short_angle_eq_lift_difference (o : Orientation ℝ Plane (Fin 2))
    {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) {r s : ℝ}
    (hr : (r : Real.Angle) = direction o u)
    (hs : (s : Real.Angle) = direction o v)
    (hlo : -Real.pi < s-r) (hhi : s-r ≤ Real.pi) :
    (o.oangle u v).toReal = s-r := by
  have he : ((s-r : ℝ) : Real.Angle) = o.oangle u v := by
    rw [Real.Angle.coe_sub, hs, hr]
    exact o.oangle_sub_left reference_nonzero hu hv
  rw [← he]
  exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hlo,hhi⟩

lemma fixed_direction_correction_constant {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (o : Orientation ℝ Plane (Fin 2))
    (U : C(X, Plane)) (f : C(X, ℝ)) (v : Plane)
    (hU : ∀ t, U t ≠ 0) (hv : v ≠ 0)
    (hf : ∀ t, (f t : Real.Angle) = direction o (U t))
    (hbranch : ∀ t, o.oangle (U t) v ≠ (Real.pi : Real.Angle)) :
    ∀ s t, f s + (o.oangle (U s) v).toReal =
      f t + (o.oangle (U t) v).toReal := by
  have hδ : Continuous (fun t => (o.oangle (U t) v).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp (f := fun s : X => (U s, v))
      (short_angle_continuousAt o (hU t) hv (hbranch t))
      (U.continuous.continuousAt.prodMk continuousAt_const)
  have hc : Continuous (fun t => f t + (o.oangle (U t) v).toReal) :=
    f.continuous.add hδ
  apply (AddCircle.isCoveringMap_coe (2 * Real.pi)).const_of_comp hc
  intro s t
  exact (corrected_angle_lifts o (hU s) hv (hf s)).trans
    (corrected_angle_lifts o (hU t) hv (hf t)).symm

lemma fixed_direction_correction_interval (o : Orientation ℝ Plane (Fin 2))
    (U : C(unitInterval, Plane)) (f : C(unitInterval, ℝ)) (v : Plane)
    (hU : ∀ t, U t ≠ 0) (hv : v ≠ 0)
    (hf : ∀ t, (f t : Real.Angle) = direction o (U t))
    (a b : unitInterval) (hab : a ≤ b)
    (hbranch : ∀ t ∈ Icc a b, o.oangle (U t) v ≠ (Real.pi : Real.Angle)) :
    f b + (o.oangle (U b) v).toReal =
      f a + (o.oangle (U a) v).toReal := by
  letI : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  let R : C(Icc a b, unitInterval) := ⟨Subtype.val, continuous_subtype_val⟩
  exact fixed_direction_correction_constant o (U.comp R) (f.comp R) v
    (fun t => hU t) hv (fun t => hf t) (fun t => hbranch t t.property)
    ⟨b,⟨hab,le_rfl⟩⟩ ⟨a,⟨le_rfl,hab⟩⟩

lemma finite_corner_margin {c : RegularJordanCurve}
    (o : Orientation ℝ Plane (Fin 2)) (A : ArcPresentation c)
    (hcorner : ∀ i, -Real.pi < cornerAngle o A i ∧ cornerAngle o A i < Real.pi) :
    ∃ κ : ℝ, 0 < κ ∧ 2*κ < Real.pi ∧
      ∀ i, |cornerAngle o A i| + 2*κ < Real.pi := by
  let d : Fin A.count → ℝ := fun i => (Real.pi - |cornerAngle o A i|) / 4
  have hd (i : Fin A.count) : 0 < d i := by
    have hi : |cornerAngle o A i| < Real.pi := abs_lt.mpr (hcorner i)
    dsimp [d]
    positivity
  have hne : (Finset.univ : Finset (Fin A.count)).Nonempty :=
    ⟨⟨0,A.positive⟩, Finset.mem_univ _⟩
  let κ := min (Real.pi/4) (Finset.univ.inf' hne d)
  have hκ : 0 < κ := lt_min (by positivity)
    ((Finset.lt_inf'_iff hne).mpr (fun i _ => hd i))
  refine ⟨κ,hκ, ?_, ?_⟩
  · have hh : κ ≤ Real.pi / 4 := min_le_left _ _
    linarith [Real.pi_pos]
  · intro i
    have hh : κ ≤ d i := (min_le_right _ _).trans (Finset.inf'_le d (Finset.mem_univ i))
    have hi : |cornerAngle o A i| < Real.pi := abs_lt.mpr (hcorner i)
    dsimp [d] at hh
    linarith

lemma oangle_normalize_both (o : Orientation ℝ Plane (Fin 2))
    {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
    o.oangle (NormedSpace.normalize u) (NormedSpace.normalize v) = o.oangle u v := by
  rw [NormedSpace.normalize, NormedSpace.normalize]
  rw [o.oangle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hu)),
    o.oangle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hv))]


/-- Real tangent phase on each original arc, taken from one genuine circuit lift. -/
def phase {c : RegularJordanCurve} (A : ArcPresentation c)
    (L : C(unitInterval, ℝ)) (i : Fin A.count) : C(unitInterval, ℝ) :=
  L.comp (P202.PlaneTurning.slotMap A ⟨2 * i.val, by omega⟩)

lemma phase_lifts {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    {A : ArcPresentation c} (T : TangentCircuit o A)
    (L : C(unitInterval, ℝ)) (hL : IsCircuitLift T L)
    (i : Fin A.count) (t : unitInterval) :
    (phase A L i t : Real.Angle) = direction o (velocity A i t) := by
  change (L (slot A ⟨2 * i.val, by omega⟩ t) : Real.Angle) = _
  rw [hL, T.on_arc]
  exact P202.PlaneTurning.direction_normalize o (A.regular i t t.property)

lemma phase_first {c : RegularJordanCurve} (A : ArcPresentation c)
    (L : C(unitInterval, ℝ)) :
    phase A L ⟨0, A.positive⟩ 0 = L 0 := by
  change L (slot A ⟨2 * (⟨0, A.positive⟩ : Fin A.count).val, by omega⟩ 0) = L 0
  rw [P202.PlaneTurning.slot_arc_start]
  exact congrArg L (P202.PlaneTurning.grid_first A)

lemma phase_join {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    {A : ArcPresentation c} (T : TangentCircuit o A)
    (L : C(unitInterval, ℝ)) (hL : IsCircuitLift T L) (i : Fin A.count) :
    phase A L i 1 + cornerAngle o A i =
      phase A L (finRotate A.count i) 0 +
        (if i.val + 1 = A.count then L 1 - L 0 else 0) := by
  obtain ⟨θ⟩ := P202.PlaneTurning.choicesExist c o A
  have hi := P202.PlaneTurning.circuit_corner_increment T θ L hL i
  rw [← P202.PlaneTurning.slot_arc_corner, P202.PlaneTurning.slot_corner_end] at hi
  have hn : 0 < A.count := A.positive
  letI : NeZero A.count := ⟨ne_of_gt hn⟩
  by_cases hilast : i.val + 1 = A.count
  · have his : i.succ = Fin.last A.count := Fin.ext (by simp; omega)
    have hrot : finRotate A.count i = 0 := by
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod,
        Fin.val_zero]
      rw [hilast, Nat.mod_self]
    rw [his, P202.PlaneTurning.grid_last] at hi
    simp only [if_pos hilast, hrot]
    have hfirst : phase A L (0 : Fin A.count) 0 = L 0 := by
      change L (slot A ⟨2 * (0 : Fin A.count).val, by omega⟩ 0) = L 0
      rw [P202.PlaneTurning.slot_arc_start]
      simpa using congrArg L (P202.PlaneTurning.grid_first A)
    rw [hfirst]
    change L (slot A ⟨2 * i.val, by omega⟩ 1) + cornerAngle o A i = _
    linarith
  · have hilt : i.val + 1 < A.count := by omega
    have hrot : (finRotate A.count i).castSucc = i.succ := by
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod,
        Fin.val_castSucc, Fin.val_succ]
      exact Nat.mod_eq_of_lt hilt
    have hstart : phase A L (finRotate A.count i) 0 =
        L (P202.PlaneTurning.grid A i.succ) := by
      change L (slot A ⟨2 * (finRotate A.count i).val, by omega⟩ 0) = _
      rw [P202.PlaneTurning.slot_arc_start, hrot]
    rw [if_neg hilast, add_zero, hstart]
    change L (slot A ⟨2 * i.val, by omega⟩ 1) + cornerAngle o A i = _
    linarith


lemma adjacent_arc_coordinates {c : RegularJordanCurve} (A : ArcPresentation c)
    (i k : Fin A.count) (a b d e : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hd : d ∈ Icc (0 : ℝ) 1) (he : e ∈ Icc (0 : ℝ) 1)
    (hab : a < b) (hde : d < e)
    (hx : A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*b =
      A.time k.castSucc + (A.time k.succ - A.time k.castSucc)*d) :
    (k = i ∧ b = d) ∨ (k.val = i.val + 1 ∧ b = 1 ∧ d = 0) := by
  have hi : 0 < A.time i.succ - A.time i.castSucc :=
    sub_pos.mpr (A.strictMono (by simp))
  have hk : 0 < A.time k.succ - A.time k.castSucc :=
    sub_pos.mpr (A.strictMono (by simp))
  have hbi : 0 < b := lt_of_le_of_lt ha.1 hab
  have hdk : d < 1 := lt_of_lt_of_le hde he.2
  have hik : i.val ≤ k.val := by
    by_contra! hh
    have ht : A.time k.succ ≤ A.time i.castSucc := A.strictMono.monotone (by
      change k.val + 1 ≤ i.val
      omega)
    nlinarith [hd.1, hb.2]
  have hki : k.val ≤ i.val + 1 := by
    by_contra! hh
    have ht : A.time i.succ < A.time k.castSucc := A.strictMono (by
      change i.val + 1 < k.val
      omega)
    nlinarith [hd.1, hb.2]
  by_cases hsame : k = i
  · left
    refine ⟨hsame, ?_⟩
    subst k
    nlinarith
  · right
    have hsucc : k.val = i.val + 1 := by
      have hne : k.val ≠ i.val := by intro h; exact hsame (Fin.ext h)
      omega
    have ht : A.time i.succ = A.time k.castSucc := congrArg A.time (Fin.ext (by
      simpa using hsucc.symm))
    refine ⟨hsucc, ?_, ?_⟩ <;> nlinarith [hd.1, hb.2]

lemma closing_arc_coordinates {c : RegularJordanCurve} (A : ArcPresentation c)
    (i k : Fin A.count) (b d : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1)
    (hbi : A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*b = 1)
    (hdk : A.time k.castSucc + (A.time k.succ - A.time k.castSucc)*d = 0) :
    i.val + 1 = A.count ∧ b = 1 ∧ k.val = 0 ∧ d = 0 := by
  have hi : 0 < A.time i.succ - A.time i.castSucc :=
    sub_pos.mpr (A.strictMono (by simp))
  have hk : 0 < A.time k.succ - A.time k.castSucc :=
    sub_pos.mpr (A.strictMono (by simp))
  have his : A.time i.succ ≤ 1 := by
    rw [← A.last]
    exact A.strictMono.monotone (Fin.le_last _)
  have hkz : 0 ≤ A.time k.castSucc := by
    rw [← A.first]
    exact A.strictMono.monotone (Fin.zero_le _)
  have hione : A.time i.succ = 1 := by nlinarith [hb.2]
  have hkzero : A.time k.castSucc = 0 := by nlinarith [hd.1]
  have hiidx : i.succ = Fin.last A.count := A.strictMono.injective (by
    simpa [A.last] using hione)
  have hkidx : k.castSucc = 0 := A.strictMono.injective (by
    simpa [A.first] using hkzero)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg Fin.val hiidx
    simpa using this
  · nlinarith
  · have := congrArg Fin.val hkidx
    simpa using this
  · nlinarith

lemma rotate_value_of_lt {n : ℕ} (i : Fin n) (hi : i.val+1 < n) :
    (finRotate n i).val = i.val+1 := by
  letI : NeZero n := i.neZero
  simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  exact Nat.mod_eq_of_lt hi

lemma rotate_value_of_last {n : ℕ} (i : Fin n) (hi : ¬i.val+1 < n) :
    (finRotate n i).val = 0 := by
  letI : NeZero n := i.neZero
  simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have he : i.val+1 = n := by omega
  rw [he, Nat.mod_self]

lemma successive_refined_coordinates {c : RegularJordanCurve} (A : ArcPresentation c)
    (Q : Partition) (j : Fin Q.count) (i k : Fin A.count) (a b d e : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hd : d ∈ Icc (0 : ℝ) 1) (he : e ∈ Icc (0 : ℝ) 1)
    (hab : a < b) (hde : d < e)
    (hsb : Q.time j.succ =
      A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*b)
    (hsd : Q.time (finRotate Q.count j).castSucc =
      A.time k.castSucc + (A.time k.succ - A.time k.castSucc)*d) :
    if j.val+1 < Q.count then
      ((k = i ∧ b = d) ∨
        (k = finRotate A.count i ∧ b = 1 ∧ d = 0 ∧ i.val+1 < A.count))
    else
      (i.val+1 = A.count ∧ b = 1 ∧ k.val = 0 ∧ d = 0) := by
  by_cases hj : j.val+1 < Q.count
  · simp only [if_pos hj]
    have htime : Q.time j.succ = Q.time (finRotate Q.count j).castSucc := by
      congr 1
      apply Fin.ext
      simpa using (rotate_value_of_lt j hj).symm
    have hx : A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*b =
        A.time k.castSucc + (A.time k.succ - A.time k.castSucc)*d := by
      rw [← hsb, htime, hsd]
    obtain hsame | ⟨hnext, hb1, hd0⟩ := adjacent_arc_coordinates A i k a b d e
      ha hb hd he hab hde hx
    · exact Or.inl hsame
    · have hi : i.val+1 < A.count := by omega
      refine Or.inr ⟨?_, hb1, hd0, hi⟩
      apply Fin.ext
      rw [rotate_value_of_lt i hi]
      exact hnext
  · simp only [if_neg hj]
    have hlast : j.succ = Fin.last Q.count := Fin.ext (by simp; omega)
    have hzero : (finRotate Q.count j).castSucc = 0 := Fin.ext (by
      simpa using rotate_value_of_last j hj)
    have hbi : A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*b = 1 := by
      rw [← hsb, hlast, Q.last]
    have hdk : A.time k.castSucc + (A.time k.succ - A.time k.castSucc)*d = 0 := by
      rw [← hsd, hzero, Q.first]
    exact closing_arc_coordinates A i k b d hb hd hbi hdk

lemma successive_sample_join {c : RegularJordanCurve} (A : ArcPresentation c)
    (o : Orientation ℝ Plane (Fin 2)) (Q : Partition)
    (p : Fin A.count → unitInterval → ℝ) (W : ℝ)
    (hp : ∀ i : Fin A.count, p i 1 + cornerAngle o A i =
      p (finRotate A.count i) 0 + (if i.val+1 < A.count then 0 else W))
    (j : Fin Q.count) (i k : Fin A.count) (a b d e : unitInterval)
    (hab : (a : ℝ) < b) (hde : (d : ℝ) < e)
    (hsb : Q.time j.succ =
      A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*(b : ℝ))
    (hsd : Q.time (finRotate Q.count j).castSucc =
      A.time k.castSucc + (A.time k.succ - A.time k.castSucc)*(d : ℝ)) :
    p i b + (if (b : ℝ) = 1 then cornerAngle o A i else 0) =
      p k d + (if j.val+1 < Q.count then 0 else W) := by
  have hc := successive_refined_coordinates A Q j i k a b d e
    a.property b.property d.property e.property hab hde hsb hsd
  by_cases hj : j.val+1 < Q.count
  · simp only [if_pos hj] at hc ⊢
    rcases hc with ⟨hki, hbd⟩ | ⟨hki, hb, hd, hi⟩
    · have hbd' : b = d := Subtype.ext hbd
      have hb1 : (b : ℝ) ≠ 1 := by
        have := e.property.2
        linarith
      rw [if_neg hb1, hki, hbd']
    · have hb' : b = 1 := Subtype.ext hb
      have hd' : d = 0 := Subtype.ext hd
      simpa [hki, hb', hd', hi] using hp i
  · simp only [if_neg hj] at hc ⊢
    obtain ⟨hi, hb, hk, hd⟩ := hc
    have hni : ¬ i.val+1 < A.count := by omega
    have hki : k = finRotate A.count i := Fin.ext (by
      rw [rotate_value_of_last i hni]
      exact hk)
    have hb' : b = 1 := Subtype.ext hb
    have hd' : d = 0 := Subtype.ext hd
    simpa [hki, hb', hd', hni] using hp i

lemma cyclic_sum_displacements {n : ℕ} (hn : 0 < n) (B : Fin n → ℝ) (D : ℝ) :
    (∑ j : Fin n, (B (finRotate n j) - B j +
      if j.val + 1 < n then 0 else D)) = D := by
  have hs : (∑ j : Fin n, B (finRotate n j)) = ∑ j : Fin n, B j :=
    Equiv.sum_comp (finRotate n) B
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hs, sub_self, zero_add]
  let l : Fin n := ⟨n-1, by omega⟩
  rw [Finset.sum_eq_single l]
  · have hh : ¬ l.val+1<n := by dsimp [l]; omega
    simp [hh]
  · intro j _ hj
    have hh : j.val+1<n := by
      have hne : j.val ≠ n-1 := fun h => hj (Fin.ext h)
      omega
    simp [hh]
  · simp

lemma polygon_sum_of_lifted_phases {c : RegularJordanCurve} {Q : Partition}
    {o : Orientation ℝ Plane (Fin 2)} (B : Fin Q.count → ℝ) (D : ℝ)
    (hB : ∀ j, (B j : Real.Angle) = direction o (inscribedEdge c Q j))
    (hD : (D : Real.Angle) = 0)
    (hsmall : ∀ j, |B (finRotate Q.count j) - B j +
      (if j.val+1<Q.count then 0 else D)| < Real.pi) :
    P202Specs.PolygonTurning.totalTurning o (polygon c Q) = D := by
  have he (j : Fin Q.count) : polygonCornerAngle o c Q j =
      B (finRotate Q.count j) - B j + (if j.val+1<Q.count then 0 else D) := by
    let d := B (finRotate Q.count j) - B j + (if j.val+1<Q.count then 0 else D)
    have hd : (d : Real.Angle) = o.oangle (inscribedEdge c Q j)
        (inscribedEdge c Q (finRotate Q.count j)) := by
      change (((B (finRotate Q.count j) - B j +
        (if j.val+1<Q.count then 0 else D)) : ℝ) : Real.Angle) = _
      rw [Real.Angle.coe_add, Real.Angle.coe_sub, hB, hB]
      have hz : (((if j.val+1<Q.count then 0 else D) : ℝ) : Real.Angle) = 0 := by
        split_ifs <;> simp [hD]
      rw [hz, add_zero]
      unfold direction
      exact o.oangle_sub_left reference_nonzero (nonzeroEdges c Q j)
        (nonzeroEdges c Q (finRotate Q.count j))
    change (o.oangle _ _).toReal = d
    rw [← hd]
    exact Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨(abs_lt.mp (hsmall j)).1, (abs_lt.mp (hsmall j)).2.le⟩
  rw [← polygon_sum]
  simp only [polygonTurning, he]
  exact cyclic_sum_displacements (by have := Q.at_least_three; omega) B D

/-- Chord angle charts have constant corrected lifts on small smooth subarcs.
The finite two-sided corner margins make all cyclic phase differences principal,
so their telescoping sum is exactly the original tangent lift displacement. -/
theorem uniformTurningEquality : Expected.uniformTurningEquality := by
  intro c o A
  obtain ⟨κ,hκ,hκπ,hκcorner⟩ :=
    finite_corner_margin o A (P202.PlaneTurning.cornerBounds c o A)
  obtain ⟨η,hη,hηangle⟩ := uniform_short_angle_small o κ hκ
  obtain ⟨δ,hδ,hδdir⟩ := refined_chord_directions A η hη
  obtain ⟨T⟩ := P202.PlaneTurning.circuitExists c o A
  obtain ⟨L,hL⟩ := P202.PlaneTurning.circuit_lift_exists T
  let D := L 1 - L 0
  have hD : (D : Real.Angle) = 0 := by
    change ((L 1 - L 0 : ℝ) : Real.Angle) = 0
    rw [Real.Angle.coe_sub, hL, hL, T.closed, sub_self]
  have hp (i : Fin A.count) : phase A L i 1 + cornerAngle o A i =
      phase A L (finRotate A.count i) 0 +
        (if i.val+1<A.count then 0 else D) := by
    have hh := phase_join T L hL i
    by_cases hi : i.val+1<A.count
    · have hn : i.val+1 ≠ A.count := by omega
      simpa only [if_pos hi, if_neg hn, add_zero] using hh
    · have hn : i.val+1 = A.count := by omega
      simpa only [if_neg hi, if_pos hn] using hh
  refine ⟨δ,hδ,?_⟩
  intro Q hQ hmesh θ
  choose idx a b ha hb hab hsa hsb hdir using hδdir Q hQ hmesh
  let aa (j : Fin Q.count) : unitInterval := ⟨a j,ha j⟩
  let bb (j : Fin Q.count) : unitInterval := ⟨b j,hb j⟩
  let V (j : Fin Q.count) : Plane := NormedSpace.normalize (inscribedEdge c Q j)
  let R (j : Fin Q.count) (t : unitInterval) : ℝ :=
    (o.oangle (P202.PlaneTurning.tangentArc A (idx j) t) (V j)).toReal
  have hV (j : Fin Q.count) : V j ≠ 0 :=
    (NormedSpace.normalize_eq_zero_iff _).not.mpr (nonzeroEdges c Q j)
  have hU (j : Fin Q.count) (t : unitInterval) :
      P202.PlaneTurning.tangentArc A (idx j) t ≠ 0 :=
    (NormedSpace.normalize_eq_zero_iff _).not.mpr (A.regular (idx j) t t.property)
  have hf (j : Fin Q.count) (t : unitInterval) :
      (phase A L (idx j) t : Real.Angle) =
        direction o (P202.PlaneTurning.tangentArc A (idx j) t) := by
    change (phase A L (idx j) t : Real.Angle) =
      direction o (NormedSpace.normalize (velocity A (idx j) t))
    exact (phase_lifts T L hL (idx j) t).trans
      (P202.PlaneTurning.direction_normalize o
        (v := velocity A (idx j) t) (A.regular (idx j) t t.property)).symm
  have hR (j : Fin Q.count) (t : unitInterval) (ht : (t : ℝ) ∈ Icc (a j) (b j)) :
      |R j t| < κ := by
    apply hηangle _ _
    · exact NormedSpace.norm_normalize (A.regular (idx j) t t.property)
    · exact NormedSpace.norm_normalize (nonzeroEdges c Q j)
    · simpa only [P202.PlaneTurning.tangentArc, ContinuousMap.coe_mk, V, norm_sub_rev]
        using hdir j t ht
  let B (j : Fin Q.count) : ℝ := phase A L (idx j) (aa j) + R j (aa j)
  have hBend (j : Fin Q.count) :
      B j = phase A L (idx j) (bb j) + R j (bb j) := by
    exact (fixed_direction_correction_interval o (P202.PlaneTurning.tangentArc A (idx j))
      (phase A L (idx j)) (V j) (hU j) (hV j) (hf j)
      (aa j) (bb j) (by exact (hab j).le) (by
        intro t ht he
        have hh := hR j t ⟨ht.1,ht.2⟩
        dsimp [R] at hh
        rw [he, Real.Angle.toReal_pi] at hh
        have hp0 := Real.pi_pos
        rw [abs_of_pos hp0] at hh
        linarith)).symm
  have hB (j : Fin Q.count) :
      (B j : Real.Angle) = direction o (inscribedEdge c Q j) := by
    have hh := corrected_angle_lifts o (hU j (aa j)) (hV j) (hf j (aa j))
    change (B j : Real.Angle) = direction o (V j) at hh
    rw [P202.PlaneTurning.direction_normalize o (nonzeroEdges c Q j)] at hh
    exact hh
  have hsmall (j : Fin Q.count) :
      |B (finRotate Q.count j) - B j +
        (if j.val+1<Q.count then 0 else D)| < Real.pi := by
    let k := finRotate Q.count j
    have hj := successive_sample_join A o Q (fun i t => phase A L i t) D hp
      j (idx j) (idx k) (aa j) (bb j) (aa k) (bb k)
      (hab j) (hab k) (hsb j) (hsa k)
    let C : ℝ := if b j = 1 then cornerAngle o A (idx j) else 0
    have hC : |C| + 2*κ < Real.pi := by
      dsimp [C]
      split_ifs
      · exact hκcorner (idx j)
      · simpa using hκπ
    have hr0 := hR k (aa k) ⟨le_rfl,(hab k).le⟩
    have hr1 := hR j (bb j) ⟨(hab j).le,le_rfl⟩
    have he : B k - B j + (if j.val+1<Q.count then 0 else D) =
        C + R k (aa k) - R j (bb j) := by
      rw [hBend j]
      change phase A L (idx k) (aa k) + R k (aa k) -
          (phase A L (idx j) (bb j) + R j (bb j)) + _ = _
      change phase A L (idx j) (bb j) + C =
        phase A L (idx k) (aa k) + _ at hj
      linarith
    change |B k - B j + _| < _
    rw [he]
    calc
      |C + R k (aa k) - R j (bb j)| ≤ |C| + |R k (aa k)| + |R j (bb j)| := by
        linarith [abs_sub (C + R k (aa k)) (R j (bb j)),
          abs_add_le C (R k (aa k))]
      _ < Real.pi := by linarith
  have hpoly := polygon_sum_of_lifted_phases B D hB hD hsmall
  have htotal := P202.PlaneTurning.circuit_increment_eq_total T θ L hL
  exact htotal.trans hpoly.symm

theorem comparison : Expected.comparison :=
  comparison_of_uniformTurningEquality uniformTurningEquality

end P202.PlaneTangentComparison
