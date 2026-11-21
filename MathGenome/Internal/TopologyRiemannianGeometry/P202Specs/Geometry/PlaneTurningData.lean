import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionFoundation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Topology.Covering.FundamentalGroupCircle

/-!
Independent tangent-data statements for paper.tex 4831–4889, lem:p202-plane-turning.
The curve is the shared circle-parametrized regular Jordan curve. A finite
arc presentation records actual smooth extensions of its restrictions; its
existence is a conclusion, not an additional hypothesis on the curve.
Angles are measured in an arbitrary orientation of the shared Euclidean plane.
The unit-tangent circuit inserts literal shorter rotations at all joins.
-/
noncomputable section
open Set
open scoped BigOperators unitInterval ContDiff

namespace P202Specs.PlaneTurning
open PlanarRegionTopology (Plane ParameterCircle RegularJordanCurve realLift)

instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A finite smooth decomposition of the original parametrized curve, with
positive affine reparametrizations of the intervals in one period. Extra
smooth subdivision vertices are permitted. -/
structure ArcPresentation (c : RegularJordanCurve) where
  count : ℕ
  positive : 0 < count
  time : Fin (count + 1) → ℝ
  strictMono : StrictMono time
  first : time 0 = 0
  last : time (Fin.last count) = 1
  arc : Fin count → ℝ → Plane
  agrees : ∀ (i : Fin count) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
    arc i t = realLift c.parametrization
      (time i.castSucc + (time i.succ - time i.castSucc) * t)
  smooth : ∀ i : Fin count, ∃ δ : ℝ, 0 < δ ∧
    ContDiffOn ℝ ∞ (arc i) (Ioo (-δ) (1 + δ))
  regular : ∀ (i : Fin count) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → deriv (arc i) t ≠ 0
  noncuspidal : ∀ i : Fin count,
    NormedSpace.normalize (deriv (arc i) 1) ≠
      -NormedSpace.normalize (deriv (arc (finRotate count i)) 0)

def reference : Plane := !₂[1, 0]

def velocity {c : RegularJordanCurve} (A : ArcPresentation c) (i : Fin A.count)
    (t : ℝ) : Plane := deriv (A.arc i) t

def direction (o : Orientation ℝ Plane (Fin 2)) (v : Plane) : Real.Angle :=
  o.oangle reference v

/-- Short signed exterior rotation, including zero and negative turns. -/
def cornerAngle {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (i : Fin A.count) : ℝ :=
  (o.oangle (velocity A i 1) (velocity A (finRotate A.count i) 0)).toReal

/-- Every continuous real tangent-angle choice is allowed, with independently
chosen integer translates on different arcs. -/
structure AngleChoices {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) where
  angle : Fin A.count → C(unitInterval, ℝ)
  lifts : ∀ i t, (angle i t : Real.Angle) = direction o (velocity A i t)

def totalTurning {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    {A : ArcPresentation c} (θ : AngleChoices o A) : ℝ :=
  ∑ i, (θ.angle i 1 - θ.angle i 0 + cornerAngle o A i)

/-- The reversed physical smooth arc, with the original index retained. -/
def reversedArc {c : RegularJordanCurve} (A : ArcPresentation c)
    (i : Fin A.count) (t : ℝ) : Plane := A.arc i (1 - t)

/-- Continuous angles of the actual reversed velocities. -/
def reversedAngle {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    {A : ArcPresentation c} (θ : AngleChoices o A) (i : Fin A.count) :
    C(unitInterval, ℝ) :=
  ⟨fun t => θ.angle i (unitInterval.symm t) + Real.pi, by fun_prop⟩

/-- Reversed traversal, indexed by the original arcs: the arc angle increment
is negated, and the next arc is the original predecessor. The π added to the
angle of every reversed velocity cancels in its endpoint increment. -/
def reversedTotalTurning {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    {A : ArcPresentation c} (θ : AngleChoices o A) : ℝ :=
  ∑ i, (reversedAngle θ i 1 - reversedAngle θ i 0 +
    (o.oangle (-velocity A i 0)
      (-velocity A ((finRotate A.count).symm i) 1)).toReal)

/-- The same reversed traversal with arbitrary continuous reversed angles. -/
def reversedTurningWith {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (ψ : Fin A.count → C(unitInterval, ℝ)) : ℝ :=
  ∑ i, (ψ i 1 - ψ i 0 +
    (o.oangle (-velocity A i 0)
      (-velocity A ((finRotate A.count).symm i) 1)).toReal)

def LiftsReversed {c : RegularJordanCurve} (o : Orientation ℝ Plane (Fin 2))
    (A : ArcPresentation c) (ψ : Fin A.count → C(unitInterval, ℝ)) : Prop :=
  ∀ i t, (ψ i t : Real.Angle) = direction o (-velocity A i (1 - t))

/-- The geometric bounded Jordan side, without orientation or index input. -/
def IsBoundedSide (c : RegularJordanCurve) (U : Set Plane) : Prop :=
  IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧ frontier U = c.trace

def HasBoundedSideOnLeft (c : RegularJordanCurve)
    (o : Orientation ℝ Plane (Fin 2)) (U : Set Plane) : Prop :=
  ∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      realLift c.parametrization t +
        r • o.rightAngleRotation (deriv (realLift c.parametrization) t) ∈ U

/-- A uniform interval slot. It is used for both smooth and polygon circuits. -/
def uniformSlot (n : ℕ) (hn : 0 < n) (j : Fin n)
    (t : unitInterval) : unitInterval :=
  ⟨((j : ℝ) + t) / n, by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    constructor
    · exact div_nonneg (add_nonneg (by positivity) t.property.1) hn'.le
    · apply (div_le_one hn').mpr
      have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
      linarith [t.property.2]⟩

/-- Uniform slots for traversing each smooth tangent arc and its next corner. -/
def slot {c : RegularJordanCurve} (A : ArcPresentation c) (j : Fin (2 * A.count))
    (t : unitInterval) : unitInterval :=
  ⟨((j : ℝ) + t) / (2 * A.count), by
    have hn : (0 : ℝ) < A.count := by exact_mod_cast A.positive
    constructor
    · exact div_nonneg (add_nonneg (by positivity) t.property.1) (by positivity)
    · apply (div_le_one (by positivity : (0 : ℝ) < 2 * A.count)).mpr
      have hj : (j : ℝ) + 1 ≤ 2 * A.count := by exact_mod_cast j.isLt
      linarith [t.property.2]⟩

/-- An actual continuous unit-vector loop with prescribed arc and short
corner formulas. This is constructed in the conclusion, never assumed of c. -/
structure TangentCircuit {c : RegularJordanCurve}
    (o : Orientation ℝ Plane (Fin 2)) (A : ArcPresentation c) where
  map : C(unitInterval, Plane)
  unit : ∀ t, ‖map t‖ = 1
  closed : map 1 = map 0
  on_arc : ∀ (i : Fin A.count) (t : unitInterval),
    map (slot A ⟨2 * i.val, by omega⟩ t) = NormedSpace.normalize (velocity A i t)
  on_corner : ∀ (i : Fin A.count) (t : unitInterval),
    map (slot A ⟨2 * i.val + 1, by omega⟩ t) =
      o.rotation ((t : ℝ) * cornerAngle o A i : ℝ)
        (NormedSpace.normalize (velocity A i 1))

/-- The fixed axis is nonzero; it has unit Euclidean length. -/
lemma reference_nonzero : reference ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Plane => v 0) h
  norm_num [reference] at h0

/-- The actual direction loop in the angle circle ℝ/(2πℤ). -/
def TangentCircuit.angleLoop {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} {A : ArcPresentation c}
    (T : TangentCircuit o A) :
    Path (direction o (T.map 0)) (direction o (T.map 0)) where
  toFun t := direction o (T.map t)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have h0 : T.map t ≠ 0 := by
      intro h
      have hu := T.unit t
      simp [h] at hu
    have hc : ContinuousAt
        (fun p : Plane × Plane => o.oangle p.1 p.2) (reference, T.map t) :=
      o.continuousAt_oangle (x := (reference, T.map t)) reference_nonzero h0
    exact ContinuousAt.comp (f := fun s : unitInterval => (reference, T.map s)) hc
      (continuous_const.prodMk T.map.continuous).continuousAt
  source' := rfl
  target' := congrArg (direction o) T.closed

/-- Winding of the inserted unit-tangent circuit, using Mathlib's actual
fundamental-group invariant of the angle circle. -/
def TangentCircuit.winding {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} {A : ArcPresentation c}
    (T : TangentCircuit o A) : ℤ :=
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  AddCircle.windingNumber (p := 2 * Real.pi) (.of (.mk T.angleLoop))

/-- All real lifts of the genuine angle loop, with arbitrary initial value. -/
def IsCircuitLift {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    {A : ArcPresentation c} (T : TangentCircuit o A) (L : C(unitInterval, ℝ)) : Prop :=
  ∀ t, (L t : Real.Angle) = direction o (T.map t)

/-- A strictly increasing finite partition of one full period. There are
at least three edges. It contains no geometric or turning certificate. -/
structure Partition where
  count : ℕ
  at_least_three : 3 ≤ count
  time : Fin (count + 1) → ℝ
  strictMono : StrictMono time
  first : time 0 = 0
  last : time (Fin.last count) = 1

/-- Knot preservation is a condition on parameter values alone. -/
def Partition.Refines {c : RegularJordanCurve} (Q : Partition)
    (A : ArcPresentation c) : Prop :=
  ∀ i : Fin (A.count + 1), ∃ j : Fin (Q.count + 1), Q.time j = A.time i

/-- Every consecutive parameter gap is strictly smaller than δ. -/
def Partition.MeshLT (Q : Partition) (δ : ℝ) : Prop :=
  ∀ i : Fin Q.count, Q.time i.succ - Q.time i.castSucc < δ

/-- Literal inscribed vertices of the original curve. -/
def inscribedVertex (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count) : Plane :=
  realLift c.parametrization (Q.time i.castSucc)

/-- Directed chord of the original parametrized curve, including the last chord
ending at parameter 1, which represents the initial point of the circle. -/
def inscribedEdge (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count) : Plane :=
  realLift c.parametrization (Q.time i.succ) - inscribedVertex c Q i

/-- The actual straight segment at its affine parameter. -/
def inscribedEdgeMap (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count)
    (t : unitInterval) : Plane :=
  inscribedVertex c Q i + (t : ℝ) • inscribedEdge c Q i

/-- The actual polygonal trace; vertices are never perturbed. -/
def inscribedTrace (c : RegularJordanCurve) (Q : Partition) : Set Plane :=
  ⋃ i : Fin Q.count, Set.range (inscribedEdgeMap c Q i)

/-- Short exterior angle at the end of directed chord i. -/
def polygonCornerAngle (o : Orientation ℝ Plane (Fin 2))
    (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count) : ℝ :=
  (o.oangle (inscribedEdge c Q i)
    (inscribedEdge c Q (finRotate Q.count i))).toReal

def polygonTurning (o : Orientation ℝ Plane (Fin 2))
    (c : RegularJordanCurve) (Q : Partition) : ℝ :=
  ∑ i, polygonCornerAngle o c Q i

/-- A freely based unit direction loop, represented by its genuine map. -/
structure UnitDirectionLoop where
  map : C(unitInterval, Plane)
  unit : ∀ t, ‖map t‖ = 1
  closed : map 1 = map 0

/-- A homotopy in the unit circle through closed loops. The basepoint may move. -/
structure UnitDirectionHomotopy (T S : UnitDirectionLoop) where
  map : C(unitInterval × unitInterval, Plane)
  unit : ∀ s t, ‖map (s, t)‖ = 1
  at_zero : ∀ t, map (0, t) = T.map t
  at_one : ∀ t, map (1, t) = S.map t
  closed : ∀ s, map (s, 1) = map (s, 0)

def TangentCircuit.toUnitLoop {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} {A : ArcPresentation c}
    (T : TangentCircuit o A) : UnitDirectionLoop := ⟨T.map, T.unit, T.closed⟩

/-- A polygon circuit has constant edge-direction slots and literal short
corner rotations. Existence and any nondegeneracy are conclusions to prove
for sufficiently fine partitions, rather than assumptions in the partition. -/
structure PolygonCircuit (o : Orientation ℝ Plane (Fin 2))
    (c : RegularJordanCurve) (Q : Partition) extends UnitDirectionLoop where
  on_edge : ∀ (i : Fin Q.count) (t : unitInterval),
    map (uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val, by omega⟩ t) = NormedSpace.normalize (inscribedEdge c Q i)
  on_corner : ∀ (i : Fin Q.count) (t : unitInterval),
    map (uniformSlot (2 * Q.count) (by have := Q.at_least_three; omega)
      ⟨2 * i.val + 1, by omega⟩ t) =
      o.rotation ((t : ℝ) * polygonCornerAngle o c Q i : ℝ)
        (NormedSpace.normalize (inscribedEdge c Q i))

namespace Expected

def presentationExists : Prop := ∀ c : RegularJordanCurve, Nonempty (ArcPresentation c)

def choicesExist : Prop := ∀ (c : RegularJordanCurve) (o : Orientation ℝ Plane (Fin 2))
  (A : ArcPresentation c), Nonempty (AngleChoices o A)

def choiceIndependence : Prop := ∀ (c : RegularJordanCurve)
  (o : Orientation ℝ Plane (Fin 2)) (A : ArcPresentation c) (θ φ : AngleChoices o A),
  (∀ i, θ.angle i 1 - θ.angle i 0 = φ.angle i 1 - φ.angle i 0) ∧
    totalTurning θ = totalTurning φ

def cornerBounds : Prop := ∀ (c : RegularJordanCurve) (o : Orientation ℝ Plane (Fin 2))
  (A : ArcPresentation c) (i : Fin A.count),
  -Real.pi < cornerAngle o A i ∧ cornerAngle o A i < Real.pi

def reversal : Prop := ∀ (c : RegularJordanCurve) (o : Orientation ℝ Plane (Fin 2))
  (A : ArcPresentation c) (θ : AngleChoices o A),
  (∀ (i : Fin A.count) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
    HasDerivAt (reversedArc A i) (-velocity A i (1 - t)) t) ∧
  (∀ (i : Fin A.count) (t : unitInterval),
    (reversedAngle θ i t : Real.Angle) = direction o (-velocity A i (1 - t))) ∧
  reversedTotalTurning θ = -totalTurning θ ∧
  ∀ ψ : Fin A.count → C(unitInterval, ℝ), LiftsReversed o A ψ →
    reversedTurningWith o A ψ = -totalTurning θ

/-- Construction of the continuous unit-tangent loop with short corner
rotations, existence of its real lift, and identification of all lift changes
with the displayed sum. The integer is its winding under ℝ → ℝ/(2πℤ). -/
def circuitLiftFormula : Prop := ∀ (c : RegularJordanCurve)
  (o : Orientation ℝ Plane (Fin 2)) (A : ArcPresentation c),
  ∀ T : TangentCircuit o A,
    (∃ L : C(unitInterval, ℝ), IsCircuitLift T L) ∧
    ∀ (θ : AngleChoices o A) (L : C(unitInterval, ℝ)), IsCircuitLift T L →
      totalTurning θ = L 1 - L 0 ∧
      L 1 - L 0 = 2 * Real.pi * (T.winding : ℝ)

/-- Circuit existence is stated independently of lift arithmetic. -/
def circuitExists : Prop := ∀ (c : RegularJordanCurve)
  (o : Orientation ℝ Plane (Fin 2)) (A : ArcPresentation c),
  Nonempty (TangentCircuit o A)

/-- Full winding connection, with no tangent circuit assumed as curve input. -/
def tangentWinding : Prop := circuitExists ∧ circuitLiftFormula

/-- Arbitrarily fine strictly increasing partitions preserving all smooth
presentation knots, with at least three literal polygon edges. -/
def finePartitions : Prop := ∀ (c : RegularJordanCurve) (A : ArcPresentation c)
    (δ : ℝ), 0 < δ → ∃ Q : Partition, Q.Refines A ∧ Q.MeshLT δ

end Expected
end P202Specs.PlaneTurning
