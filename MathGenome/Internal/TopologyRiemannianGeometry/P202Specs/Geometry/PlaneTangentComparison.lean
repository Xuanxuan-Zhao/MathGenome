import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneTurningData
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolygonTurning

/-!
Independent statements for the tangent/polygon comparison in
paper.tex 4843–4850 and 4875–4888. All polygons below have the literal
inscribed vertices, and all homotopies take values in the unit circle.
No simplicity, positivity, angle sum, or homotopy certificate is input.
-/
noncomputable section
open Set
open scoped BigOperators unitInterval

namespace P202Specs.PlaneTangentComparison
open PlaneTurning
open PlanarRegionTopology (Plane RegularJordanCurve)

/-- The polygon with the original curve's actual sampled vertices. -/
def polygon (c : RegularJordanCurve) (Q : Partition) : Polygon Plane Q.count :=
  ⟨inscribedVertex c Q⟩

/-- Direction as a genuine closed path in the radian angle circle.
The initial point depends on the loop; it is not fixed by convention. -/
def angleLoop (o : Orientation ℝ Plane (Fin 2)) (S : UnitDirectionLoop) :
    Path (direction o (S.map 0)) (direction o (S.map 0)) where
  toFun t := direction o (S.map t)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hn : S.map t ≠ 0 := by
      intro h
      have hu := S.unit t
      simp [h] at hu
    exact ContinuousAt.comp (f := fun s : unitInterval => (reference, S.map s))
      (o.continuousAt_oangle reference_nonzero hn)
      (continuous_const.prodMk S.map.continuous).continuousAt
  source' := rfl
  target' := congrArg (direction o) S.closed

/-- Mathlib's circle winding, at the actual moving basepoint. -/
def winding (o : Orientation ℝ Plane (Fin 2)) (S : UnitDirectionLoop) : ℤ :=
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  AddCircle.windingNumber (p := 2 * Real.pi) (.of (.mk (angleLoop o S)))

namespace Expected

/-- Closing parameter 1 is the initial parameter 0 in the source circle.
This identifies every literal chord, including the closing edge. -/
def polygonEdges : Prop := ∀ (c : RegularJordanCurve) (Q : Partition),
  (∀ i, PolygonTurning.edgeVector (polygon c Q) i = inscribedEdge c Q i) ∧
  (∀ o : Orientation ℝ Plane (Fin 2),
    PlaneTurning.polygonTurning o c Q = PolygonTurning.totalTurning o (polygon c Q))

/-- A Jordan parametrization and a strictly increasing partition already
ensure that every chord is nonzero. No mesh hypothesis is necessary. -/
def nonzeroEdges : Prop := ∀ (c : RegularJordanCurve) (Q : Partition)
  (i : Fin Q.count), inscribedEdge c Q i ≠ 0

/-- Construct the polygon circuit from its genuine constant edge directions
and the shorter signed rotations at all vertices. -/
def polygonCircuits : Prop := ∀ (c : RegularJordanCurve)
  (o : Orientation ℝ Plane (Fin 2)) (Q : Partition),
  Nonempty (PolygonCircuit o c Q)

/-- Every real lift of the polygon direction loop has increment exactly the
literal exterior-angle sum, and this is 2π times its actual circle winding. -/
def polygonWinding : Prop := ∀ (c : RegularJordanCurve)
  (o : Orientation ℝ Plane (Fin 2)) (Q : Partition) (P : PolygonCircuit o c Q),
  (∃ L : C(unitInterval, ℝ), ∀ t, (L t : Real.Angle) = direction o (P.map t)) ∧
  ∀ L : C(unitInterval, ℝ),
    (∀ t, (L t : Real.Angle) = direction o (P.map t)) →
    PolygonTurning.totalTurning o (polygon c Q) = L 1 - L 0 ∧
    L 1 - L 0 = 2 * Real.pi * (winding o P.toUnitDirectionLoop : ℝ)

/-- Free homotopies through unit loops preserve genuine circle winding even
when their initial points move. -/
def homotopyWinding : Prop := ∀ (o : Orientation ℝ Plane (Fin 2))
  (S T : UnitDirectionLoop), UnitDirectionHomotopy S T → winding o S = winding o T

/-- The converse constructs an actual homotopy in the unit circle, by
interpolating real angle lifts with identical endpoint displacement. -/
def homotopyClassification : Prop := ∀ (o : Orientation ℝ Plane (Fin 2))
  (S T : UnitDirectionLoop),
  Nonempty (UnitDirectionHomotopy S T) ↔ winding o S = winding o T

/-- Uniform chord-direction convergence on every actual smooth arc, with a
single threshold for the finite presentation. Chords are endpoint differences
of the given arc, and all tangents on the subarc are covered. -/
def smallChordDirections : Prop := ∀ (c : RegularJordanCurve) (A : ArcPresentation c)
  (ε : ℝ), 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ (i : Fin A.count) (a b : ℝ),
    a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → a < b → b-a < η →
    ∀ t ∈ Icc a b,
      ‖NormedSpace.normalize (A.arc i b - A.arc i a) -
        NormedSpace.normalize (velocity A i t)‖ < ε

/-- At every original join the short signed angle is stable under independent
perturbation of its two unit tangents. The strict π margin includes reflex
and straight joins and explicitly rules out crossing the branch cut. -/
def cornerStability : Prop := ∀ (c : RegularJordanCurve)
  (o : Orientation ℝ Plane (Fin 2)) (A : ArcPresentation c) (i : Fin A.count)
  (ε : ℝ), 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ u v : Plane,
    ‖u - NormedSpace.normalize (velocity A i 1)‖ < η →
    ‖v - NormedSpace.normalize (velocity A (finRotate A.count i) 0)‖ < η →
    -Real.pi < (o.oangle u v).toReal ∧ (o.oangle u v).toReal < Real.pi ∧
    |(o.oangle u v).toReal - cornerAngle o A i| < ε

/-- Knot preservation really places each literal edge on one original smooth
subarc. All local parameters and the affine agreement are conclusions. -/
def refiningEdges : Prop := ∀ (c : RegularJordanCurve) (A : ArcPresentation c)
  (Q : Partition), Q.Refines A → ∀ j : Fin Q.count,
    ∃ (i : Fin A.count) (a b : ℝ),
      a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a < b ∧
      Q.time j.castSucc = A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*a ∧
      Q.time j.succ = A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*b ∧
      inscribedEdge c Q j = A.arc i b - A.arc i a

/-- The actual global parameter mesh, rather than a mesh in arbitrarily
rescaled arc parameters, controls all chord directions simultaneously. -/
def refinedChordDirections : Prop := ∀ (c : RegularJordanCurve) (A : ArcPresentation c)
  (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition,
    Q.Refines A → Q.MeshLT δ → ∀ j : Fin Q.count,
      ∃ (i : Fin A.count) (a b : ℝ),
        a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a < b ∧
        Q.time j.castSucc = A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*a ∧
        Q.time j.succ = A.time i.castSucc + (A.time i.succ - A.time i.castSucc)*b ∧
        ∀ t ∈ Icc a b,
          ‖NormedSpace.normalize (inscribedEdge c Q j) -
            NormedSpace.normalize (velocity A i t)‖ < ε

/-- Local increasing projections exclude opposite adjacent directions for
every sufficiently fine literal inscribed polygon, even without refinement. -/
def fineNoncuspidal : Prop := ∀ c : RegularJordanCurve,
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
    PolygonTurning.Noncuspidal (polygon c Q)

/-- The scalar comparison, expressed independently of any circuit
or homotopy witness. Together with the proved general winding and existence
statements, this implies the full unit-circle comparison below. -/
def uniformTurningEquality : Prop := ∀ (c : RegularJordanCurve)
  (o : Orientation ℝ Plane (Fin 2)) (A : ArcPresentation c),
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.Refines A → Q.MeshLT δ →
    ∀ θ : AngleChoices o A,
      totalTurning θ = PolygonTurning.totalTurning o (polygon c Q)

/-- The full uniform comparison: one threshold works for every knot-preserving
refinement, for arbitrary orientation and independent continuous arc angles.
The polygon circuit and the homotopy are conclusions. Noncuspidality is
retained at every new vertex, including the cyclic closing vertex. -/
def comparison : Prop := ∀ (c : RegularJordanCurve)
  (o : Orientation ℝ Plane (Fin 2)) (A : ArcPresentation c),
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.Refines A → Q.MeshLT δ →
    PolygonTurning.Noncuspidal (polygon c Q) ∧
    ∃ P : PolygonCircuit o c Q,
      (∀ T : TangentCircuit o A,
        Nonempty (UnitDirectionHomotopy T.toUnitLoop P.toUnitDirectionLoop) ∧
        T.winding = winding o P.toUnitDirectionLoop) ∧
      ∀ θ : AngleChoices o A,
        totalTurning θ = PolygonTurning.totalTurning o (polygon c Q)

end Expected
end P202Specs.PlaneTangentComparison
