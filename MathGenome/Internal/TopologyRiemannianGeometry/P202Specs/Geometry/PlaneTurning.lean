import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneInscribedPolygons
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneTangentComparison

/-!
Independent final statements for paper.tex 4831–4917,
lem:p202-plane-turning. The curve, positive smooth presentations, arbitrary
continuous tangent-angle choices, actual short-rotation tangent circuits,
and their winding are the shared objects from PlaneTurningData.
No decomposition, polygon, lift, or winding certificate is assumed of a curve.
-/
noncomputable section
open Set
open scoped unitInterval

namespace P202Specs.PlaneTurning
open PlanarRegionTopology (Plane RegularJordanCurve)

namespace Expected

/-- Complete signed turning theorem for every presentation and every lift.
Decomposition and lift existence are unconditional results in PlaneTurningData. -/
def turning : Prop := ∀ (c : RegularJordanCurve) (o : Orientation ℝ Plane (Fin 2))
  (U : Set Plane), IsBoundedSide c U → HasBoundedSideOnLeft c o U →
  ∀ (A : ArcPresentation c) (θ : AngleChoices o A),
    totalTurning θ = 2 * Real.pi ∧ reversedTotalTurning θ = -(2 * Real.pi) ∧
    ∀ ψ : Fin A.count → C(unitInterval, ℝ), LiftsReversed o A ψ →
      reversedTurningWith o A ψ = -(2 * Real.pi)

/-- A common mesh preserves simplicity, the actual bounded-left side,
and the unit-circle homotopy class, for every knot-preserving partition.
The polygon vertices are literal samples of the original curve. -/
def positiveInscribedApproximation : Prop :=
  ∀ (c : RegularJordanCurve) (o : Orientation ℝ Plane (Fin 2)) (U : Set Plane),
    IsBoundedSide c U → HasBoundedSideOnLeft c o U →
    ∀ A : ArcPresentation c, ∃ δ : ℝ, 0 < δ ∧
      ∀ Q : Partition, Q.Refines A → Q.MeshLT δ →
        PolygonTurning.IsSimple (inscribedPolygon c Q) ∧
        PolygonTurning.Noncuspidal (inscribedPolygon c Q) ∧
        (∃ UQ : Set Plane,
          PolygonTurning.IsBoundedSide (inscribedPolygon c Q) UQ ∧
          PolygonTurning.HasBoundedSideOnLeft o (inscribedPolygon c Q) UQ) ∧
        ∃ P : PolygonCircuit o c Q,
          (∀ T : TangentCircuit o A,
            Nonempty (UnitDirectionHomotopy T.toUnitLoop P.toUnitDirectionLoop) ∧
            T.winding = PlaneTangentComparison.winding o P.toUnitDirectionLoop) ∧
          ∀ θ : AngleChoices o A,
            totalTurning θ = PolygonTurning.totalTurning o (inscribedPolygon c Q)

/-- The full boundary theorem includes decomposition, angle and circuit
existence, both signed turning sums for arbitrary angle choices, and the
actual winding and lift formula for every inserted unit-tangent circuit. -/
def boundaryTurning : Prop :=
  ∀ (c : RegularJordanCurve) (o : Orientation ℝ Plane (Fin 2)) (U : Set Plane),
    IsBoundedSide c U → HasBoundedSideOnLeft c o U →
    Nonempty (ArcPresentation c) ∧
    ∀ A : ArcPresentation c,
      Nonempty (AngleChoices o A) ∧ Nonempty (TangentCircuit o A) ∧
      (∀ θ : AngleChoices o A,
        totalTurning θ = 2 * Real.pi ∧
        reversedTotalTurning θ = -(2 * Real.pi) ∧
        ∀ ψ : Fin A.count → C(unitInterval, ℝ), LiftsReversed o A ψ →
          reversedTurningWith o A ψ = -(2 * Real.pi)) ∧
      ∀ T : TangentCircuit o A,
        (∃ L : C(unitInterval, ℝ), IsCircuitLift T L) ∧ T.winding = 1 ∧
        ∀ (θ : AngleChoices o A) (L : C(unitInterval, ℝ)), IsCircuitLift T L →
          totalTurning θ = L 1 - L 0 ∧
          L 1 - L 0 = 2 * Real.pi * (T.winding : ℝ) ∧
          L 1 - L 0 = 2 * Real.pi

end Expected
end P202Specs.PlaneTurning
