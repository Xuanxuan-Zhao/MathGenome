import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Orbits

/-! Independent specification for paper.tex, d13:13:nullclines and the
Chapter 13 standing convention on transverse segments. The plane uses its
usual real coordinates. All zero sets are relative to the actual open domain;
the zero-extension convention outside that domain creates no equilibria.
No invariance of a coordinate nullcline is imposed. -/
noncomputable section
open Set

namespace D13Unified.Ch13.Nullclines

abbrev Plane := ℝ × ℝ

/-- A nondegenerate centered straight segment, with a chosen direction. -/
structure StraightSegment where
  center : Plane
  direction : Plane
  radius : ℝ
  radius_pos : 0 < radius
  direction_ne_zero : direction ≠ 0

end D13Unified.Ch13.Nullclines

namespace Specs.D13Unified.Ch13.Nullclines
open _root_.D13Unified _root_.D13Unified.Ch13.Nullclines
open Ch01.AutonomousParameters
open _root_.D13Unified.Ch06.StateDerivative

/-- First coordinate nullcline, relative to Ω. -/
def nullclineXValue (F : AutonomousODE Plane) : Set Plane :=
  {p | p ∈ F.domain ∧ (autonomousEvalValue F p).1 = 0}

/-- Second coordinate nullcline, relative to Ω. -/
def nullclineYValue (F : AutonomousODE Plane) : Set Plane :=
  {p | p ∈ F.domain ∧ (autonomousEvalValue F p).2 = 0}

/-- `true` chooses the positive sign, `false` the negative sign, in each
coordinate. Thus the four Boolean pairs are the four open tangent quadrants. -/
def openQuadrantValue (sx sy : Bool) : Set Plane :=
  {v | (if sx then 0 < v.1 else v.1 < 0) ∧
       (if sy then 0 < v.2 else v.2 < 0)}

def phaseRegionValue (F : AutonomousODE Plane) (sx sy : Bool) : Set Plane :=
  F.domain ∩ autonomousEvalValue F ⁻¹' openQuadrantValue sx sy

/-- The parameter runs from `-radius` to `radius` in the chosen direction. -/
def segmentPointValue (S : StraightSegment) (u : ℝ) : Plane :=
  S.center + u • S.direction

def segmentCarrierValue (S : StraightSegment) : Set Plane :=
  segmentPointValue S '' Icc (-S.radius) S.radius

/-- A fixed affine real coordinate, defined on the ambient plane. Its
restriction to the supporting line takes `center + u • direction` to `u`. -/
def segmentCoordinateValue (S : StraightSegment) (p : Plane) : ℝ :=
  ((p.1 - S.center.1) * S.direction.1 +
   (p.2 - S.center.2) * S.direction.2) /
    (S.direction.1 ^ 2 + S.direction.2 ^ 2)

/-- Dot product of the field with the chosen left normal `(-d₂,d₁)`.
Normalization is immaterial to nonvanishing. -/
def normalComponentValue (F : AutonomousODE Plane) (S : StraightSegment)
    (p : Plane) : ℝ :=
  S.direction.1 * (autonomousEvalValue F p).2 -
  S.direction.2 * (autonomousEvalValue F p).1

/-- Shortness is implemented by restricting the radius until every point
is admissible and the normal component is nowhere zero, including endpoints. -/
def isTransverseValue (F : AutonomousODE Plane) (S : StraightSegment) : Prop :=
  segmentCarrierValue S ⊆ F.domain ∧
  ∀ p ∈ segmentCarrierValue S, normalComponentValue F S p ≠ 0

end Specs.D13Unified.Ch13.Nullclines

namespace D13Unified.Ch13.Nullclines
/-- Carries its affine ordering data as well as transversality. -/
structure TransverseSegment (F : AutonomousODE Plane) extends StraightSegment where
  transverse : Specs.D13Unified.Ch13.Nullclines.isTransverseValue F toStraightSegment
end D13Unified.Ch13.Nullclines

namespace Specs.D13Unified.Ch13.Nullclines
open _root_.D13Unified _root_.D13Unified.Ch13.Nullclines
open Ch01.AutonomousParameters
open _root_.D13Unified.Ch06.StateDerivative

def NullclineType := AutonomousODE Plane → Set Plane

def OpenQuadrantType := Bool → Bool → Set Plane

def PhaseRegionType := AutonomousODE Plane → Bool → Bool → Set Plane

def SegmentPointType := StraightSegment → ℝ → Plane

def SegmentCarrierType := StraightSegment → Set Plane

def SegmentCoordinateType := StraightSegment → Plane → ℝ

def NormalComponentType := AutonomousODE Plane → StraightSegment → Plane → ℝ

def IsTransverseType := AutonomousODE Plane → StraightSegment → Prop

def EquilibriaIntersection : Prop :=
  ∀ F : AutonomousODE Plane,
    {p | p ∈ F.domain ∧ autonomousEvalValue F p = 0} =
      nullclineXValue F ∩ nullclineYValue F

/-- Links the algebraic characterization to the accepted orbit notion. -/
def ConstantIffIntersection : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, _root_.D13Unified.Ch11.Orbits.IsConstant F p ↔
      p ∈ nullclineXValue F ∩ nullclineYValue F

/-- This holds for every classical solution, not just the selected maximal one. -/
def TrajectoryTangent : Prop :=
  ∀ (F : AutonomousODE Plane) (I : OpenTimeInterval) (x : ℝ → Plane),
    classicalAutonomousSolutionOnValue F I x →
    ∀ t ∈ I.carrier, deriv x t = autonomousEvalValue F (x t)

def TangentQuadrant : Prop :=
  ∀ (F : AutonomousODE Plane) (I : OpenTimeInterval) (x : ℝ → Plane),
    classicalAutonomousSolutionOnValue F I x →
    ∀ t ∈ I.carrier, ∀ sx sy : Bool,
      deriv x t ∈ openQuadrantValue sx sy ↔ x t ∈ phaseRegionValue F sx sy

/-- Off both zero sets there is precisely one of the four open quadrants. -/
def UniqueTangentQuadrant : Prop :=
  ∀ (F : AutonomousODE Plane) (I : OpenTimeInterval) (x : ℝ → Plane),
    classicalAutonomousSolutionOnValue F I x →
    ∀ t ∈ I.carrier, x t ∉ nullclineXValue F → x t ∉ nullclineYValue F →
      (∃! s : Bool × Bool, deriv x t ∈ openQuadrantValue s.1 s.2) ∧ deriv x t ≠ 0

def VerticalTangent : Prop :=
  ∀ (F : AutonomousODE Plane) (I : OpenTimeInterval) (x : ℝ → Plane),
    classicalAutonomousSolutionOnValue F I x →
    ∀ t ∈ I.carrier, x t ∈ nullclineXValue F \ nullclineYValue F →
      deriv x t = (0, (autonomousEvalValue F (x t)).2) ∧
      (deriv x t).2 ≠ 0 ∧ deriv x t ≠ 0

def HorizontalTangent : Prop :=
  ∀ (F : AutonomousODE Plane) (I : OpenTimeInterval) (x : ℝ → Plane),
    classicalAutonomousSolutionOnValue F I x →
    ∀ t ∈ I.carrier, x t ∈ nullclineYValue F \ nullclineXValue F →
      deriv x t = ((autonomousEvalValue F (x t)).1, 0) ∧
      (deriv x t).1 ≠ 0 ∧ deriv x t ≠ 0

/-- The same derivative identity for the actual canonical maximal flow. -/
def FlowTangent : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, ∀ t ∈ (flowInterval F p).carrier,
      deriv (fun r => flow F r p) t = autonomousEvalValue F (flow F t p)

def CoordinatePoint : Prop :=
  ∀ (S : StraightSegment) (u : ℝ),
    segmentCoordinateValue S (segmentPointValue S u) = u

def CoordinateOrder : Prop :=
  ∀ (S : StraightSegment) (u v : ℝ),
    segmentCoordinateValue S (segmentPointValue S u) <
      segmentCoordinateValue S (segmentPointValue S v) ↔ u < v

def SegmentParametrization : Prop :=
  ∀ (S : StraightSegment) (p : Plane), p ∈ segmentCarrierValue S ↔
    ∃! u : ℝ, u ∈ Icc (-S.radius) S.radius ∧ segmentPointValue S u = p

/-- Every regular point has a straight transverse segment with arbitrarily
small positive radius. No global flow or invariance is assumed. -/
def SmallTransverseSegment : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, autonomousEvalValue F p ≠ 0 →
    ∀ R : ℝ, 0 < R → ∃ S : TransverseSegment F, S.center = p ∧ S.radius < R

end Specs.D13Unified.Ch13.Nullclines
