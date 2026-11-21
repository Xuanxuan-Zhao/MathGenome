import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
The geometric data for paper.tex:4478--4482.  These definitions are independent
of the implementation.  In particular, no field-closure or quadratic-tower
property is assumed of the constructible points.
-/

namespace D07.Ch15.StraightedgeCompass

/-- Cartesian real coordinates, with both coordinates retained. -/
abbrev Point := ℝ × ℝ

def origin : Point := (0, 0)

def unitPoint : Point := (1, 0)

/-- The paper's finite initial set, with the prescribed origin and unit segment.
The other initial coordinates need not be rational or algebraic. -/
structure InitialData where
  points : Set Point
  finite_points : points.Finite
  origin_mem : origin ∈ points
  unitPoint_mem : unitPoint ∈ points

/-- Squared Euclidean distance.  Equality of these quantities is precisely
equality of the nonnegative Euclidean distances. -/
def squaredDistance (a b : Point) : ℝ :=
  (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2

/-- A line is specified by two points, and a circle by its center and two
points specifying its radius.  The radius points may be unrelated to the
center.  Availability and nondegeneracy are imposed by `Curve.Available`. -/
inductive Curve where
  | line (a b : Point)
  | circle (center radiusStart radiusEnd : Point)

/-- The full line or circle, rather than a segment, disk, or chosen branch. -/
def Curve.locus : Curve → Set Point
  | .line a b =>
      {p | (b.1 - a.1) * (p.2 - a.2) = (b.2 - a.2) * (p.1 - a.1)}
  | .circle c a b => {p | squaredDistance p c = squaredDistance a b}

/-- Exactly the curves drawable with the unmarked straightedge and compass
from the currently available points.  No third point or marked ruler may be
used to specify a line.  Zero-radius circles are not arbitrarily excluded. -/
def Curve.Available (S : Set Point) : Curve → Prop
  | .line a b => a ∈ S ∧ b ∈ S ∧ a ≠ b
  | .circle c a b => c ∈ S ∧ a ∈ S ∧ b ∈ S

/-- One permitted selection.  Inequality of loci excludes coincident curves
even when their descriptions differ.  Every member of the finite intersection
is eligible, including a tangent intersection. -/
def IntersectionStep (S : Set Point) (p : Point) : Prop :=
  ∃ c d : Curve,
    c.Available S ∧ d.Available S ∧ c.locus ≠ d.locus ∧
      (c.locus ∩ d.locus).Finite ∧ p ∈ c.locus ∩ d.locus

/-- A finite history of point selections.  The only base case is the given
initial set; each successor retains all old points and adds one selected
intersection.  Thus axes, projections, and arithmetic operations are not
additional primitives. -/
inductive Construction (P : InitialData) : Set Point → Prop where
  | initial : Construction P P.points
  | step {S : Set Point} {p : Point} :
      Construction P S → IntersectionStep S p → Construction P (insert p S)

/-- The horizontal direction fixed by the initial origin and unit point. -/
def horizontalAxis : Curve := .line origin unitPoint

/-- The perpendicular to the horizontal direction through the origin.  This
is a reference locus for the coordinate frame, not a freely drawable curve:
any use of it in a history must still satisfy `Curve.Available`.  Its
straightedge-and-compass construction belongs to the geometric-operations
lemma immediately following this definition in the paper. -/
def verticalAxis : Set Point :=
  {p | (unitPoint.1 - origin.1) * (p.1 - origin.1) +
    (unitPoint.2 - origin.2) * (p.2 - origin.2) = 0}

end D07.Ch15.StraightedgeCompass

namespace Specs.D07.Ch15.ConstructibleDefinition

open D07.Ch15.StraightedgeCompass

/-- Type and value of the real coordinate field Q(x,y : (x,y) ∈ P). -/
def coordinateFieldType : Type := InitialData → IntermediateField ℚ ℝ

noncomputable def coordinateFieldValue : coordinateFieldType := fun P =>
  IntermediateField.adjoin ℚ (Prod.fst '' P.points ∪ Prod.snd '' P.points)

/-- Type and value of the geometric point-constructibility predicate. -/
def isConstructibleType : Type := InitialData → Point → Prop

def isConstructibleValue : isConstructibleType := fun P p =>
  ∃ S : Set Point, Construction P S ∧ p ∈ S

/-- A real number is represented on the horizontal coordinate axis. -/
def isConstructibleRealType : Type := InitialData → ℝ → Prop

def isConstructibleRealValue : isConstructibleRealType := fun P a =>
  ∃ S : Set Point, Construction P S ∧ (a, 0) ∈ S

end Specs.D07.Ch15.ConstructibleDefinition
