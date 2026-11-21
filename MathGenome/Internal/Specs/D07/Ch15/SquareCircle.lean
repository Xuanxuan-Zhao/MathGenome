import MathGenome.Internal.Specs.D07.Ch15.ConstructibleDefinition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.Algebraic.Defs

/-!
Independent statements for K07.15.square_circle, paper.tex:4560–4568.
The initial data retain the finite set, origin and unit point from the shared
geometric definition. Rationality is required of both coordinates of every
initial point, using the canonical embedding Q → R.

A square on an edge with endpoints a,b has area squaredDistance a b; the
unit-radius circle has area Real.pi. The final statement excludes even two
constructible points whose squared distance is pi, and thus applies to a
square in any position and orientation. It does not require a particular
axis-aligned output or add arithmetic operations to the construction rules.
-/

namespace Specs.D07.Ch15.SquareCircle

open D07.Ch15.StraightedgeCompass
open Specs.D07.Ch15.ConstructibleDefinition

/-- Every initial coordinate is rational; extra rational points are allowed. -/
def RationalInitialCoordinates (P : InitialData) : Prop :=
  ∀ p ∈ P.points, ∃ x y : ℚ, p = ((x : ℝ), (y : ℝ))

def ConstructibleRealAlgebraic : Prop :=
  ∀ (P : InitialData), RationalInitialCoordinates P →
    ∀ a : ℝ, isConstructibleRealValue P a → IsAlgebraic ℚ a

def SqrtPiNotConstructible : Prop :=
  ∀ (P : InitialData), RationalInitialCoordinates P →
    ¬ isConstructibleRealValue P (Real.sqrt Real.pi)

/-- No constructible side length, including any positive side of a square,
has square equal to the area of the unit circle. -/
def NoConstructibleSide : Prop :=
  ∀ (P : InitialData), RationalInitialCoordinates P →
    ∀ s : ℝ, isConstructibleRealValue P s → s ^ 2 ≠ Real.pi

/-- The geometric impossibility, with arbitrary constructible edge endpoints. -/
def NoSquareCircle : Prop :=
  ∀ (P : InitialData), RationalInitialCoordinates P →
    ¬ ∃ a b : Point,
      isConstructibleValue P a ∧ isConstructibleValue P b ∧
        squaredDistance a b = Real.pi

end Specs.D07.Ch15.SquareCircle
