import MathGenome.Internal.Specs.D07.Ch15.DegreeObstruction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Independent statements for K07.15.trisect_angle, paper.tex:4552–4562.
Angles are measured in radians. An angle is constructed by producing a point
on its positive ray from the given origin, with the unit segment fixing the
initial ray. The radius is arbitrary and positive; unit normalization is a
conclusion, not a premise about available points. All point constructions use
the original finite intersection histories. Rational initial data may include
any finite set of rational-coordinate points, not just the unit endpoints.
-/
namespace D07.Ch15.TrisectAngle
open StraightedgeCompass
open Specs.D07.Ch15.ConstructibleDefinition

/-- Ordinary rational initial data, retaining both coordinates. -/
def RationalInitialData (P : InitialData) : Prop :=
  ∀ p ∈ P.points, ∃ x y : ℚ, p = ((x : ℝ), (y : ℝ))

/-- Constructing a ray, with no supplied point on that ray assumed. -/
def AngleConstructible (P : InitialData) (θ : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ isConstructibleValue P (r * Real.cos θ, r * Real.sin θ)

/-- The specific cubic for twice the cosine of twenty degrees. -/
noncomputable def trisectionCubic : Polynomial ℚ :=
  Polynomial.X ^ 3 - Polynomial.C 3 * Polynomial.X - 1

end D07.Ch15.TrisectAngle

namespace Specs.D07.Ch15.TrisectAngle
open _root_.D07.Ch15.StraightedgeCompass _root_.D07.Ch15.TrisectAngle
open Specs.D07.Ch15.ConstructibleDefinition
open IntermediateField

/-- Arbitrary positive ray representatives and normalized directions agree. -/
def NormalizeRay : Prop := ∀ (P : InitialData) (θ : ℝ),
  AngleConstructible P θ ↔ isConstructibleValue P (Real.cos θ, Real.sin θ)

/-- Sixty degrees is itself constructible from the unit segment. -/
def ConstructibleSixty : Prop := ∀ P : InitialData,
  AngleConstructible P (Real.pi / 3)

/-- The concrete algebraic obstruction used in the source. -/
def TwentyDegree : Prop :=
  IsIntegral ℚ (2 * Real.cos (Real.pi / 9)) ∧
  minpoly ℚ (2 * Real.cos (Real.pi / 9)) = trisectionCubic ∧
  Module.finrank ℚ ℚ⟮2 * Real.cos (Real.pi / 9)⟯ = 3

/-- No permitted finite construction produces the trisection of sixty degrees. -/
def NoTrisectionSixty : Prop := ∀ P : InitialData,
  RationalInitialData P → ¬ AngleConstructible P ((Real.pi / 3) / 3)

/-- Supplying any finite collection of already constructible points as
input does not enable trisection. In particular this allows the constructed
sixty-degree input ray itself to be supplied to a putative procedure. -/
def NoTrisectionFromConstructibleData : Prop := ∀ P Q : InitialData,
  RationalInitialData P →
  (∀ p ∈ Q.points, isConstructibleValue P p) →
  ¬ AngleConstructible Q ((Real.pi / 3) / 3)

/-- The result does not exclude trisection of individual angles: the straight
angle has a constructible trisection at sixty degrees. -/
def StraightAngleTrisectable : Prop := ∀ P : InitialData,
  AngleConstructible P Real.pi ∧ AngleConstructible P (Real.pi / 3)

/-- A universal procedure would in particular work for every already
constructible input angle between zero and a straight angle. Even this
restricted universal existence statement fails. -/
def NoUniversalTrisection : Prop := ∀ P : InitialData,
  RationalInitialData P →
  ¬ (∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
    AngleConstructible P θ → AngleConstructible P (θ / 3))

end Specs.D07.Ch15.TrisectAngle
