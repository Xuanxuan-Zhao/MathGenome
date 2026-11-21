import MathGenome.Internal.Specs.D07.Ch15.ConstructibleDefinition
import Mathlib.Analysis.Real.Sqrt
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! Coordinate calculations for the necessity direction of paper.tex:4501.
All subfields and simple extensions use their actual inclusions in ℝ.
No algebraicity of the initial coordinates or of the ambient real field is assumed.
-/

namespace D07.Ch15.StraightedgeCompass

def HasCoordinates (M : IntermediateField ℚ ℝ) (p : Point) : Prop :=
  p.1 ∈ M ∧ p.2 ∈ M

noncomputable def sqrtExtension (M : IntermediateField ℚ ℝ) (d : M) :
    IntermediateField M ℝ := IntermediateField.adjoin M {Real.sqrt (d : ℝ)}

/-- Finiteness is explicit, so the natural finrank cannot mean its infinite
dimensional fallback value. Both coordinates use the same chosen radicand. -/
def InQuadraticExtension (M : IntermediateField ℚ ℝ) (p : Point) : Prop :=
  ∃ d : M, 0 ≤ (d : ℝ) ∧
    FiniteDimensional M (sqrtExtension M d) ∧
    Module.finrank M (sqrtExtension M d) ≤ 2 ∧
    p.1 ∈ sqrtExtension M d ∧ p.2 ∈ sqrtExtension M d

end D07.Ch15.StraightedgeCompass

namespace Specs.D07.Ch15.QuadraticTowerIffIntersectionCoordinates

open D07.Ch15.StraightedgeCompass

def LineEquation : Prop :=
  ∀ (M : IntermediateField ℚ ℝ) (a b : Point),
    HasCoordinates M a → HasCoordinates M b → a ≠ b →
    ∃ A B C : M, (A ≠ 0 ∨ B ≠ 0) ∧
      ∀ p : Point, p ∈ (Curve.line a b).locus ↔
        (A : ℝ) * p.1 + (B : ℝ) * p.2 + (C : ℝ) = 0

def CircleEquation : Prop :=
  ∀ (M : IntermediateField ℚ ℝ) (c a b : Point),
    HasCoordinates M c → HasCoordinates M a → HasCoordinates M b →
    ∃ D E F : M, ∀ p : Point,
      p ∈ (Curve.circle c a b).locus ↔
        p.1 ^ 2 + p.2 ^ 2 + (D : ℝ) * p.1 + (E : ℝ) * p.2 + (F : ℝ) = 0

def NonparallelLines : Prop :=
  ∀ (M : IntermediateField ℚ ℝ) (a b c d p : Point),
    HasCoordinates M a → HasCoordinates M b →
    HasCoordinates M c → HasCoordinates M d →
    (b.1 - a.1) * (d.2 - c.2) - (b.2 - a.2) * (d.1 - c.1) ≠ 0 →
    p ∈ (Curve.line a b).locus → p ∈ (Curve.line c d).locus →
    HasCoordinates M p

/-- The vanishing discriminant (tangent case) already has coordinates in M.
The premise uses squared radius r; it does not assume its square root in M. -/
def TangentLineCircle : Prop :=
  ∀ (M : IntermediateField ℚ ℝ) (A B C cx cy r : M) (p : Point),
    (A ≠ 0 ∨ B ≠ 0) →
    (A : ℝ) * p.1 + (B : ℝ) * p.2 + (C : ℝ) = 0 →
    (p.1 - (cx : ℝ)) ^ 2 + (p.2 - (cy : ℝ)) ^ 2 = (r : ℝ) →
    (A ^ 2 + B ^ 2) * r - (A * cx + B * cy + C) ^ 2 = 0 →
    HasCoordinates M p

/-- This proves the assertion for every selected intersection in the shared
geometric interface, including tangencies and zero-radius circles. -/
def IntersectionCoordinates : Prop :=
  ∀ (M : IntermediateField ℚ ℝ) (S : Set Point) (p : Point),
    (∀ q ∈ S, HasCoordinates M q) → IntersectionStep S p →
    InQuadraticExtension M p

def ConcentricCirclesDisjoint : Prop :=
  ∀ (c a b d e : Point), squaredDistance a b ≠ squaredDistance d e →
    Disjoint (Curve.circle c a b).locus (Curve.circle c d e).locus

/-- The zero radicand used in a tangent/linear step gives no extension. -/
def ZeroRadicand : Prop :=
  ∀ M : IntermediateField ℚ ℝ, sqrtExtension M 0 = ⊥

end Specs.D07.Ch15.QuadraticTowerIffIntersectionCoordinates
