import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-! Independent statements for paper.tex, `fa2:p1:quadratic-seminorm`.
The first three statements use only a real vector space. The last statement
uses its given norm, and the unit-sphere midpoint definition of rotundity.
No nontriviality or completeness assumption is imposed. -/

universe u

namespace ExpandedFA.Asplund.QuadraticSeminormsSpec

/-- A real-valued (hence finite), nonnegative, convex, two-homogeneous function. -/
def NonnegativeQuadraticConvex {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : E → ℝ) : Prop :=
  (∀ x, 0 ≤ q x) ∧ ConvexOn ℝ Set.univ q ∧
    ∀ (a : ℝ) (x : E), q (a • x) = a ^ 2 * q x

/-- Characterization by squares of real seminorms, in both directions. -/
def SquareSeminormCharacterization : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℝ E] (q : E → ℝ),
    NonnegativeQuadraticConvex q ↔ ∃ p : Seminorm ℝ E, ∀ x, q x = (p x) ^ 2

/-- The first estimate, for every interior weight. -/
def WeightedSumEstimate : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℝ E] (q : E → ℝ),
    NonnegativeQuadraticConvex q → ∀ (x y : E) (t : ℝ), 0 < t → t < 1 →
      q (x + y) ≤ q x / t + q y / (1 - t)

/-- The second estimate, retaining the constant four and every interior weight. -/
def WeightedDifferenceEstimate : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℝ E] (q : E → ℝ),
    NonnegativeQuadraticConvex q → ∀ (x y : E) (t : ℝ), 0 < t → t < 1 →
      4 * q x ≤ q (x + y) / t + q (x - y) / (1 - t)

/-- Strict convexity on the unit sphere means that distinct unit vectors have
midpoint of norm less than one. This is vacuous on the zero space. -/
def UnitSphereStrictConvex {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ (x y : E), ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y → ‖(1 / 2 : ℝ) • (x + y)‖ < 1

/-- Equivalence of unit-sphere rotundity and strict convexity of the squared norm. -/
def StrictConvexSquareEquivalence : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E],
    UnitSphereStrictConvex (E := E) ↔
      StrictConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ 2)

end ExpandedFA.Asplund.QuadraticSeminormsSpec
