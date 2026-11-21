import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

/-! Independent statements for the estimates and continuity clause of
`paper.tex`, fa2:p4:bochner-positive, lines 18637–18652. -/

namespace ExpandedFA.PartIV.PositiveDefiniteContinuity.Spec

/-- All finite scalar quadratic sums are nonnegative real numbers. Repeated
points and empty families are allowed. No continuity is included. -/
def PositiveDefinite {G : Type*} [AddGroup G] (φ : G → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G) (a : Fin n → ℂ),
    (∑ j, ∑ k, starRingEnd ℂ (a j) * a k * φ (x k - x j)).im = 0 ∧
    0 ≤ (∑ j, ∑ k, starRingEnd ℂ (a j) * a k * φ (x k - x j)).re

def Estimates : Prop :=
  ∀ (d : ℕ) (φ : EuclideanSpace ℝ (Fin d) → ℂ), PositiveDefinite φ →
    (φ 0).im = 0 ∧ 0 ≤ (φ 0).re ∧
    (∀ x, ‖φ x‖ ≤ (φ 0).re) ∧
    ∀ x h, ‖φ (x + h) - φ x‖ ^ 2 ≤
      2 * (φ 0).re * ((φ 0).re - (φ h).re)

def Continuity : Prop :=
  ∀ (d : ℕ) (φ : EuclideanSpace ℝ (Fin d) → ℂ), PositiveDefinite φ →
    ContinuousAt φ 0 → UniformContinuous φ

/-- The degenerate case is included in both results above, and also made explicit. -/
def ZeroCase : Prop :=
  ∀ (d : ℕ) (φ : EuclideanSpace ℝ (Fin d) → ℂ), PositiveDefinite φ →
    φ 0 = 0 → φ = 0

end ExpandedFA.PartIV.PositiveDefiniteContinuity.Spec
