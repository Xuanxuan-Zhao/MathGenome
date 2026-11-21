import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Independent single-step assertions from W73 (paper.tex:2754–2778).
`U` is an arbitrary open neighborhood of the closed radius-`R` interval.
There is no hypothesis about the location of the next Newton point. -/
namespace Specs.NumAnalysis206.Newton.ScalarError
open Set

/-- Differentiability and nonzero denominator, followed by the quadratic estimate. -/
def stepError : Prop :=
  ∀ (f : ℝ → ℝ) (p R m M : ℝ) (U : Set ℝ),
    0 < R → IsOpen U → Icc (p - R) (p + R) ⊆ U →
    ContDiffOn ℝ 2 f U → f p = 0 → 0 < m →
    (∀ t ∈ Icc (p - R) (p + R), m ≤ |deriv f t|) →
    (∀ t ∈ Icc (p - R) (p + R), |deriv (deriv f) t| ≤ M) →
    ∀ x ∈ Icc (p - R) (p + R),
      scalarStepValidValue f x ∧
      |scalarNewtonValue f x - p| ≤ M * |x - p| ^ 2 / (2 * m)

/-- The absorbing, successfully stopped update obeys the same estimate. -/
def stoppedStepError : Prop :=
  ∀ (f : ℝ → ℝ) (p R m M : ℝ) (U : Set ℝ),
    0 < R → IsOpen U → Icc (p - R) (p + R) ⊆ U →
    ContDiffOn ℝ 2 f U → f p = 0 → 0 < m →
    (∀ t ∈ Icc (p - R) (p + R), m ≤ |deriv f t|) →
    (∀ t ∈ Icc (p - R) (p + R), |deriv (deriv f) t| ≤ M) →
    ∀ x ∈ Icc (p - R) (p + R),
      stoppedStepValidValue f (scalarStepValidValue f) x ∧
      |stopAtRootValue f (scalarNewtonValue f) x - p| ≤
        M * |x - p| ^ 2 / (2 * m)

/-- Zero curvature makes one exact step reach the specified root, also with stopping. -/
def zeroCurvature : Prop :=
  ∀ (f : ℝ → ℝ) (p R m : ℝ) (U : Set ℝ),
    0 < R → IsOpen U → Icc (p - R) (p + R) ⊆ U →
    ContDiffOn ℝ 2 f U → f p = 0 → 0 < m →
    (∀ t ∈ Icc (p - R) (p + R), m ≤ |deriv f t|) →
    (∀ t ∈ Icc (p - R) (p + R), |deriv (deriv f) t| ≤ 0) →
    ∀ x ∈ Icc (p - R) (p + R),
      scalarNewtonValue f x = p ∧ stopAtRootValue f (scalarNewtonValue f) x = p

end Specs.NumAnalysis206.Newton.ScalarError
