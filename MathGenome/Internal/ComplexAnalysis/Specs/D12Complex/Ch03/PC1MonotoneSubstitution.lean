import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory Set

namespace D12Complex.Ch03.PC1MonotoneSubstitution.Specs

/-- Weighted substitution on a continuous nondecreasing piecewise C¹ parameter interval.
The finite partition is strict in the source, but its image may have repeated nodes.
The case `n = 0` represents a degenerate interval. No continuity of `g` is required. -/
def weighted_substitution_type : Prop :=
  ∀ (φ : ℝ → ℝ) (c d : ℝ) (n : ℕ) (node : Fin (n + 1) → ℝ),
    c ≤ d →
    ContinuousOn φ (Icc c d) →
    MonotoneOn φ (Icc c d) →
    StrictMono node →
    node 0 = c →
    node (Fin.last n) = d →
    (∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ))) →
    ∀ g : ℝ → ℂ, IntervalIntegrable g volume (φ c) (φ d) →
      IntervalIntegrable (fun t => deriv φ t • g (φ t)) volume c d ∧
      (∫ t in c..d, deriv φ t • g (φ t)) = ∫ s in φ c..φ d, g s

end D12Complex.Ch03.PC1MonotoneSubstitution.Specs
