import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.ScalarError

/-! Independent statement of W73, paper.tex:2754–2781.
The only hypotheses on a run are its initial error and the prescribed Newton
construction. Invariance, valid derivatives, and convergence are conclusions.
The canonical stopped construction has the exact unstopped Newton recurrence,
including at a root. -/
namespace Specs.NumAnalysis206.Newton.ScalarConvergence
open Set Filter

/-- Local quadratic convergence, with a geometric majorant, zero-curvature
termination, and absorption of any root reached along the run. -/
def localConvergence : Prop :=
  ∀ (f : ℝ → ℝ) (p R m M : ℝ) (U : Set ℝ),
    0 < R → IsOpen U → Icc (p - R) (p + R) ⊆ U →
    ContDiffOn ℝ 2 f U → f p = 0 → 0 < m →
    (∀ t ∈ Icc (p - R) (p + R), m ≤ |deriv f t|) →
    (∀ t ∈ Icc (p - R) (p + R), |deriv (deriv f) t| ≤ M) →
    ∀ (r x₀ : ℝ), 0 < r → r ≤ R → M * r / (2 * m) < 1 →
    |x₀ - p| ≤ r →
    let x := scalarNewtonIteratesValue f x₀
    (∀ n : ℕ,
      x n ∈ Icc (p - r) (p + r) ∧
      scalarStepValidValue f (x n) ∧
      x (n + 1) = scalarNewtonValue f (x n) ∧
      |x (n + 1) - p| ≤ M * |x n - p| ^ 2 / (2 * m) ∧
      |x n - p| ≤ (M * r / (2 * m)) ^ n * |x₀ - p|) ∧
    Tendsto x atTop (nhds p) ∧
    (M = 0 → ∀ n : ℕ, x (n + 1) = p) ∧
    (∀ N : ℕ, f (x N) = 0 → ∀ k : ℕ, x (N + k) = x N)

end Specs.NumAnalysis206.Newton.ScalarConvergence
