import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.MultipleExpansion

/-! W74: local convergence with the specified multiplicity, successful root
stopping, and the asymptotic error ratio for every nonterminating ordinary run.
All assumptions concern the original local factorization, not the iterates. -/

open Filter Topology
namespace Specs.NumAnalysis206.Newton

/-- Conclusions for every exact run of a stopped scalar method. The geometric
bound implies invariance; validity is required only when a division is used. -/
def localMultipleRootRuns (f : ℝ → ℝ) (p r q : ℝ) (step : ℝ → ℝ) : Prop :=
  ∀ (x₀ : ℝ) (x : ℕ → ℝ), |x₀ - p| < r →
    IsExactRunValue (stopAtRootValue f step) x₀ x →
    (∀ n, |x n - p| ≤ q ^ n * |x₀ - p| ∧ |x n - p| < r ∧
      stoppedStepValidValue f (scalarStepValidValue f) (x n)) ∧
    Tendsto x atTop (𝓝 p) ∧
    (∀ N, x N = p → ∀ k, x (N + k) = p)

/-- Both Newton methods converge from one common neighborhood. The ordinary
error retains its linear term and quadratic remainder, the corrected method
retains its quadratic bound, and all non-root denominators are nonzero.
The ratio assertion is restricted to runs whose errors never vanish. -/
def multipleRootConvergence : Prop :=
  ∀ (f g : ℝ → ℝ) (p : ℝ) (m : ℕ), 2 ≤ m →
    ContDiffAt ℝ 2 g p → g p ≠ 0 →
    f =ᶠ[𝓝 p] (fun x => (x - p) ^ m * g x) →
    ∃ r C q : ℝ, 0 < r ∧ 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧ f p = 0 ∧
      (∀ x : ℝ, |x - p| < r →
        DifferentiableAt ℝ f x ∧ (x ≠ p → deriv f x ≠ 0) ∧
        |scalarNewtonValue f x - p - (1 - 1 / (m : ℝ)) * (x - p)| ≤
          C * |x - p| ^ 2 ∧
        |correctedNewtonValue m f x - p| ≤ (m : ℝ) * C * |x - p| ^ 2 ∧
        |scalarNewtonValue f x - p| ≤ q * |x - p| ∧
        |correctedNewtonValue m f x - p| ≤ q * |x - p|) ∧
      localMultipleRootRuns f p r q (scalarNewtonValue f) ∧
      localMultipleRootRuns f p r q (correctedNewtonValue m f) ∧
      (∀ (x₀ : ℝ) (x : ℕ → ℝ), |x₀ - p| < r →
        IsExactRunValue (stopAtRootValue f (scalarNewtonValue f)) x₀ x →
        (∀ n, x n ≠ p) →
        Tendsto (fun n => |x (n + 1) - p| / |x n - p|)
          atTop (𝓝 (1 - 1 / (m : ℝ))))

end Specs.NumAnalysis206.Newton
