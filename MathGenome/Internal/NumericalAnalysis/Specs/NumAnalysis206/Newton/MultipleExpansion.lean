import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Independent local statement for the identity and error expansions in W74.
`ContDiffAt ℝ 2 g p` expresses C² regularity on a neighborhood of p. The
factorization is only required near p. Convergence is a separate obligation. -/

open Filter Topology

namespace Specs.NumAnalysis206.Newton

/-- A positive denominator bound and explicit finite quadratic error bounds.
The derivative is asserted nonzero only off p. The error estimates also hold at
p, since the raw Newton expressions there equal the successful-stop value p. -/
def multipleRootExpansion : Prop :=
  ∀ (f g : ℝ → ℝ) (p : ℝ) (m : ℕ), 2 ≤ m →
    ContDiffAt ℝ 2 g p → g p ≠ 0 →
    f =ᶠ[𝓝 p] (fun x => (x - p) ^ m * g x) →
    ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ 0 ≤ C ∧ f p = 0 ∧
      ∀ x : ℝ, |x - p| < r →
        DifferentiableAt ℝ f x ∧
        deriv f x = (x - p) ^ (m - 1) * ((m : ℝ) * g x + (x - p) * deriv g x) ∧
        c ≤ |(m : ℝ) * g x + (x - p) * deriv g x| ∧
        (x ≠ p → deriv f x ≠ 0 ∧
          f x / deriv f x = (x - p) / (m : ℝ) -
            (x - p) ^ 2 * deriv g x /
              ((m : ℝ) * ((m : ℝ) * g x + (x - p) * deriv g x))) ∧
        |scalarNewtonValue f x - p - (1 - 1 / (m : ℝ)) * (x - p)| ≤
          C * |x - p| ^ 2 ∧
        |correctedNewtonValue m f x - p| ≤ (m : ℝ) * C * |x - p| ^ 2

end Specs.NumAnalysis206.Newton
