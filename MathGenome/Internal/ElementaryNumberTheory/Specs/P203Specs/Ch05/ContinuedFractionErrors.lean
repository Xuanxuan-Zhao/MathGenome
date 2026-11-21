import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.Convergents
import Mathlib.Topology.Instances.Real.Lemmas

/-! Strict bounds, convergence, and uniqueness from paper.tex §nt:E03,
`eq:nt-cf-error` and the paragraph immediately following its proof.
The signed integer continuants and the zero-based, stopping-aware digits
are exactly those shared with the preceding sections. -/
namespace P203Specs
open Filter
open scoped Topology

/-- Both strict bounds hold even at the initial index. -/
def ConvergentErrorBounds : Prop :=
  ∀ (x : ℝ), Irrational x → ∀ n : ℕ,
    1 / ((convergentDenominator x n : ℝ) *
      ((convergentDenominator x (n + 1 : ℕ) : ℝ) +
        (convergentDenominator x n : ℝ))) <
      |x - (convergentNumerator x n : ℝ) / (convergentDenominator x n : ℝ)| ∧
    |x - (convergentNumerator x n : ℝ) / (convergentDenominator x n : ℝ)| <
      1 / ((convergentDenominator x n : ℝ) *
        (convergentDenominator x (n + 1 : ℕ) : ℝ))

/-- Divergence of the actual integer denominators. -/
def ConvergentDenominatorsTendToInfinity : Prop :=
  ∀ (x : ℝ), Irrational x →
    Tendsto (fun n : ℕ => convergentDenominator x n) atTop atTop

/-- The real ratios of the canonical integer continuants converge to x. -/
def ConvergentConvergence : Prop :=
  ∀ (x : ℝ), Irrational x →
    Tendsto (fun n : ℕ =>
      (convergentNumerator x n : ℝ) / (convergentDenominator x n : ℝ)) atTop (𝓝 x)

/-- Equality of every algorithm-produced digit determines the irrational real. -/
def InfiniteDigitUniqueness : Prop :=
  ∀ (x y : ℝ), Irrational x → Irrational y →
    (∀ n : ℕ, partialQuotient x n = partialQuotient y n) → x = y

end P203Specs
