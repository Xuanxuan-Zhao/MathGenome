import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.BigO
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Independent specification of K03.06.error_notation (paper.tex:2888–2896).
The approach is the full real two-sided punctured neighborhood of zero.
`RCLike` includes both manuscript scalar fields ℝ and ℂ; increments are real.
The strictness witness is the real-valued power, embedded in either scalar
field, with the canonical real power at the nonnegative base |h|. Only nonzero h are tested, so its base is positive there.
Natural n includes zero. No differentiability assumptions are made.
-/

namespace Specs.SingleVariableAnalysis.Ch06.ErrorNotation
open Filter
open scoped Topology

/-- The next-order big-O bound implies the order-n little-o estimate. -/
def nextOrderBigOImpliesLittleO : Prop :=
  ∀ {K : Type} [RCLike K] (n : ℕ) (r : ℝ → K),
    Ch02.BigO.scalarBigOValue (𝓝[≠] (0 : ℝ)) r (fun h => (h : K) ^ (n + 1)) →
    Ch02.BigO.scalarLittleOValue (𝓝[≠] (0 : ℝ)) r (fun h => (h : K) ^ n)

/-- Every fractional intermediate order is little-o of the nth integer power. -/
def fractionalOrderLittleO : Prop :=
  ∀ {K : Type} [RCLike K] (n : ℕ) (α : ℝ), 0 < α → α < 1 →
    Ch02.BigO.scalarLittleOValue (𝓝[≠] (0 : ℝ))
      (fun h => ((|h| ^ ((n : ℝ) + α) : ℝ) : K)) (fun h => (h : K) ^ n)

/-- The same witnesses fail the next-order big-O estimate. -/
def fractionalOrderNotBigO : Prop :=
  ∀ {K : Type} [RCLike K] (n : ℕ) (α : ℝ), 0 < α → α < 1 →
    ¬ Ch02.BigO.scalarBigOValue (𝓝[≠] (0 : ℝ))
      (fun h => ((|h| ^ ((n : ℝ) + α) : ℝ) : K)) (fun h => (h : K) ^ (n + 1))

end Specs.SingleVariableAnalysis.Ch06.ErrorNotation
