import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.BinomialQuantities
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Independent propositions for the geometric majorant and its strict tails. -/

open scoped Topology

namespace D03SupportRepairs.Specs

/-- The full real geometric majorant is summable. -/
def geomTermSummableType : Prop :=
  Summable (fun j : ℕ => geomTermValue j)

/-- Every strict tail, padded by zeros, is summable. -/
def geometricTailSummableType : Prop :=
  ∀ J : ℕ, Summable (fun j : ℕ => if J < j then geomTermValue j else 0)

/-- Every actual geometric tail is nonnegative. -/
def geometricTailNonnegType : Prop :=
  ∀ J : ℕ, 0 ≤ geometricTailValue J

/-- The strict tails tend to zero as their natural cutoff tends to infinity. -/
def geometricTailTendstoType : Prop :=
  Filter.Tendsto geometricTailValue Filter.atTop (nhds (0 : ℝ))

end D03SupportRepairs.Specs
