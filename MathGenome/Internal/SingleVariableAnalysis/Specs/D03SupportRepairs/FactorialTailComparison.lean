import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.BinomialQuantities
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Independent propositions for summability and comparison of the actual
inverse-factorial tails. All natural cutoffs, including zero, are included. -/

namespace D03SupportRepairs.Specs

/-- The full inverse-factorial series is summable in the reals. -/
def invFactorialSummableType : Prop :=
  Summable (fun j : ℕ => invFactorialValue j)

/-- Every strict inverse-factorial tail, padded by zeros, is summable. -/
def factorialTailSummableType : Prop :=
  ∀ J : ℕ, Summable (fun j : ℕ => if J < j then invFactorialValue j else 0)

/-- The actual inverse-factorial tails are nonnegative. -/
def factorialTailNonnegType : Prop :=
  ∀ J : ℕ, 0 ≤ factorialTailValue J

/-- Each actual inverse-factorial tail is bounded by the source geometric tail. -/
def factorialTailLeGeometricTailType : Prop :=
  ∀ J : ℕ, factorialTailValue J ≤ geometricTailValue J

end D03SupportRepairs.Specs
