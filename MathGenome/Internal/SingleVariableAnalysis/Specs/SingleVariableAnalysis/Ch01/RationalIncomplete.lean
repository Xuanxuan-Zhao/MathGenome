import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy

/-!
Independent specification for the rational counterexample in
`K03.01.cauchy` and `K03.01.counterexamples` (paper.tex:286, 354).

As in the shared sequence interface, Lean index `n` denotes the paper's
positive index `n + 1`. Thus the error bound below is exactly `1/k` at
every positive paper index `k`. `CauchySeq` and rational `Tendsto` use
the usual metric on ℚ, inherited from ℝ, with no completeness assumption.
The square root is the canonical nonnegative real square root, identified
with the manuscript's root construction by the upstream PositiveRoots goal.
-/

namespace Specs.SingleVariableAnalysis.Ch01.RationalIncomplete

open scoped Topology

def sqrtTwoIrrational : Prop := Irrational (Real.sqrt 2)

def approximationLimit : Prop :=
  ∀ q : ℕ → ℚ,
    (∀ n : ℕ, |(q n : ℝ) - Real.sqrt 2| < 1 / ((n : ℝ) + 1)) →
      SequenceLimit.realSequenceConvergesValue (fun n => (q n : ℝ)) (Real.sqrt 2)

def approximationCauchy : Prop :=
  ∀ q : ℕ → ℚ,
    (∀ n : ℕ, |(q n : ℝ) - Real.sqrt 2| < 1 / ((n : ℝ) + 1)) →
      CauchySeq q

def approximationNoRationalLimit : Prop :=
  ∀ q : ℕ → ℚ,
    (∀ n : ℕ, |(q n : ℝ) - Real.sqrt 2| < 1 / ((n : ℝ) + 1)) →
      ∀ r : ℚ, ¬ Filter.Tendsto q Filter.atTop (𝓝 r)

def rationalCounterexample : Prop :=
  ∃ q : ℕ → ℚ,
    (∀ n : ℕ, |(q n : ℝ) - Real.sqrt 2| < 1 / ((n : ℝ) + 1)) ∧
      SequenceLimit.realSequenceConvergesValue (fun n => (q n : ℝ)) (Real.sqrt 2) ∧
      CauchySeq q ∧ ¬ ∃ r : ℚ, Filter.Tendsto q Filter.atTop (𝓝 r)

def rationalsNotComplete : Prop := ¬ CompleteSpace ℚ

end Specs.SingleVariableAnalysis.Ch01.RationalIncomplete
