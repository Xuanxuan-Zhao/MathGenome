import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SupInf
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit

/-!
Independent specification for `K03.01.monotone` (paper.tex:244–251).

As in the sequence-limit interface, `a n` represents the manuscript's term
`a_{n+1}`. `Monotone` means nondecreasing and `Antitone` means nonincreasing;
neither is strict. Boundedness concerns the entire real range. Finite limits
use the shared real supremum/infimum, and infinite limits use arbitrary real
thresholds, separately from finite convergence.
-/

namespace Specs.SingleVariableAnalysis.Ch01.Monotone

open SupInf SequenceLimit

def monotoneConvergesToSupremum : Prop :=
  ∀ (a : ℕ → ℝ), Monotone a → ∀ hb : BddAbove (Set.range a),
    realSequenceConvergesValue a
      (realSupremumValue (Set.range a) (Set.range_nonempty a) hb)

def monotoneDivergesToPosInfinity : Prop :=
  ∀ (a : ℕ → ℝ), Monotone a → ¬ BddAbove (Set.range a) →
    divergesToPosInfinityValue a

def antitoneConvergesToInfimum : Prop :=
  ∀ (a : ℕ → ℝ), Antitone a → ∀ hb : BddBelow (Set.range a),
    realSequenceConvergesValue a
      (realInfimumValue (Set.range a) (Set.range_nonempty a) hb)

def antitoneDivergesToNegInfinity : Prop :=
  ∀ (a : ℕ → ℝ), Antitone a → ¬ BddBelow (Set.range a) →
    divergesToNegInfinityValue a

end Specs.SingleVariableAnalysis.Ch01.Monotone
