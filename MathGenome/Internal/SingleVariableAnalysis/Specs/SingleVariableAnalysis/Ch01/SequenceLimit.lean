import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Scalar
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
Independent specification for `K03.01.sequence_limit` (paper.tex:211–219).
The manuscript's positive-indexed sequences are represented with a shift:
the value at Lean index `n : ℕ` is the manuscript's term numbered `n + 1`.
Thus a Lean tail `n ≥ N` is exactly the positive-index tail numbered `N + 1`.
Finite limits have values in the canonical `ℝ` or `ℂ`, while divergence
predicates concern real sequences and arbitrary real thresholds.
-/

namespace Specs.SingleVariableAnalysis.Ch01.SequenceLimit

open scoped Topology

def sequenceEventuallyType : Type := (ℕ → Prop) → Prop

def sequenceEventuallyValue : sequenceEventuallyType :=
  fun P => ∃ N : ℕ, ∀ n ≥ N, P n

def realSequenceConvergesType : Type := (ℕ → ℝ) → ℝ → Prop

def realSequenceConvergesValue : realSequenceConvergesType :=
  fun a L => ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

def complexSequenceConvergesType : Type := (ℕ → ℂ) → ℂ → Prop

def complexSequenceConvergesValue : complexSequenceConvergesType :=
  fun a L => ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖a n - L‖ < ε

def divergesToPosInfinityType : Type := (ℕ → ℝ) → Prop

def divergesToPosInfinityValue : divergesToPosInfinityType :=
  fun a => ∀ B : ℝ, ∃ N : ℕ, ∀ n ≥ N, B < a n

def divergesToNegInfinityType : Type := (ℕ → ℝ) → Prop

def divergesToNegInfinityValue : divergesToNegInfinityType :=
  fun a => ∀ B : ℝ, ∃ N : ℕ, ∀ n ≥ N, a n < B

def sequenceEventuallyIff : Prop :=
  ∀ P : ℕ → Prop,
    sequenceEventuallyValue P ↔ Filter.Eventually P Filter.atTop

def realSequenceConvergesIff : Prop :=
  ∀ (a : ℕ → ℝ) (L : ℝ),
    realSequenceConvergesValue a L ↔ Filter.Tendsto a Filter.atTop (𝓝 L)

def complexSequenceConvergesIff : Prop :=
  ∀ (a : ℕ → ℂ) (L : ℂ),
    complexSequenceConvergesValue a L ↔ Filter.Tendsto a Filter.atTop (𝓝 L)

def divergesToPosInfinityIff : Prop :=
  ∀ a : ℕ → ℝ,
    divergesToPosInfinityValue a ↔ Filter.Tendsto a Filter.atTop Filter.atTop

def divergesToNegInfinityIff : Prop :=
  ∀ a : ℕ → ℝ,
    divergesToNegInfinityValue a ↔ Filter.Tendsto a Filter.atTop Filter.atBot

/-- Infinite divergence does not constitute a finite real scalar limit. -/
def posInfinityNotFinite : Prop :=
  ∀ a : ℕ → ℝ, divergesToPosInfinityValue a →
    ∀ L : ℝ, ¬ realSequenceConvergesValue a L

def negInfinityNotFinite : Prop :=
  ∀ a : ℕ → ℝ, divergesToNegInfinityValue a →
    ∀ L : ℝ, ¬ realSequenceConvergesValue a L

def infinityDirectionsExclusive : Prop :=
  ∀ a : ℕ → ℝ, divergesToPosInfinityValue a → ¬ divergesToNegInfinityValue a

end Specs.SingleVariableAnalysis.Ch01.SequenceLimit
