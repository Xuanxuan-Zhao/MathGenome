import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Limsup

/-!
Independent specification of K03.01.limsup_rules, paper.tex:301–313.
The bounds are the upstream extended-real tail bounds. Under the boundedness
hypotheses they are finite, so the equalities and sums have exactly their
ordinary real meanings. Index `n` represents the manuscript's index `n+1`.
-/

namespace Specs.SingleVariableAnalysis.Ch01.LimsupRules

open Limsup SequenceLimit

def boundedConvergenceIff : Prop :=
  ∀ (a : ℕ → ℝ), BddAbove (Set.range a) → BddBelow (Set.range a) →
    ∀ L : ℝ, realSequenceConvergesValue a L ↔
      sequenceLiminfValue a = (L : EReal) ∧ sequenceLimsupValue a = (L : EReal)

def boundedSumBounds : Prop :=
  ∀ (a b : ℕ → ℝ),
    BddAbove (Set.range a) → BddBelow (Set.range a) →
    BddAbove (Set.range b) → BddBelow (Set.range b) →
    sequenceLiminfValue a + sequenceLiminfValue b ≤
        sequenceLiminfValue (fun n => a n + b n) ∧
    sequenceLiminfValue (fun n => a n + b n) ≤
        sequenceLimsupValue (fun n => a n + b n) ∧
    sequenceLimsupValue (fun n => a n + b n) ≤
        sequenceLimsupValue a + sequenceLimsupValue b

def boundedNegation : Prop :=
  ∀ (a : ℕ → ℝ), BddAbove (Set.range a) → BddBelow (Set.range a) →
    sequenceLimsupValue (fun n => -a n) = -sequenceLiminfValue a

/-- The two bounded alternating sequences give precisely the strict bound 0 < 2. -/
def strictSumExample : Prop :=
  let a : ℕ → ℝ := fun n => (-1 : ℝ) ^ (n + 1)
  let b : ℕ → ℝ := fun n => -a n
  BddAbove (Set.range a) ∧ BddBelow (Set.range a) ∧
  BddAbove (Set.range b) ∧ BddBelow (Set.range b) ∧
  sequenceLimsupValue a = 1 ∧ sequenceLimsupValue b = 1 ∧
  sequenceLimsupValue (fun n => a n + b n) = 0 ∧
  sequenceLimsupValue (fun n => a n + b n) <
    sequenceLimsupValue a + sequenceLimsupValue b ∧ (0 : ℝ) < 2

end Specs.SingleVariableAnalysis.Ch01.LimsupRules
