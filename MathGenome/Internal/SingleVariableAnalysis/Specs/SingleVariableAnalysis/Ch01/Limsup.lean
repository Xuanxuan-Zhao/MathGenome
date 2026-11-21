import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SupInf
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Subsequence

/-!
Independent specification of K03.01.limsup, paper.tex:288–302.
As in the upstream sequence interface, `a n` denotes the paper's `a_{n+1}`.
All four bounds are defined in EReal for every real sequence. Real extraction
below is used only with boundedness, and explicit coercion equalities certify
that neither infinite endpoint has been replaced by the default `toReal` value.
-/

namespace Specs.SingleVariableAnalysis.Ch01.Limsup

open SequenceLimit Subsequence

def tailBoundType : Type := (ℕ → ℝ) → ℕ → EReal
noncomputable def tailSupremumValue : tailBoundType :=
  fun a N => ⨆ n ≥ N, (a n : EReal)
noncomputable def tailInfimumValue : tailBoundType :=
  fun a N => ⨅ n ≥ N, (a n : EReal)

def sequenceBoundType : Type := (ℕ → ℝ) → EReal
noncomputable def sequenceLimsupValue : sequenceBoundType :=
  fun a => ⨅ N, tailSupremumValue a N
noncomputable def sequenceLiminfValue : sequenceBoundType :=
  fun a => ⨆ N, tailInfimumValue a N

def tailSupremumAntitone : Prop := ∀ a, Antitone (tailSupremumValue a)
def tailInfimumMonotone : Prop := ∀ a, Monotone (tailInfimumValue a)

/-- Every tail bound and both limiting bounds are finite real numbers. -/
def boundedBoundsFinite : Prop :=
  ∀ a : ℕ → ℝ, BddAbove (Set.range a) → BddBelow (Set.range a) →
    (∀ N, ((tailSupremumValue a N).toReal : EReal) = tailSupremumValue a N ∧
      ((tailInfimumValue a N).toReal : EReal) = tailInfimumValue a N) ∧
    ((sequenceLimsupValue a).toReal : EReal) = sequenceLimsupValue a ∧
    ((sequenceLiminfValue a).toReal : EReal) = sequenceLiminfValue a

/-- Decreasing/increasing convergence in the finite, epsilon sense. -/
def boundedTailConvergence : Prop :=
  ∀ a : ℕ → ℝ, BddAbove (Set.range a) → BddBelow (Set.range a) →
    Antitone (fun N => (tailSupremumValue a N).toReal) ∧
    Monotone (fun N => (tailInfimumValue a N).toReal) ∧
    realSequenceConvergesValue (fun N => (tailSupremumValue a N).toReal)
      (sequenceLimsupValue a).toReal ∧
    realSequenceConvergesValue (fun N => (tailInfimumValue a N).toReal)
      (sequenceLiminfValue a).toReal

def boundedExtremeSubsequentialLimits : Prop :=
  ∀ a : ℕ → ℝ, BddAbove (Set.range a) → BddBelow (Set.range a) →
    realSubsequentialLimitValue a (sequenceLimsupValue a).toReal ∧
    realSubsequentialLimitValue a (sequenceLiminfValue a).toReal

/-- The extended order statement also applies to unbounded sequences. -/
def subsequentialLimitBounds : Prop :=
  ∀ (a : ℕ → ℝ) (v : ℝ), realSubsequentialLimitValue a v →
    sequenceLiminfValue a ≤ (v : EReal) ∧ (v : EReal) ≤ sequenceLimsupValue a

def boundedSubsequentialLimitBounds : Prop :=
  ∀ a : ℕ → ℝ, BddAbove (Set.range a) → BddBelow (Set.range a) →
    ∀ v : ℝ, realSubsequentialLimitValue a v →
      (sequenceLiminfValue a).toReal ≤ v ∧ v ≤ (sequenceLimsupValue a).toReal

end Specs.SingleVariableAnalysis.Ch01.Limsup
