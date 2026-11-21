import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit

/-!
Independent specification of `K03.01.subsequence` (paper.tex:260–269).

As in the upstream limit interface, `a n` is the paper's term `a_{n+1}`.
A map `φ : ℕ → ℕ` selects positive indices `φ j + 1` at positions `j + 1`.
Strict increase on these shifted indices is exactly strict increase of `φ`.
There is no restriction on the first selected term.
-/

namespace Specs.SingleVariableAnalysis.Ch01.Subsequence

universe u

def isSubsequenceType : Type (u + 1) :=
  {α : Type u} → (ℕ → α) → (ℕ → α) → Prop

/-- The first sequence is obtained from the second by a strictly increasing map. -/
def isSubsequenceValue : isSubsequenceType :=
  fun b a => ∃ φ : ℕ → ℕ, StrictMono φ ∧ b = a ∘ φ

def realSubsequentialLimitType : Type := (ℕ → ℝ) → ℝ → Prop

def realSubsequentialLimitValue : realSubsequentialLimitType :=
  fun a L => ∃ φ : ℕ → ℕ, StrictMono φ ∧
    SequenceLimit.realSequenceConvergesValue (a ∘ φ) L

def complexSubsequentialLimitType : Type := (ℕ → ℂ) → ℂ → Prop

def complexSubsequentialLimitValue : complexSubsequentialLimitType :=
  fun a L => ∃ φ : ℕ → ℕ, StrictMono φ ∧
    SequenceLimit.complexSequenceConvergesValue (a ∘ φ) L

/-- The induction bound in the manuscript's proof. -/
def subsequenceIndexGe : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ∀ j : ℕ, j ≤ φ j

def sequenceEventuallyComp : Prop :=
  ∀ (P : ℕ → Prop) (φ : ℕ → ℕ), StrictMono φ →
    SequenceLimit.sequenceEventuallyValue P →
      SequenceLimit.sequenceEventuallyValue (P ∘ φ)

def realSequenceConvergesComp : Prop :=
  ∀ (a : ℕ → ℝ) (L : ℝ) (φ : ℕ → ℕ), StrictMono φ →
    SequenceLimit.realSequenceConvergesValue a L →
      SequenceLimit.realSequenceConvergesValue (a ∘ φ) L

def complexSequenceConvergesComp : Prop :=
  ∀ (a : ℕ → ℂ) (L : ℂ) (φ : ℕ → ℕ), StrictMono φ →
    SequenceLimit.complexSequenceConvergesValue a L →
      SequenceLimit.complexSequenceConvergesValue (a ∘ φ) L

def realSequenceConvergesOfIsSubsequence : Prop :=
  ∀ (a b : ℕ → ℝ) (L : ℝ), isSubsequenceValue b a →
    SequenceLimit.realSequenceConvergesValue a L →
      SequenceLimit.realSequenceConvergesValue b L

def complexSequenceConvergesOfIsSubsequence : Prop :=
  ∀ (a b : ℕ → ℂ) (L : ℂ), isSubsequenceValue b a →
    SequenceLimit.complexSequenceConvergesValue a L →
      SequenceLimit.complexSequenceConvergesValue b L

end Specs.SingleVariableAnalysis.Ch01.Subsequence
