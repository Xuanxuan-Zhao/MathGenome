import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit

/-!
Independent specification of `K03.01.unique_limit` (paper.tex:218–226).
As in the upstream sequence interface, Lean index `n` denotes the paper's
term `n + 1`. Bounds cover the entire range, including every initial term.
Finite changes may occur at any finite set of indices. The shift by `k`
deletes precisely the first `k` terms; the equivalences also cover restoring
an arbitrary finite prefix. Scalars are exactly the canonical reals and
complex numbers, with finite scalar limits throughout.
-/

namespace Specs.SingleVariableAnalysis.Ch01.UniqueLimit

open Specs.SingleVariableAnalysis.Ch01.SequenceLimit

def realLimitUnique : Prop :=
  ∀ (a : ℕ → ℝ) (L M : ℝ),
    realSequenceConvergesValue a L → realSequenceConvergesValue a M → L = M

def complexLimitUnique : Prop :=
  ∀ (a : ℕ → ℂ) (L M : ℂ),
    complexSequenceConvergesValue a L → complexSequenceConvergesValue a M → L = M

def realConvergentBounded : Prop :=
  ∀ (a : ℕ → ℝ) (L : ℝ), realSequenceConvergesValue a L →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |a n| ≤ C

def complexConvergentBounded : Prop :=
  ∀ (a : ℕ → ℂ) (L : ℂ), complexSequenceConvergesValue a L →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖a n‖ ≤ C

def realFiniteChangesIff : Prop :=
  ∀ (a b : ℕ → ℝ), Set.Finite {n | a n ≠ b n} → ∀ L : ℝ,
    realSequenceConvergesValue a L ↔ realSequenceConvergesValue b L

def complexFiniteChangesIff : Prop :=
  ∀ (a b : ℕ → ℂ), Set.Finite {n | a n ≠ b n} → ∀ L : ℂ,
    complexSequenceConvergesValue a L ↔ complexSequenceConvergesValue b L

def realShiftIff : Prop :=
  ∀ (a : ℕ → ℝ) (L : ℝ) (k : ℕ),
    realSequenceConvergesValue (fun n => a (n + k)) L ↔ realSequenceConvergesValue a L

def complexShiftIff : Prop :=
  ∀ (a : ℕ → ℂ) (L : ℂ) (k : ℕ),
    complexSequenceConvergesValue (fun n => a (n + k)) L ↔
      complexSequenceConvergesValue a L

end Specs.SingleVariableAnalysis.Ch01.UniqueLimit
