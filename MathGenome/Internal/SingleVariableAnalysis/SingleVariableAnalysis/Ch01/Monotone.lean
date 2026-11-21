import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SupInf
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SequenceLimit
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Monotone
import Mathlib.Tactic.Linarith

/-!
# Monotone convergence of real sequences

This proves all four cases of `K03.01.monotone` (paper.tex:244–251).
The indexing is shifted exactly as in `SequenceLimit`: `a n` is the source's
term `a_{n+1}`. For bounded sequences, supremum/infimum approximation supplies
one term within epsilon of the bound, and monotonicity controls its whole tail.
For unbounded sequences, choose a term past the requested real threshold.
-/

namespace SingleVariableAnalysis

/-- A nondecreasing bounded-above real sequence tends to its range supremum. -/
theorem monotone_converges_to_supremum (a : ℕ → ℝ) (ha : Monotone a)
    (hb : BddAbove (Set.range a)) :
    RealSequenceConverges a
      (realSupremum (Set.range a) (Set.range_nonempty a) hb) := by
  intro ε hε
  obtain ⟨x, ⟨N, rfl⟩, hx, _⟩ :=
    real_supremum_approx (Set.range a) (Set.range_nonempty a) hb ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hu := (real_supremum_isLUB (Set.range a) (Set.range_nonempty a) hb).1
    (Set.mem_range_self n)
  have hl := hx.trans_le (ha hn)
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A nondecreasing unbounded-above real sequence exceeds every threshold eventually. -/
theorem monotone_diverges_to_posInfinity (a : ℕ → ℝ) (ha : Monotone a)
    (hb : ¬ BddAbove (Set.range a)) : DivergesToPosInfinity a := by
  intro B
  obtain ⟨x, ⟨N, rfl⟩, hx⟩ := not_bddAbove_iff.mp hb B
  exact ⟨N, fun n hn => hx.trans_le (ha hn)⟩

/-- A nonincreasing bounded-below real sequence tends to its range infimum. -/
theorem antitone_converges_to_infimum (a : ℕ → ℝ) (ha : Antitone a)
    (hb : BddBelow (Set.range a)) :
    RealSequenceConverges a
      (realInfimum (Set.range a) (Set.range_nonempty a) hb) := by
  intro ε hε
  obtain ⟨x, ⟨N, rfl⟩, _, hx⟩ :=
    real_infimum_approx (Set.range a) (Set.range_nonempty a) hb ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hl := (real_infimum_isGLB (Set.range a) (Set.range_nonempty a) hb).1
    (Set.mem_range_self n)
  have hu := (ha hn).trans_lt hx
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A nonincreasing unbounded-below real sequence falls below every threshold eventually. -/
theorem antitone_diverges_to_negInfinity (a : ℕ → ℝ) (ha : Antitone a)
    (hb : ¬ BddBelow (Set.range a)) : DivergesToNegInfinity a := by
  intro B
  obtain ⟨x, ⟨N, rfl⟩, hx⟩ := not_bddBelow_iff.mp hb B
  exact ⟨N, fun n hn => (ha hn).trans_lt hx⟩

end SingleVariableAnalysis
