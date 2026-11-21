import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.RationalIncomplete
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Archimedean
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.PositiveRoots

/-!
# A rational Cauchy sequence without a rational limit

This implements the rational counterexample of `K03.01.cauchy` and
`K03.01.counterexamples`. All sequences follow the shared shifted indexing:
Lean `n` is the manuscript's positive index `n + 1`.

Rational density supplies a witness within `1/(n+1)` for each term.
The reciprocal tail estimate proves real convergence. The real Cauchy
criterion and the actual definition of the rational metric transfer the
pairwise estimates to ℚ. Any rational limit would, by continuity of the
embedding into ℝ and uniqueness of real limits, equal √2.

Irrationality is reused from Mathlib's `irrational_sqrt_two`, proved there
through the nonsquare criterion for rational square roots and primality of 2.
The upstream `nonnegativeRoot_sqrt` identifies this canonical square root
with the manuscript's supremum construction.
-/

namespace SingleVariableAnalysis

open scoped Topology

theorem sqrt_two_irrational : Irrational (Real.sqrt 2) :=
  irrational_sqrt_two

/-- Every sequence with the prescribed errors has the asserted real limit. -/
theorem rational_sqrt_two_limit (q : ℕ → ℚ)
    (hq : ∀ n : ℕ, |(q n : ℝ) - Real.sqrt 2| < 1 / ((n : ℝ) + 1)) :
    RealSequenceConverges (fun n => (q n : ℝ)) (Real.sqrt 2) := by
  intro ε hε
  obtain ⟨N, _, hN⟩ := reciprocal_tail ε hε
  refine ⟨N, fun n hn => ?_⟩
  have ht := hN (n + 1) (hn.trans (Nat.le_succ n))
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  rw [Nat.cast_add, Nat.cast_one, abs_of_pos (one_div_pos.mpr hpos)] at ht
  exact (hq n).trans ht

/-- The standard rational metric has exactly the real pairwise distances. -/
theorem rational_sqrt_two_cauchy (q : ℕ → ℚ)
    (hq : ∀ n : ℕ, |(q n : ℝ) - Real.sqrt 2| < 1 / ((n : ℝ) + 1)) :
    CauchySeq q := by
  have hc := (real_cauchy_criterion (fun n => (q n : ℝ))).mp
    ⟨Real.sqrt 2, rational_sqrt_two_limit q hq⟩
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hc ε hε
  exact ⟨N, fun m hm n hn => by
    simpa only [Rat.dist_eq] using hN n hn m hm⟩

theorem rational_sqrt_two_no_limit (q : ℕ → ℚ)
    (hq : ∀ n : ℕ, |(q n : ℝ) - Real.sqrt 2| < 1 / ((n : ℝ) + 1))
    (r : ℚ) : ¬ Filter.Tendsto q Filter.atTop (𝓝 r) := by
  intro hr
  have hreal := (realSequenceConverges_iff _ _).mp (rational_sqrt_two_limit q hq)
  have hrat : Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (𝓝 (r : ℝ)) :=
    (Rat.continuous_coe_real.tendsto r).comp hr
  have heq : (r : ℝ) = Real.sqrt 2 := tendsto_nhds_unique hrat hreal
  exact sqrt_two_irrational ⟨r, heq⟩

/-- Choose all rational witnesses and retain every part of the counterexample. -/
theorem rational_incompleteness :
    ∃ q : ℕ → ℚ,
      (∀ n : ℕ, |(q n : ℝ) - Real.sqrt 2| < 1 / ((n : ℝ) + 1)) ∧
        RealSequenceConverges (fun n => (q n : ℝ)) (Real.sqrt 2) ∧
        CauchySeq q ∧ ¬ ∃ r : ℚ, Filter.Tendsto q Filter.atTop (𝓝 r) := by
  have ha : ∀ n : ℕ, ∃ r : ℚ,
      |(r : ℝ) - Real.sqrt 2| < 1 / ((n : ℝ) + 1) := by
    intro n
    exact rational_approximation (Real.sqrt 2) (1 / ((n : ℝ) + 1)) (by positivity)
  choose q hq using ha
  exact ⟨q, hq, rational_sqrt_two_limit q hq, rational_sqrt_two_cauchy q hq,
    fun ⟨r, hr⟩ => rational_sqrt_two_no_limit q hq r hr⟩

/-- Completeness fails for the usual rational metric. -/
theorem rationals_not_complete : ¬ CompleteSpace ℚ := by
  intro hcomplete
  let : CompleteSpace ℚ := hcomplete
  obtain ⟨q, _, _, hc, hn⟩ := rational_incompleteness
  exact hn (cauchySeq_tendsto_of_complete hc)

end SingleVariableAnalysis
