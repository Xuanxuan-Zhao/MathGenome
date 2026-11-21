import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.WeakLowerSemicontinuity
import Mathlib.Order.Interval.Finset.Nat

/-!
Independent statements for paper.tex §v02-03, Theorem
`thm:convex-weak-closed` (lines 912–934). Weak convergence is convergence
in σ(X,X′), formed from the continuous dual of the original norm topology.
The finite combinations are indexed by nonempty intervals starting at n;
omitted terms have coefficient zero. All convergence in the conclusion
uses the original norm topology. No completeness hypothesis is imposed.
-/
noncomputable section
universe u
open Filter
open scoped Topology BigOperators
namespace VariationalNotes.ConvexAnalysis.Specs

/-- Mazur's lemma, with explicit real coefficients and tail indices. -/
def mazur_tail_combinations : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (xseq : ℕ → X) (x : X),
    Tendsto (fun n => toWeakSpace ℝ X (xseq n)) atTop (𝓝 (toWeakSpace ℝ X x)) →
    ∃ (m : ℕ → ℕ) (a : ℕ → ℕ → ℝ),
      (∀ n, n ≤ m n) ∧
      (∀ n j, 0 ≤ a n j) ∧
      (∀ n j, j ∉ Finset.Icc n (m n) → a n j = 0) ∧
      (∀ n, ∑ j ∈ Finset.Icc n (m n), a n j = 1) ∧
      Tendsto (fun n => ∑ j ∈ Finset.Icc n (m n), a n j • xseq j) atTop (𝓝 x)

/-- All three assertions of the source theorem. The first two assertions
retain their full hypotheses, independently of the weakly convergent sequence. -/
def convex_weak_closed : Prop :=
  normClosed_convex_isWeaklyClosed.{u} ∧
  convex_normLowerSemicontinuous_isWeaklyLowerSemicontinuous.{u} ∧
  mazur_tail_combinations.{u}

end VariationalNotes.ConvexAnalysis.Specs
