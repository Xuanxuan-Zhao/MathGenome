import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.MertensWeighted
import Mathlib.Order.Filter.AtTopBot.Basic

/-! The second estimate and divergence in Theorem 3.11, paper.tex:1275–1283.
The sum uses the shared positive prime index with a real upper cutoff. -/
namespace P203Specs.MertensReciprocal

/-- The reciprocal prime sum with real cutoff. -/
noncomputable def R (x : ℝ) : ℝ :=
  ∑ p ∈ PrimeProduct.primes x, 1 / (p : ℝ)

/-- A constant term with the source's reciprocal-logarithm error. -/
def Estimate : Prop :=
  ∃ B C : ℝ, 0 ≤ C ∧ ∃ X : ℝ, 2 ≤ X ∧
    ∀ x : ℝ, X ≤ x → |R x - Real.log (Real.log x) - B| ≤ C / Real.log x

/-- Divergence expressed by real-cutoff partial sums tending to positive infinity. -/
def Divergence : Prop := Filter.Tendsto R Filter.atTop Filter.atTop

end P203Specs.MertensReciprocal
