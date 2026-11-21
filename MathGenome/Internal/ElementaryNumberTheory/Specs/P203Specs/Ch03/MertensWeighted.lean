import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.PrimeProduct

/-! The first assertion of Theorem 3.11, paper.tex:1275–1279.
The prime index uses positive primes and retains the real upper limit.
All logarithms are natural, and the estimate is for real x → +∞. -/
namespace P203Specs.MertensWeighted

/-- The logarithmically weighted prime sum with real cutoff. -/
noncomputable def M (x : ℝ) : ℝ :=
  ∑ p ∈ PrimeProduct.primes x, Real.log (p : ℝ) / (p : ℝ)

/-- M(x) = log x + O(1), expressed as an eventual uniform absolute bound. -/
def Estimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ X : ℝ,
    ∀ x : ℝ, X ≤ x → |M x - Real.log x| ≤ C

end P203Specs.MertensWeighted
