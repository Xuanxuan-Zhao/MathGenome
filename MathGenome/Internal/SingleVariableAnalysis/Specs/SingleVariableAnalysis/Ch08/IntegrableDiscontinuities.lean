import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Criterion
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.OscillationSets
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.ZeroCovers

/-! The forward direction of K03.08.oscillation_criterion, paper.tex:2223–2232.
Integrability is the upstream Darboux predicate, including boundedness and a ≤ b.
Discontinuities use continuity relative to [a,b], including both endpoints.
The conclusion is the upstream countable open bounded interval cover predicate.
-/
namespace Specs.SingleVariableAnalysis.Ch08.IntegrableDiscontinuities

/-- Every positive relative oscillation superlevel has length zero. -/
def integrableSuperlevelLengthZero : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, Integral.realIntegrableValue f a b →
    ∀ α : ℝ, 0 < α →
      ZeroCovers.lengthZeroValue (OscillationSets.oscillationSuperlevelValue f a b α)

/-- The discontinuity set of any bounded real Riemann integrable function has
countable-cover length zero. Singleton intervals are included. -/
def integrableDiscontinuitiesLengthZero : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, Integral.realIntegrableValue f a b →
    ZeroCovers.lengthZeroValue (OscillationSets.intervalDiscontinuitiesValue f a b)

end Specs.SingleVariableAnalysis.Ch08.IntegrableDiscontinuities
