import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.IntegerHitting
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.MeanHittingTime

open MeasureTheory
open scoped ENNReal

namespace P207.Walk.SymmetricInfiniteMeansSpec

/-- The two adjacent entrances and the positive return have infinite extended
expectation, even though each time is almost surely finite. -/
def infinite_means : Prop := ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1),
  p = 1 - p →
    (∫⁻ ω, ENat.toENNReal (Markov.hittingTime {0} ω) ∂integerLaw p hp hp1 1) = ⊤ ∧
    (∫⁻ ω, ENat.toENNReal (Markov.hittingTime {0} ω) ∂integerLaw p hp hp1 (-1)) = ⊤ ∧
    (∫⁻ ω, ENat.toENNReal (Markov.returnTime 0 ω) ∂integerLaw p hp hp1 0) = ⊤

def almost_sure_finite : Prop := ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1),
  p = 1 - p →
    (∀ᵐ ω ∂integerLaw p hp hp1 1, Markov.hittingTime {0} ω < ⊤) ∧
    (∀ᵐ ω ∂integerLaw p hp hp1 (-1), Markov.hittingTime {0} ω < ⊤) ∧
    (∀ᵐ ω ∂integerLaw p hp hp1 0, Markov.returnTime 0 ω < ⊤)

end P207.Walk.SymmetricInfiniteMeansSpec
