import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.LatticeLocalBounds

open MeasureTheory
open scoped ENNReal

namespace P207.Walk.SpectralDivergenceSpec

/-- The low-dimensional singularity is nonintegrable for the concrete normalized
angular Haar measure, including the logarithmic case of dimension two. -/
def divergence : Prop := ∀ (d : ℕ) [NeZero d], d = 1 ∨ d = 2 →
  (∫⁻ t : Torus d, (ENNReal.ofReal (1 - phi t ^ 2))⁻¹ ∂torusMeasure d) = ⊤

end P207.Walk.SpectralDivergenceSpec
