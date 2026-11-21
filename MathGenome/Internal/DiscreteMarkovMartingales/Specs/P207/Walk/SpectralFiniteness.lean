import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.LatticeLocalBounds

open MeasureTheory
open scoped ENNReal

namespace P207.Walk.SpectralFinitenessSpec

/-- The high-dimensional analytic part of the proof of Pólya's theorem.
The integral uses the literal probability Haar measure and extended reciprocal. -/
def spectral_finiteness : Prop := ∀ (d : ℕ) [NeZero d], 3 ≤ d →
  (∫⁻ t : Torus d, (ENNReal.ofReal (1 - phi t ^ 2))⁻¹ ∂torusMeasure d) < ⊤

end P207.Walk.SpectralFinitenessSpec
