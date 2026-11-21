import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.GamblersRuin
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.MeanHittingTime

open MeasureTheory
open scoped ENNReal

namespace P207.Walk.RuinMeanSpec

/-- Expectation of the actual entrance time, including time-zero entrance at
both endpoints. The equality in extended nonnegative reals also records finiteness.
The upper exit probability is the canonical path-event probability. -/
def ruin_mean : Prop := ∀ (N : ℕ), 1 ≤ N →
  ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : RuinState N),
    (∫⁻ ω, ENat.toENNReal (ruinTime N ω)
      ∂Markov.statePathLaw (ruinKernel N p hp hp1) i) =
    ENNReal.ofReal (if p = 1 - p then (i.val : ℝ) * (N - (i.val : ℝ))
      else ((N : ℝ) * ruinExitProbability N p hp hp1 i - i.val) / (p - (1 - p)))

/-- The same formula as an equality of real values, without truncating the
closed form through `ofReal`. -/
def ruin_mean_real : Prop := ∀ (N : ℕ), 1 ≤ N →
  ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : RuinState N),
    (∫⁻ ω, ENat.toENNReal (ruinTime N ω)
      ∂Markov.statePathLaw (ruinKernel N p hp hp1) i).toReal =
    if p = 1 - p then (i.val : ℝ) * (N - (i.val : ℝ))
      else ((N : ℝ) * ruinExitProbability N p hp hp1 i - i.val) / (p - (1 - p))

end P207.Walk.RuinMeanSpec
