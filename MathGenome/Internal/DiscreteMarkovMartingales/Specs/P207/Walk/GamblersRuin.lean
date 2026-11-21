import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.RuinAbsorption

open MeasureTheory

namespace P207.Walk
noncomputable section

/-- Probability of reaching the upper endpoint strictly before the lower endpoint.
The shared entrance times include time zero and may be infinite. -/
def ruinExitProbability (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) : ℝ :=
  (Markov.statePathLaw (ruinKernel N p hp hp1) i
    {ω | Markov.hittingTime {Fin.last N} ω < Markov.hittingTime {0} ω}).toReal

namespace GamblersRuinSpec

def probabilityType := (N : ℕ) → (p : ℝ) → (hp : 0 < p) → (hp1 : p < 1) →
  RuinState N → ℝ
def probabilityValue : probabilityType := ruinExitProbability

def exit_zero : Prop := ∀ (N : ℕ), 1 ≤ N →
  ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), ruinExitProbability N p hp hp1 0 = 0

def exit_last : Prop := ∀ (N : ℕ), 1 ≤ N →
  ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), ruinExitProbability N p hp hp1 (Fin.last N) = 1

/-- All states are included, in particular both endpoints and the interval `N = 1`. -/
def gamblers_ruin : Prop := ∀ (N : ℕ), 1 ≤ N →
  ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : RuinState N),
    ruinExitProbability N p hp hp1 i =
      if p = 1 - p then (i.val : ℝ) / N
      else (1 - ((1 - p) / p) ^ i.val) / (1 - ((1 - p) / p) ^ N)

end GamblersRuinSpec
end
end P207.Walk
