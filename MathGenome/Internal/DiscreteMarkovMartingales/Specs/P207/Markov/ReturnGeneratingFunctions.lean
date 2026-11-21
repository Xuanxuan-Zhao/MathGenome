import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.RecurrenceInterfaces
import Mathlib.Analysis.SpecificLimits.Basic

/-! The complete proposition in paper.tex, p207:W11 (lines 551–579).
Probabilities are ENNReal masses of the accepted canonical law. The generating
functions are real sums; their boundary limits are embedded in ENNReal so the
Green limit includes infinity. No irreducibility or recurrence is assumed. -/
open MeasureTheory Filter
open scoped ENNReal Topology
universe u
namespace P207.Markov.ReturnGeneratingFunctions
noncomputable section

variable {S : Type u}

def diagonalMass (P : StochasticMatrix S) (i : S) (n : ℕ) : ℝ≥0∞ := power P n i i

variable [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

def firstReturnMass (P : StochasticMatrix S) (i : S) (n : ℕ) : ℝ≥0∞ :=
  statePathLaw P i {ω | returnTime i ω = n}

def greenFunction (P : StochasticMatrix S) (i : S) (z : ℝ) : ℝ :=
  ∑' n : ℕ, (diagonalMass P i n).toReal * z ^ n

def firstReturnFunction (P : StochasticMatrix S) (i : S) (z : ℝ) : ℝ :=
  ∑' n : ℕ, (firstReturnMass P i (n + 1)).toReal * z ^ (n + 1)

end
end P207.Markov.ReturnGeneratingFunctions

namespace P207.Markov.ReturnGeneratingFunctionsSpec
noncomputable section
open ReturnGeneratingFunctions

def diagonalMassType := {S : Type u} → StochasticMatrix S → S → ℕ → ℝ≥0∞
def diagonalMassValue : diagonalMassType := @diagonalMass

def firstReturnMassType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → S → ℕ → ℝ≥0∞
def firstReturnMassValue : firstReturnMassType := @firstReturnMass

def generatingFunctionType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → S → ℝ → ℝ
def greenFunctionType := {S : Type u} → StochasticMatrix S → S → ℝ → ℝ
def greenFunctionValue : greenFunctionType := @greenFunction
def firstReturnFunctionValue : generatingFunctionType := @firstReturnFunction

def diagonal_zero : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S), diagonalMass P i 0 = 1

def firstReturn_zero : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S), firstReturnMass P i 0 = 0

def firstReturn_total : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S), (∑' n : ℕ, firstReturnMass P i (n + 1)) = returnProbability P i

def convolution : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S), ∀ n : ℕ, 1 ≤ n →
    diagonalMass P i n = ∑ k ∈ Finset.Icc 1 n,
      firstReturnMass P i k * diagonalMass P i (n - k)

def summable_green : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S), ∀ z : ℝ, 0 ≤ z → z < 1 →
    Summable (fun n : ℕ => (diagonalMass P i n).toReal * z ^ n)

def summable_firstReturn : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S), ∀ z : ℝ, 0 ≤ z → z < 1 →
    Summable (fun n : ℕ => (firstReturnMass P i (n + 1)).toReal * z ^ (n + 1))

def firstReturn_le : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S), ∀ z : ℝ, 0 ≤ z → z < 1 → firstReturnFunction P i z ≤ z

def firstReturn_lt_one : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S), ∀ z : ℝ, 0 ≤ z → z < 1 → firstReturnFunction P i z < 1

def green_le : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S), ∀ z : ℝ, 0 ≤ z → z < 1 → greenFunction P i z ≤ 1 / (1 - z)

def reciprocal : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S), ∀ z : ℝ, 0 ≤ z → z < 1 →
    greenFunction P i z = 1 / (1 - firstReturnFunction P i z)

def limit_firstReturn : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S),
    Tendsto (fun z : ℝ => ENNReal.ofReal (firstReturnFunction P i z))
      (𝓝[<] 1) (𝓝 (returnProbability P i))

def limit_green : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S),
    Tendsto (fun z : ℝ => ENNReal.ofReal (greenFunction P i z))
      (𝓝[<] 1) (𝓝 (∑' n : ℕ, diagonalMass P i n))

end
end P207.Markov.ReturnGeneratingFunctionsSpec
