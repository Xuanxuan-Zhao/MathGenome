import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.GamblersRuin
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.RecurrenceInterfaces
import Mathlib.Probability.Independence.Basic

/-! Whole-line part of paper.tex, §W21. The walk uses the canonical product
path space with its natural coordinate filtration. Its entrance times include
zero; the separate shared return time starts at one. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace P207.Walk
noncomputable section

/-- No absorbing boundary: each coin moves one unit on the integer line. -/
def integerKernel (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Markov.StochasticMatrix ℤ :=
  fun i => (ruinCoin p hp hp1).map (fun b => if b then i + 1 else i - 1)

/-- The canonical law of the unrestricted walk started at any integer. -/
@[instance_reducible] def integerLaw (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : ℤ) :
    Measure (ℕ → ℤ) := Markov.statePathLaw (integerKernel p hp hp1) i

instance integerLaw_isProbabilityMeasure (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : ℤ) :
    IsProbabilityMeasure (integerLaw p hp hp1 i) := by
  change IsProbabilityMeasure (Markov.pathLaw _ (PMF.pure i))
  infer_instance

/-- Increments are indexed from zero: increment zero is the first move. -/
def integerIncrement (n : ℕ) (ω : ℕ → ℤ) : ℤ := ω (n + 1) - ω n

/-- Eventual entrance at zero, expressed as an ordinary real probability. -/
def integerHittingProbability (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : ℤ) : ℝ :=
  (Markov.hittingProbability (integerKernel p hp hp1) {0} i).toReal

namespace IntegerHittingSpec

def kernelType := (p : ℝ) → (hp : 0 < p) → (hp1 : p < 1) → Markov.StochasticMatrix ℤ
def kernelValue : kernelType := integerKernel

def lawType := (p : ℝ) → (hp : 0 < p) → (hp1 : p < 1) → ℤ → Measure (ℕ → ℤ)
def lawValue : lawType := integerLaw

def incrementType := ℕ → (ℕ → ℤ) → ℤ
def incrementValue : incrementType := integerIncrement

def probabilityType := (p : ℝ) → (hp : 0 < p) → (hp1 : p < 1) → ℤ → ℝ
def probabilityValue : probabilityType := integerHittingProbability

def kernel_mass : Prop := ∀ p hp hp1 (i j : ℤ),
  integerKernel p hp hp1 i j =
    (if j = i + 1 then ENNReal.ofReal p else 0) +
    (if j = i - 1 then ENNReal.ofReal (1 - p) else 0)

def natural_chain : Prop := ∀ p hp hp1 (i : ℤ),
  Markov.IsMarkovChain (integerKernel p hp hp1) (PMF.pure i)
    Markov.coordinate Markov.coordinateFiltration (integerLaw p hp hp1 i)

/-- The canonical construction really has independent increments. -/
def increments_independent : Prop := ∀ p hp hp1 (i : ℤ),
  iIndepFun integerIncrement (integerLaw p hp hp1 i)

def increment_law : Prop := ∀ p hp hp1 (i : ℤ) (n : ℕ),
  (integerLaw p hp hp1 i).map (integerIncrement n) =
    ((ruinCoin p hp hp1).map (fun b => if b then (1 : ℤ) else -1)).toMeasure

/-- The unrestricted exit race agrees with the stopped interval walk, including
both endpoints. Equality concerns actual path-law probabilities. -/
def interval_bridge : Prop := ∀ (N : ℕ), 1 ≤ N →
  ∀ p hp hp1 (i : RuinState N),
    ((integerLaw p hp hp1 (i.val : ℤ))
      {ω | Markov.hittingTime {(N : ℤ)} ω < Markov.hittingTime {0} ω}).toReal =
      ruinExitProbability N p hp hp1 i

def hit_zero : Prop := ∀ p hp hp1,
  integerHittingProbability p hp hp1 0 = 1

def hit_positive : Prop := ∀ p hp hp1 (i : ℤ), 0 < i →
  integerHittingProbability p hp hp1 i =
    if 1 - p < p then ((1 - p) / p) ^ i.toNat else 1

def hit_negative : Prop := ∀ p hp hp1 (i : ℤ), i < 0 →
  integerHittingProbability p hp hp1 i =
    if p < 1 - p then (p / (1 - p)) ^ (-i).toNat else 1

/-- Strictly positive return, not the immediate zero-time entrance. -/
def positive_return : Prop := ∀ p hp hp1,
  (Markov.returnProbability (integerKernel p hp hp1) 0).toReal = 2 * min p (1 - p)

end IntegerHittingSpec
end
end P207.Walk
