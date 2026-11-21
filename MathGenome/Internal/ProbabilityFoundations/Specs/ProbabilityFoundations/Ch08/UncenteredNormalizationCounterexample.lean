import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

namespace ProbabilityFoundations.Ch08.UncenteredNormalizationCounterexample

/-- The deterministic sequence in the example, with indices starting at one. -/
def oneVariable {Ω : Type*} (_k : ℕ) (_ω : Ω) : ℝ := 1

/-- The first `n` terms, namely `X₁ + ⋯ + Xₙ`; the empty sum is zero. -/
def partialSum {Ω : Type*} (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, oneVariable (k + 1) ω

/-- The uncentered normalization from §8.1. -/
noncomputable def normalizedSum {Ω : Type*} (p : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  partialSum n ω / (n : ℝ) ^ (1 / p)

end ProbabilityFoundations.Ch08.UncenteredNormalizationCounterexample

namespace Specs.ProbabilityFoundations.Ch08.UncenteredNormalizationCounterexample

open _root_.ProbabilityFoundations.Ch08.UncenteredNormalizationCounterexample

/-- The tail hypothesis holds for the independent identically distributed constant
sequence, but its uncentered normalized sums diverge and do not converge in probability
to zero. On a probability space, convergence in measure is convergence in probability. -/
def counterexampleType : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ), 1 < p → p < 2 →
    (∀ k : ℕ, Measurable (oneVariable (Ω := Ω) k)) ∧
    iIndepFun (oneVariable (Ω := Ω)) μ ∧
    (∀ j k : ℕ, IdentDistrib (oneVariable j) (oneVariable k) μ μ) ∧
    Tendsto (fun r : ℝ => r ^ p * μ.real {ω | r < |oneVariable 1 ω|})
      atTop (𝓝 0) ∧
    (∀ (n : ℕ) (ω : Ω), 0 < n → normalizedSum p n ω = (n : ℝ) ^ (1 - 1 / p)) ∧
    (∀ ω : Ω, Tendsto (fun n : ℕ => normalizedSum p n ω) atTop atTop) ∧
    ¬ TendstoInMeasure μ (normalizedSum p) atTop (fun _ => (0 : ℝ))

end Specs.ProbabilityFoundations.Ch08.UncenteredNormalizationCounterexample
