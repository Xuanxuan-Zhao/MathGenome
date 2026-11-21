import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic

/-! Independent specification of paper.tex, Theorem `rare-poisson` (3203–3222).
Parameters in the closed unit interval include both endpoints. The nonnegative
finite supremum is zero for an empty row. Each row may have its own arbitrary,
not necessarily complete, probability space. -/
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace ProbabilityFoundations.Ch09

/-- Maximum success parameter, with zero as the empty-row value. -/
noncomputable def bernoulliRowMaximum {r : ℕ} (p : Fin r → Set.Icc (0 : ℝ) 1) : ℝ :=
  (Finset.univ.sup (fun j => (⟨(p j : ℝ), (p j).property.1⟩ : ℝ≥0))).val

/-- The Poisson law as a Borel probability measure on the real line. -/
noncomputable def poissonLaw (rate : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨(poissonMeasure rate).map (Nat.cast : ℕ → ℝ), inferInstance⟩

end ProbabilityFoundations.Ch09

namespace Specs.ProbabilityFoundations.Ch09.RareEventPoissonLimit
open _root_.ProbabilityFoundations.Ch09
universe u

/-- Full independent, non-identically distributed finite-row assertion. -/
def rareEventPoissonLimitType : Prop :=
  ∀ {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (r : ℕ → ℕ) (B : ∀ n, Fin (r n) → Ω n → ℝ)
    (p : ∀ n, Fin (r n) → Set.Icc (0 : ℝ) 1)
    (hB : ∀ n j, Measurable (B n j)),
    (∀ n, iIndepFun (B n) (P n)) →
    (∀ n j, (P n).map (B n j) = bernoulliMeasure (1 : ℝ) 0 (p n j)) →
    ∀ rate : ℝ≥0,
    Tendsto (fun n => bernoulliRowMaximum (p n)) atTop (𝓝 0) →
    Tendsto (fun n => ∑ j, (p n j : ℝ)) atTop (𝓝 (rate : ℝ)) →
    Tendsto (fun n => Ch06.WeakFramework.probabilityLawValue (P n)
      (fun ω => ∑ j, B n j ω) (by fun_prop)) atTop (𝓝 (poissonLaw rate))

def poissonLawMassType : Prop :=
  ∀ (rate : ℝ≥0) (k : ℕ), (poissonLaw rate : Measure ℝ) {(k : ℝ)} =
    ENNReal.ofReal (Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ k / (k.factorial : ℝ))

def poissonLawZeroType : Prop :=
  (poissonLaw 0 : Measure ℝ) = Measure.dirac 0

end Specs.ProbabilityFoundations.Ch09.RareEventPoissonLimit
