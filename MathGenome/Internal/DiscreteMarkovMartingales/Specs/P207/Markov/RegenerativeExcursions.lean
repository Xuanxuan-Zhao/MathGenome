import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.StationaryReturnTimes
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.StrongMarkov
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

/-! Excursion vectors and their moments, paper.tex p207:W19, through the
paragraph before the strong law. Time zero belongs to the first hit. Infinity
is absorbing for successive hits, and the entire vector is zero whenever
one of its endpoints is infinite. No iid or moment certificate is assumed.
Stationarity and irreducibility already imply positive recurrence by W14;
we therefore do not impose a redundant positive-recurrence hypothesis. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory Classical
universe u v
namespace P207.Markov
noncomputable section

/-- Successive visits, starting with the first entrance (including time zero). -/
def returnEpoch {S : Type u} {Ω : Type v} (X : ℕ → Ω → S) (i : S) :
    ℕ → Ω → WithTop ℕ
  | 0 => hittingAfter X {i} 0
  | s + 1 => fun ω => if returnEpoch X i s ω = ⊤ then ⊤ else
      hittingAfter X {i} ((returnEpoch X i s ω).untopA + 1) ω

/-- The length, signed reward, and absolute reward of a complete excursion.
The product associates to the right: `(length, reward, absolute reward)`. -/
def excursionVector {S : Type u} {Ω : Type v} (X : ℕ → Ω → S) (i : S)
    (f : S → ℝ) (s : ℕ) (ω : Ω) : ℝ × ℝ × ℝ :=
  if returnEpoch X i s ω = ⊤ ∨ returnEpoch X i (s + 1) ω = ⊤ then (0, 0, 0)
  else
    let a := (returnEpoch X i s ω).untopA
    let b := (returnEpoch X i (s + 1) ω).untopA
    ((b - a : ℕ), ∑ k ∈ Finset.Ico a b, f (X k ω),
      ∑ k ∈ Finset.Ico a b, |f (X k ω)|)

/-- One complete excursion on a path, with zero on the no-return layer. -/
def singleExcursionVector {S : Type u} (i : S) (f : S → ℝ)
    (p : ℕ → S) : ℝ × ℝ × ℝ :=
  if returnTime i p = ⊤ then (0, 0, 0) else
    let b := (returnTime i p).untopA
    ((b : ℝ), ∑ k ∈ Finset.range b, f (p k),
      ∑ k ∈ Finset.range b, |f (p k)|)

namespace RegenerativeExcursionsSpec

def returnEpochType := {S : Type u} → {Ω : Type v} →
  (ℕ → Ω → S) → S → ℕ → Ω → WithTop ℕ
def returnEpochValue : returnEpochType.{u,v} := @returnEpoch

def excursionVectorType := {S : Type u} → {Ω : Type v} →
  (ℕ → Ω → S) → S → (S → ℝ) → ℕ → Ω → ℝ × ℝ × ℝ
def excursionVectorValue : excursionVectorType.{u,v} := @excursionVector

def singleExcursionVectorType := {S : Type u} → S → (S → ℝ) →
  (ℕ → S) → ℝ × ℝ × ℝ
def singleExcursionVectorValue : singleExcursionVectorType.{u} := @singleExcursionVector

def returnEpoch_isStoppingTime : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] [MeasurableSingletonClass S]
    {Ω : Type v} [m : MeasurableSpace Ω] (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m), Adapted ℱ X → ∀ i s,
    P207.IsDiscreteStoppingTime ℱ (returnEpoch X i s)

def measurable_excursionVector : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [m : MeasurableSpace Ω] (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m), Adapted ℱ X → ∀ i f s,
    Measurable (excursionVector X i f s)

def measurable_singleExcursionVector : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (i : S) (f : S → ℝ), Measurable (singleExcursionVector i f)

def returnEpoch_finite : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (π ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    Irreducible P → IsStationary P π → IsMarkovChain P ν X ℱ μ → ∀ i,
    ∀ᵐ ω ∂μ, ∀ s, returnEpoch X i s ω < ⊤

/-- Full assigned conclusion, for every realization, filtration and initial law.
`Summable` is the real formulation of the finite nonnegative π-weighted sum.
The three integrability conclusions make all displayed expectations ordinary
finite Bochner integrals. Identical distribution is stated against the actual
single-excursion law, stronger than pairwise equality of distributions. -/
def regenerative_excursions : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (π ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    Irreducible P → IsStationary P π → IsMarkovChain P ν X ℱ μ →
    ∀ (i : S) (f : S → ℝ), Summable (fun j => (π j).toReal * |f j|) →
    (∀ᵐ ω ∂μ, ∀ s, returnEpoch X i s ω < ⊤) ∧
    (∀ s, Measurable (excursionVector X i f s)) ∧
    iIndepFun (excursionVector X i f) μ ∧
    (∀ s, IdentDistrib (excursionVector X i f s) (singleExcursionVector i f)
      μ (statePathLaw P i)) ∧
    ∀ s,
      Integrable (fun ω => (excursionVector X i f s ω).1) μ ∧
      Integrable (fun ω => (excursionVector X i f s ω).2.1) μ ∧
      Integrable (fun ω => (excursionVector X i f s ω).2.2) μ ∧
      (∫ ω, (excursionVector X i f s ω).1 ∂μ) = 1 / (π i).toReal ∧
      (∫ ω, (excursionVector X i f s ω).2.1 ∂μ) =
        ∑' j, ((π j).toReal / (π i).toReal) * f j ∧
      (∫ ω, (excursionVector X i f s ω).2.2 ∂μ) =
        ∑' j, ((π j).toReal / (π i).toReal) * |f j|

end RegenerativeExcursionsSpec
end
end P207.Markov
