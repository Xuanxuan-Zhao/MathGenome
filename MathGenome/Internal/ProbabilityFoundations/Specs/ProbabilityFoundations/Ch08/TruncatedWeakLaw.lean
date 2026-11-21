import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.VarianceWeakLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic

/-! Independent statements for the truncated weak law, paper.tex:2743–2774.
All sums use indices 1 through n. There is no condition on the unused X₀.
The cutoff includes both endpoints, and its expectation is used even when
X₁ has no first absolute moment. No completeness of the probability space
or mutual independence is imposed. -/
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

universe u
namespace Specs.ProbabilityFoundations.Ch08.TruncatedWeakLaw
open Specs.ProbabilityFoundations.Ch08.VarianceWeakLaw
open Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces

/-- Symmetric, closed cutoff: in particular the atom at -a is retained. -/
noncomputable def symmetricTruncation {Ω : Type u} (X : Ω → ℝ) (a : ℝ) : Ω → ℝ :=
  {ω | |X ω| ≤ a}.indicator X

noncomputable def sampleAverage {Ω : Type u} (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => partialSum X n ω / (n : ℝ)

noncomputable def truncatedMean {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, symmetricTruncation X (n : ℝ) ω ∂P

/-- The first conclusion requires only the tail criterion, not integrability. -/
def truncatedWeakLawType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ),
    (∀ k, 1 ≤ k → Measurable (X k)) →
    (∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → IndepFun (X i) (X j) P) →
    (∀ k, 1 ≤ k → IdentDistrib (X k) (X 1) P P) →
    Tendsto (fun n : ℕ => (n : ℝ) * P.real {ω | (n : ℝ) < |X 1 ω|})
      atTop (𝓝 0) →
    ConvergesInProbabilityValue P
      (fun n ω => sampleAverage X n ω - truncatedMean P (X 1) n) (fun _ => 0)

/-- With a finite first absolute moment, the uncentered averages converge
in probability and in L¹, including integrability of every average and limit. -/
def integrableWeakLawType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ),
    (∀ k, 1 ≤ k → Measurable (X k)) →
    (∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → IndepFun (X i) (X j) P) →
    (∀ k, 1 ≤ k → IdentDistrib (X k) (X 1) P P) →
    Integrable (X 1) P →
    (∀ n, Integrable (sampleAverage X n) P) ∧
    Integrable (fun _ : Ω => ∫ ω, X 1 ω ∂P) P ∧
    ConvergesInProbabilityValue P (sampleAverage X) (fun _ => ∫ ω, X 1 ω ∂P) ∧
    Tendsto (fun n => ∫ ω, |sampleAverage X n ω - ∫ t, X 1 t ∂P| ∂P)
      atTop (𝓝 0)

end Specs.ProbabilityFoundations.Ch08.TruncatedWeakLaw
