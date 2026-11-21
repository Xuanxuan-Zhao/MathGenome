import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityBounds
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces
import Mathlib.Probability.Moments.Covariance

/-! Independent statements for paper.tex:2732–2741 (`prop:weak-var`).
The sums run from 1 through n. No condition is placed on the unused variable X₀.
L² convergence uses the source's moment convention (paper.tex:678–681),
including membership in L². The measurable space is not assumed complete. -/
open MeasureTheory Filter
open scoped ENNReal Topology

universe u
namespace Specs.ProbabilityFoundations.Ch08.VarianceWeakLaw
open Specs.ProbabilityFoundations.Ch01.ProbabilityBounds
open Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces

noncomputable def partialSum {Ω : Type u} (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.Icc 1 n, X k ω

noncomputable def centeredAverage {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (partialSum X n ω - ∫ t, partialSum X n t ∂P) / (n : ℝ)

/-- Exact normalized centered second moment under pairwise zero covariance. -/
def centeredSecondMomentType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ),
    (∀ k, 1 ≤ k → Measurable (X k)) →
    (∀ k, 1 ≤ k → MemLp (X k) 2 P) →
    (∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → ProbabilityTheory.covariance (X i) (X j) P = 0) →
    ∀ n, 1 ≤ n →
      (∫ ω, |centeredAverage P X n ω| ^ 2 ∂P) =
        (n : ℝ) ^ (-2 : ℤ) * ∑ k ∈ Finset.Icc 1 n, realVarianceValue P (X k)

/-- Variance weak law: L² membership, convergence of second moments, and probability convergence. -/
def varianceWeakLawType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ),
    (∀ k, 1 ≤ k → Measurable (X k)) →
    (∀ k, 1 ≤ k → MemLp (X k) 2 P) →
    (∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → ProbabilityTheory.covariance (X i) (X j) P = 0) →
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-2 : ℤ) *
      ∑ k ∈ Finset.Icc 1 n, realVarianceValue P (X k)) atTop (𝓝 0) →
    (∀ n, MemLp (centeredAverage P X n) 2 P) ∧
    Tendsto (fun n => ∫ ω, |centeredAverage P X n ω| ^ 2 ∂P) atTop (𝓝 0) ∧
    ConvergesInProbabilityValue P (centeredAverage P X) (fun _ => 0)

end Specs.ProbabilityFoundations.Ch08.VarianceWeakLaw
