import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import Mathlib.MeasureTheory.Function.L2Space

/-! Independent statements for the finite identities in paper.tex §6.9, p207:W38.
The infinite-series criterion and convergence are assigned separately. -/

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207.L2OrthogonalIncrementsSpec

/-- Differences of two successive square-integrable values are in L². -/
def increment_memLp : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → Ω → ℝ), (∀ n, MemLp (M n) 2 μ) →
    ∀ k, MemLp (fun ω => M (k + 1) ω - M k ω) 2 μ

/-- Every square and cross product used in the orthogonality and energy identities
is genuinely integrable. No martingale assumption is needed for this assertion. -/
def products_integrable : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → Ω → ℝ), (∀ n, MemLp (M n) 2 μ) →
    (∀ n, Integrable (fun ω => M n ω ^ 2) μ) ∧
    (∀ k, Integrable (fun ω => (M (k + 1) ω - M k ω) ^ 2) μ) ∧
    (∀ i j, Integrable
      (fun ω => (M (i + 1) ω - M i ω) * (M (j + 1) ω - M j ω)) μ) ∧
    (∀ i j, Integrable (fun ω => M i ω * (M (j + 1) ω - M j ω)) μ)

/-- Distinct increments are orthogonal, in either order of their indices. -/
def increments_orthogonal : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ → (∀ n, MemLp (M n) 2 μ) →
    ∀ i j, i ≠ j →
      (∫ ω, (M (i + 1) ω - M i ω) * (M (j + 1) ω - M j ω) ∂μ) = 0

/-- The initial value may be random and nonzero. -/
def initial_increment_orthogonal : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ → (∀ n, MemLp (M n) 2 μ) →
    ∀ k, (∫ ω, M 0 ω * (M (k + 1) ω - M k ω) ∂μ) = 0

/-- The finite energy identity includes n = 0 and the initial second moment. -/
def energy_identity : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ → (∀ n, MemLp (M n) 2 μ) →
    ∀ n, (∫ ω, M n ω ^ 2 ∂μ) =
      (∫ ω, M 0 ω ^ 2 ∂μ) +
        ∑ k ∈ Finset.range n, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ

end P207.L2OrthogonalIncrementsSpec
