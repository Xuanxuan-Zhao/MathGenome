import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.ACSingularZero

/-! Independent specification of paper.tex:4903–4923.

The reference is arbitrary. For real and complex targets, finiteness of
variation is a conclusion, with no added hypothesis. The witness is a
measurable reference-null set maximizing target variation, and the two parts
are the restrictions to its complement and to itself. Positivity means
nonnegative real values, also for a complex measure. No density or reference
sigma-finite support is included.
-/

open Set MeasureTheory

universe u v

namespace Specs.D11.Ch15.LebesgueDecompositionFiniteTarget

open Specs.D11.Ch14.TotalVariation Specs.D11.Ch14.ScalarInterfaces
open Specs.D11.Ch15.AbsoluteContinuity

/-- Complete finite decomposition, including uniqueness among all AC/singular
decompositions, even without separate finiteness assumptions on competitors. -/
def Decomposition {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) (μ : Measure α)
    (a s : VectorMeasure α K) : Prop :=
  IsFiniteMeasure (totalVariation_value a) ∧
  IsFiniteMeasure (totalVariation_value s) ∧
  ν = a + s ∧ scalarAbsolutelyContinuous_value a μ ∧
  scalarPositiveSingular_value s μ ∧
  ∀ a' s', ν = a' + s' → scalarAbsolutelyContinuous_value a' μ →
    scalarPositiveSingular_value s' μ → a' = a ∧ s' = s

def MaximalNullSet {α : Type u} [MeasurableSpace α]
    (ρ μ : Measure α) (B : Set α) : Prop :=
  MeasurableSet B ∧ μ B = 0 ∧
    ∀ E, MeasurableSet E → μ E = 0 → ρ E ≤ ρ B

def finite_variation_decomposition : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (μ : Measure α) [IsFiniteMeasure (totalVariation_value ν)],
    ∃ B, MaximalNullSet (totalVariation_value ν) μ B ∧
      Decomposition ν μ (ν.restrict Bᶜ) (ν.restrict B)

def signed_decomposition : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) (μ : Measure α),
    ∃ B, MaximalNullSet (totalVariation_value ν) μ B ∧
      Decomposition ν μ (ν.restrict Bᶜ) (ν.restrict B) ∧
      ((∀ E, MeasurableSet E → 0 ≤ ν E) →
        ∀ E, MeasurableSet E → 0 ≤ ν.restrict Bᶜ E ∧ 0 ≤ ν.restrict B E)

def complex_decomposition : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α) (μ : Measure α),
    ∃ B, MaximalNullSet (totalVariation_value ν) μ B ∧
      Decomposition ν μ (ν.restrict Bᶜ) (ν.restrict B) ∧
      ((∀ E, MeasurableSet E → ∃ r : ℝ, 0 ≤ r ∧ ν E = (r : ℂ)) →
        ∀ E, MeasurableSet E →
          (∃ r : ℝ, 0 ≤ r ∧ ν.restrict Bᶜ E = (r : ℂ)) ∧
          (∃ r : ℝ, 0 ≤ r ∧ ν.restrict B E = (r : ℂ)))

end Specs.D11.Ch15.LebesgueDecompositionFiniteTarget
