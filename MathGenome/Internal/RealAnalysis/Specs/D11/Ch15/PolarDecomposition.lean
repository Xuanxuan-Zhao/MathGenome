import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.RNSignedComplex

/-! Independent statements of polar decomposition, paper.tex:4983–4996.
The original measurable structure is arbitrary, and variation is the shared
partition variation. No nonzero, completeness, or sigma-finiteness assumption
is imposed on the scalar measure. Everywhere unimodularity strengthens the
stated a.e. property; uniqueness concerns all integrable representing densities.
-/

open Set MeasureTheory
universe u

namespace Specs.D11.Ch15.PolarDecomposition

open Specs.D11.Ch14.TotalVariation

def polar_complex : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (ν : ComplexMeasure X),
    ∃ u : X → ℂ, Measurable u ∧ Integrable u (totalVariation_value ν) ∧
      (∀ x, ‖u x‖ = 1) ∧
      (∀ E, MeasurableSet E → ν E = ∫ x in E, u x ∂(totalVariation_value ν)) ∧
      ∀ v : X → ℂ, Integrable v (totalVariation_value ν) →
        (∀ E, MeasurableSet E → ν E = ∫ x in E, v x ∂(totalVariation_value ν)) →
        u =ᵐ[totalVariation_value ν] v

def polar_signed : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (ν : SignedMeasure X),
    ∃ u : X → ℝ, Measurable u ∧ Integrable u (totalVariation_value ν) ∧
      (∀ x, u x = -1 ∨ u x = 1) ∧
      (∀ E, MeasurableSet E → ν E = ∫ x in E, u x ∂(totalVariation_value ν)) ∧
      ∀ v : X → ℝ, Integrable v (totalVariation_value ν) →
        (∀ E, MeasurableSet E → ν E = ∫ x in E, v x ∂(totalVariation_value ν)) →
        u =ᵐ[totalVariation_value ν] v

def zero_complex : Prop :=
  ∀ {X : Type u} [MeasurableSpace X],
    Measurable (fun _ : X => (1 : ℂ)) ∧
      Integrable (fun _ : X => (1 : ℂ)) (totalVariation_value (0 : ComplexMeasure X)) ∧
      (∀ _x : X, ‖(1 : ℂ)‖ = 1) ∧
      ∀ E : Set X, MeasurableSet E →
        (0 : ComplexMeasure X) E =
          ∫ _ in E, (1 : ℂ) ∂(totalVariation_value (0 : ComplexMeasure X))

def zero_signed : Prop :=
  ∀ {X : Type u} [MeasurableSpace X],
    Measurable (fun _ : X => (1 : ℝ)) ∧
      Integrable (fun _ : X => (1 : ℝ)) (totalVariation_value (0 : SignedMeasure X)) ∧
      (∀ _x : X, (1 : ℝ) = -1 ∨ (1 : ℝ) = 1) ∧
      ∀ E : Set X, MeasurableSet E →
        (0 : SignedMeasure X) E =
          ∫ _ in E, (1 : ℝ) ∂(totalVariation_value (0 : SignedMeasure X))

end Specs.D11.Ch15.PolarDecomposition
