import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.AbsoluteContinuity

/-! Independent statements for `paper.tex:4890–4900`.

The reference is an arbitrary positive measure on the same sigma-algebra.
The shared scalar singularity predicate means that partition variation is
concentrated on a measurable reference-null set. No density, completeness,
or sigma-finiteness hypothesis is present. The assertions hold for all
normed-group-valued measures, and therefore include every finite real or
complex scalar measure of the manuscript without extra assumptions.
-/

open Set MeasureTheory

universe u v

namespace Specs.D11.Ch15.ACSingularZero

open Specs.D11.Ch15.AbsoluteContinuity
open Specs.D11.Ch14.ScalarInterfaces

def ac_singular_zero : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (μ : Measure α),
    scalarAbsolutelyContinuous_value ν μ →
    scalarPositiveSingular_value ν μ → ν = 0

def decomposition_unique : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (μ : Measure α)
    (a₁ s₁ a₂ s₂ : VectorMeasure α K),
    ν = a₁ + s₁ → ν = a₂ + s₂ →
    scalarAbsolutelyContinuous_value a₁ μ → scalarPositiveSingular_value s₁ μ →
    scalarAbsolutelyContinuous_value a₂ μ → scalarPositiveSingular_value s₂ μ →
    a₁ = a₂ ∧ s₁ = s₂

end Specs.D11.Ch15.ACSingularZero
