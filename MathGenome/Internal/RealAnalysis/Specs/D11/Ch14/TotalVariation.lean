import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarInterfaces
import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

/-! Independent statements for `paper.tex:4631–4669`.
The raw partition supremum is the shared `partitionVariation_value`.
The measure below must agree with it on the original measurable domain.
Finiteness is a conclusion for every real or complex countably additive map,
with no bounded-variation, density, or nonemptiness assumption.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v w

namespace Specs.D11.Ch14.TotalVariation

open Specs.D11.Ch14.ScalarInterfaces
open _root_.D11.Ch14.ScalarInterfaces

abbrev totalVariation_type :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K],
    VectorMeasure α K → Measure α

noncomputable def totalVariation_value : totalVariation_type.{u,v} :=
  VectorMeasure.variation

def totalVariation_apply : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (E : Set α), MeasurableSet E →
    totalVariation_value ν E = partitionVariation_value ν E

def totalVariation_partition_formula : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (E : Set α) (hE : MeasurableSet E),
    totalVariation_value ν E =
      ⨆ (P : Finpartition (⟨E,hE⟩ : Subtype MeasurableSet)),
        ∑ A ∈ P.parts, ENNReal.ofReal ‖ν A‖

def partitionVariation_empty : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K), partitionVariation_value ν ∅ = 0

def partitionVariation_countable_additivity : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    {ι : Type w} [Countable ι] (ν : VectorMeasure α K) (E : ι → Set α),
    (∀ i, MeasurableSet (E i)) → Pairwise (fun i j => Disjoint (E i) (E j)) →
    partitionVariation_value ν (⋃ i, E i) = ∑' i, partitionVariation_value ν (E i)

def norm_le_totalVariation : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (E : Set α),
    ENNReal.ofReal ‖ν E‖ ≤ totalVariation_value ν E

def totalVariation_null_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (E : Set α), MeasurableSet E →
    (totalVariation_value ν E = 0 ↔
      ∀ A, MeasurableSet A → A ⊆ E → ν A = 0)

def signed_finite : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α),
    IsFiniteMeasure (totalVariation_value ν)

def complex_finite : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α),
    IsFiniteMeasure (totalVariation_value ν)

def signed_partitionVariation_lt_top : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) (E : Set α),
    MeasurableSet E → partitionVariation_value ν E < ⊤

def complex_partitionVariation_lt_top : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α) (E : Set α),
    MeasurableSet E → partitionVariation_value ν E < ⊤

def complex_four_positive : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α),
    ∃ α₁ α₂ α₃ α₄ : Measure α,
      IsFiniteMeasure α₁ ∧ IsFiniteMeasure α₂ ∧
      IsFiniteMeasure α₃ ∧ IsFiniteMeasure α₄ ∧
      ∀ E : Set α, MeasurableSet E →
        ν E = ((α₁ E).toReal : ℂ) - ((α₂ E).toReal : ℂ) +
          Complex.I * (((α₃ E).toReal : ℂ) - ((α₄ E).toReal : ℂ))

/-- Explicitly retain applicability to maps whose domain is only Σ. -/
def source_signed_finite : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (p : SourceScalarMeasure α ℝ),
    ∃ μ : Measure α, IsFiniteMeasure μ ∧
      ∀ (E : Set α) (hE : MeasurableSet E),
        μ E = ⨆ (P : Finpartition (⟨E,hE⟩ : Subtype MeasurableSet)),
          ∑ A ∈ P.parts, ENNReal.ofReal ‖p.value A‖

def source_complex_finite : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (p : SourceScalarMeasure α ℂ),
    ∃ μ : Measure α, IsFiniteMeasure μ ∧
      ∀ (E : Set α) (hE : MeasurableSet E),
        μ E = ⨆ (P : Finpartition (⟨E,hE⟩ : Subtype MeasurableSet)),
          ∑ A ∈ P.parts, ENNReal.ofReal ‖p.value A‖

end Specs.D11.Ch14.TotalVariation
