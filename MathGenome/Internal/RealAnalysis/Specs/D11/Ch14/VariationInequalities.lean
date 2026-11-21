import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.TotalVariation

/-! Independent statements for paper.tex:4671–4687 and 4743–4749.
The real and complex norm assertions use no bounded-variation hypothesis.
The two-point example explicitly uses the full sigma-algebra. -/

open Set MeasureTheory
open scoped ENNReal NNReal

universe u v

namespace Specs.D11.Ch14.VariationInequalities

open Specs.D11.Ch14.TotalVariation

abbrev variationNorm_type :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K],
    VectorMeasure α K → ℝ

noncomputable def variationNorm_value : variationNorm_type.{u,v} :=
  fun ν => (totalVariation_value ν univ).toReal

def variation_smul : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedField K]
    (c : K) (ν : VectorMeasure α K),
    totalVariation_value (c • ν) = ENNReal.ofReal ‖c‖ • totalVariation_value ν

def variation_add : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν η : VectorMeasure α K) (E : Set α), MeasurableSet E →
    totalVariation_value (ν + η) E ≤ totalVariation_value ν E + totalVariation_value η E

def restriction_apply : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (A E : Set α), MeasurableSet A → MeasurableSet E →
    ν.restrict A E = ν (E ∩ A)

def variation_restrict : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (A E : Set α), MeasurableSet A → MeasurableSet E →
    totalVariation_value (ν.restrict A) E = totalVariation_value ν (E ∩ A)

/-- These four clauses are the full norm axioms over the specified field.
The mass-to-real operation is justified by upstream finiteness in each application. -/
def normAxioms (K : Type v) [NormedField K] : Prop :=
  ∀ {α : Type u} [MeasurableSpace α],
    (∀ ν : VectorMeasure α K, 0 ≤ variationNorm_value ν) ∧
    (∀ ν : VectorMeasure α K, variationNorm_value ν = 0 ↔ ν = 0) ∧
    (∀ ν η : VectorMeasure α K,
      variationNorm_value (ν + η) ≤ variationNorm_value ν + variationNorm_value η) ∧
    (∀ (c : K) (ν : VectorMeasure α K),
      variationNorm_value (c • ν) = ‖c‖ * variationNorm_value ν)

def signed_norm_axioms : Prop := normAxioms.{u,0} ℝ

def complex_norm_axioms : Prop := normAxioms.{u,0} ℂ

/-- Any two-element underlying set, with every subset measurable. -/
def cancellation_example : Prop :=
  ∀ {α : Type u} (a b : α), a ≠ b → (univ : Set α) = {a,b} →
    letI : MeasurableSpace α := ⊤
    let ν : SignedMeasure α := VectorMeasure.dirac a 1 - VectorMeasure.dirac b 1
    ν univ = 0 ∧ totalVariation_value ν univ = 2 ∧ ν {a} = 1 ∧
      ¬ (totalVariation_value ν univ = 0)

end Specs.D11.Ch14.VariationInequalities
