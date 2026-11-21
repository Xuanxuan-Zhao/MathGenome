import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarInterfaces
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-! Independent statements of the Jordan theorem, `paper.tex:4610`.
The variation in the last statement is the shared raw finite-partition
supremum. All scalar evaluations in the hypotheses are on measurable sets.
There is no nonemptiness or extra bounded-variation hypothesis. -/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace Specs.D11.Ch14.Jordan

open Specs.D11.Ch14.ScalarInterfaces

abbrev positivePart_type :=
  ∀ {α : Type u} [MeasurableSpace α], SignedMeasure α → Measure α
noncomputable def positivePart_value : positivePart_type.{u} :=
  fun ν => ν.toJordanDecomposition.posPart

abbrev negativePart_type :=
  ∀ {α : Type u} [MeasurableSpace α], SignedMeasure α → Measure α
noncomputable def negativePart_value : negativePart_type.{u} :=
  fun ν => ν.toJordanDecomposition.negPart

def jordan_finite : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α),
    IsFiniteMeasure (positivePart_value ν) ∧ IsFiniteMeasure (negativePart_value ν)

def jordan_decomposition : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α),
    positiveSingular_value (positivePart_value ν) (negativePart_value ν) ∧
    ∀ E : Set α, MeasurableSet E →
      ν E = (positivePart_value ν E).toReal - (negativePart_value ν E).toReal

def jordan_unique : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (μ η : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure η],
    positiveSingular_value μ η →
    (∀ E : Set α, MeasurableSet E → ν E = (μ E).toReal - (η E).toReal) →
    μ = positivePart_value ν ∧ η = negativePart_value ν

def jordan_hahn_formula : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) (P N : Set α),
    positiveSet_value ν P → negativeSet_value ν N →
    Disjoint P N → P ∪ N = univ →
    ∀ E : Set α, MeasurableSet E →
      positivePart_value ν E = ENNReal.ofReal (ν (E ∩ P)) ∧
      negativePart_value ν E = ENNReal.ofReal (-ν (E ∩ N))

def jordan_minimal : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (μ η : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure η],
    (∀ E : Set α, MeasurableSet E → ν E = (μ E).toReal - (η E).toReal) →
    positivePart_value ν ≤ μ ∧ negativePart_value ν ≤ η

def jordan_partition_variation : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (E : Set α), MeasurableSet E →
    partitionVariation_value ν E = positivePart_value ν E + negativePart_value ν E

end Specs.D11.Ch14.Jordan
