import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.PositiveStieltjes
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.TotalVariation
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation

/-! Independent statements for the scalar bijection in paper.tex:3915–3980.
The measurable space on ℝ is Borel. Global BV refers to the upstream supremum
of classical partition sums. No equality between function variation and measure
total variation is assumed. Generic helper statements use finite-variation vector
measures; the real and complex conclusions have no additional hypothesis.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Specs.D11.Ch12.ScalarStieltjesCorrespondence

abbrev NBV_type := {E : Type*} → [NormedAddCommGroup E] → (ℝ → E) → Prop
def NBV_value : NBV_type := fun F =>
  Specs.D11.Ch12.GloballyBV_value F ∧
    (∀ x, ContinuousWithinAt F (Ici x) x) ∧ Tendsto F atBot (𝓝 0)

abbrev cumulative_type := {E : Type*} → [NormedAddCommGroup E] →
  VectorMeasure ℝ E → ℝ → E
def cumulative_value : cumulative_type := fun ν x => ν (Iic x)

abbrev initialVariation_type := {E : Type*} → [NormedAddCommGroup E] →
  (ℝ → E) → ℝ → ℝ≥0∞
noncomputable def initialVariation_value : initialVariation_type :=
  fun F x => ⨆ a : ℝ, Specs.D11.Ch12.variation_value F a x

abbrev stieltjesMeasure_type := {E : Type*} → [NormedAddCommGroup E] → [CompleteSpace E] →
  (ℝ → E) → VectorMeasure ℝ E
open scoped Classical in
noncomputable def stieltjesMeasure_value : stieltjesMeasure_type := fun F =>
  if h : BoundedVariationOn F univ then h.vectorMeasure else 0

abbrev component_type := (ℝ → ℝ) → ℝ → ℝ
noncomputable def positiveComponent_value : component_type := fun F x =>
  ((initialVariation_value F x).toReal + F x) / 2
noncomputable def negativeComponent_value : component_type := fun F x =>
  ((initialVariation_value F x).toReal - F x) / 2

def initialVariation_bridge : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (x : ℝ),
    initialVariation_value F x = eVariationOn F (Iic x)

def initialVariation_regular : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E), NBV_value F →
    (∀ x, initialVariation_value F x < ⊤) ∧
    (∀ x, ContinuousWithinAt (fun y => (initialVariation_value F y).toReal) (Ici x) x) ∧
    Tendsto (fun x => (initialVariation_value F x).toReal) atBot (𝓝 0)

def components_generators : Prop :=
  ∀ (F : ℝ → ℝ), NBV_value F →
    Specs.D11.Ch12.PositiveStieltjes.positiveGenerator_value (positiveComponent_value F) ∧
    Specs.D11.Ch12.PositiveStieltjes.positiveGenerator_value (negativeComponent_value F) ∧
    ∀ x, F x = positiveComponent_value F x - negativeComponent_value F x

def measure_finite : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (F : ℝ → E), NBV_value F →
    IsFiniteMeasure (stieltjesMeasure_value F).variation

def cumulative_measure : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (F : ℝ → E), NBV_value F →
    cumulative_value (stieltjesMeasure_value F) = F

def measure_interval : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (F : ℝ → E), NBV_value F →
    ∀ a b : ℝ, a < b → stieltjesMeasure_value F (Ioc a b) = F b - F a

def measure_atom : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (F : ℝ → E), NBV_value F →
    ∀ x : ℝ, stieltjesMeasure_value F {x} = F x - Function.leftLim F x

def cumulative_properties : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (ν : VectorMeasure ℝ E),
    IsFiniteMeasure ν.variation → NBV_value (cumulative_value ν)

def signed_cumulative_properties : Prop :=
  ∀ ν : SignedMeasure ℝ, NBV_value (cumulative_value ν)

def complex_cumulative_properties : Prop :=
  ∀ ν : ComplexMeasure ℝ, NBV_value (cumulative_value ν)

def measure_cumulative : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (ν : VectorMeasure ℝ E),
    IsFiniteMeasure ν.variation → stieltjesMeasure_value (cumulative_value ν) = ν

def signed_measure_cumulative : Prop :=
  ∀ ν : SignedMeasure ℝ, stieltjesMeasure_value (cumulative_value ν) = ν

def complex_measure_cumulative : Prop :=
  ∀ ν : ComplexMeasure ℝ, stieltjesMeasure_value (cumulative_value ν) = ν

def measure_unique : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (F : ℝ → E), NBV_value F →
    ∀ ν : VectorMeasure ℝ E,
      (∀ a b : ℝ, a < b → ν (Ioc a b) = F b - F a) → ν = stieltjesMeasure_value F

def signed_bijection : Prop :=
  ∃ e : {F : ℝ → ℝ // NBV_value F} ≃ SignedMeasure ℝ,
    (∀ F x, e F (Iic x) = F.val x) ∧
    (∀ ν x, (e.symm ν).val x = ν (Iic x))

def complex_bijection : Prop :=
  ∃ e : {F : ℝ → ℂ // NBV_value F} ≃ ComplexMeasure ℝ,
    (∀ F x, e F (Iic x) = F.val x) ∧
    (∀ ν x, (e.symm ν).val x = ν (Iic x))

end Specs.D11.Ch12.ScalarStieltjesCorrespondence
