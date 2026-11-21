import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
Independent specification of Definition 1.1 (paper.tex, probability spaces and
monotone events). The measurable spaces are specified data. No completeness is
assumed. Probability measures are the canonical `Measure` with
`IsProbabilityMeasure`; no new probability-space structure is introduced.
-/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch01.ProbabilityObjects

universe u v

-- Expected types and values of the interfaces. The real target sigma algebra
-- is explicitly Borel. Bochner expectations follow Mathlib's totalization;
-- their probabilistic use for real/complex variables is on integrable inputs.
def isEventType := ∀ {Ω : Type u} [MeasurableSpace Ω], Set Ω → Prop
def isEventValue : isEventType := fun A => MeasurableSet A

def isRandomElementType :=
  ∀ {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MeasurableSpace S], (Ω → S) → Prop
def isRandomElementValue : isRandomElementType := fun X => Measurable X

def isRealRandomVariableType := ∀ {Ω : Type u} [MeasurableSpace Ω], (Ω → ℝ) → Prop
def isRealRandomVariableValue : isRealRandomVariableType :=
  fun {Ω} mΩ X => @Measurable Ω ℝ mΩ (borel ℝ) X

def realExpectationType := ∀ {Ω : Type u} [MeasurableSpace Ω], Measure Ω → (Ω → ℝ) → ℝ
noncomputable def realExpectationValue : realExpectationType := fun P X => ∫ ω, X ω ∂P

def complexExpectationType := ∀ {Ω : Type u} [MeasurableSpace Ω], Measure Ω → (Ω → ℂ) → ℂ
noncomputable def complexExpectationValue : complexExpectationType := fun P X => ∫ ω, X ω ∂P

def nonnegativeExpectationType :=
  ∀ {Ω : Type u} [MeasurableSpace Ω], Measure Ω → (Ω → ℝ≥0∞) → ℝ≥0∞
noncomputable def nonnegativeExpectationValue : nonnegativeExpectationType :=
  fun P X => ∫⁻ ω, X ω ∂P

def almostSurelyType := ∀ {Ω : Type u} [MeasurableSpace Ω], Measure Ω → (Ω → Prop) → Prop
def almostSurelyValue : almostSurelyType := fun P p => ∀ᵐ ω ∂P, p ω

-- Every theorem specification is its full proposition, never an axiom.
def probabilityNormalizationType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω),
    IsProbabilityMeasure P ↔ P Set.univ = 1

def realRandomVariableIffType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (X : Ω → ℝ),
    (@Measurable Ω ℝ _ (borel ℝ) X) ↔ Measurable X

def indicatorIntegrableType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω), MeasurableSet A →
    Integrable (A.indicator (fun _ => (1 : ℝ))) P ∧
    Integrable (A.indicator (fun _ => (1 : ℂ))) P

def realIndicatorExpectationType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω), MeasurableSet A →
    (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂P) = (P A).toReal

def complexIndicatorExpectationType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω), MeasurableSet A →
    (∫ ω, A.indicator (fun _ => (1 : ℂ)) ω ∂P) = ((P A).toReal : ℂ)

def nonnegativeIndicatorExpectationType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω), MeasurableSet A →
    (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) = P A

def almostSurelyIffMeasurableNullType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (p : Ω → Prop),
    (∀ᵐ ω ∂P, p ω) ↔
      ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ ∀ ω, ω ∉ N → p ω

def almostSurelyIffMeasurableOneType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : Ω → Prop),
    (∀ᵐ ω ∂P, p ω) ↔
      ∃ A : Set Ω, MeasurableSet A ∧ P A = 1 ∧ ∀ ω ∈ A, p ω

end Specs.ProbabilityFoundations.Ch01.ProbabilityObjects
