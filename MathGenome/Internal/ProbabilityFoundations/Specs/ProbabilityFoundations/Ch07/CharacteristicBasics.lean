import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.LawsAndTransfer

/-! Independent statements for Proposition 7.1 and its independent-sum consequence.
All Euclidean dimensions, including zero, are allowed. The ambient probability
space carries its original sigma algebra and need not be complete. -/

open MeasureTheory
open scoped ComplexConjugate

namespace Specs.ProbabilityFoundations.Ch07.CharacteristicBasics

open _root_.ProbabilityFoundations.Ch07
open TransformObjects
open Ch01.LawsAndTransfer (lawValue)
open Ch02.IndependenceInterfaces (IndependentRandomElementsValue)

universe u v

def UniformContinuity : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)) [IsProbabilityMeasure μ],
    UniformContinuous (characteristicFunctionValue μ)

def Normalization : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)) [IsProbabilityMeasure μ],
    characteristicFunctionValue μ 0 = 1

def ConjugateSymmetry : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)) [IsProbabilityMeasure μ] (t : Euclidean d),
    characteristicFunctionValue μ (-t) = conj (characteristicFunctionValue μ t)

def ModulusBound : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)) [IsProbabilityMeasure μ] (t : Euclidean d),
    ‖characteristicFunctionValue μ t‖ ≤ 1

def PositiveDefiniteness : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)) [IsProbabilityMeasure μ],
    isPositiveDefiniteValue (characteristicFunctionValue μ)

def ConvolutionFormula : Prop :=
  ∀ {d : ℕ} (μ ν : Measure (Euclidean d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : Euclidean d),
    characteristicFunctionValue (convolutionValue μ ν) t =
      characteristicFunctionValue μ t * characteristicFunctionValue ν t

def IndependentSumFormula : Prop :=
  ∀ {d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → Euclidean d),
    Measurable X → Measurable Y → ProbabilityTheory.IndepFun X Y P →
    ∀ t : Euclidean d,
      characteristicFunctionValue (lawValue P (fun ω => X ω + Y ω)) t =
        characteristicFunctionValue (lawValue P X) t *
          characteristicFunctionValue (lawValue P Y) t

/-- Every finite subfamily of an arbitrary mutually independent family;
empty subfamilies give the characteristic function of the zero vector. -/
def IndependentFiniteSumFormula : Prop :=
  ∀ {d : ℕ} {Ω : Type u} {I : Type v} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : I → Ω → Euclidean d),
    (∀ i, Measurable (X i)) → IndependentRandomElementsValue P X →
    ∀ (s : Finset I) (t : Euclidean d),
      characteristicFunctionValue (lawValue P (fun ω => ∑ i ∈ s, X i ω)) t =
        ∏ i ∈ s, characteristicFunctionValue (lawValue P (X i)) t

end Specs.ProbabilityFoundations.Ch07.CharacteristicBasics
