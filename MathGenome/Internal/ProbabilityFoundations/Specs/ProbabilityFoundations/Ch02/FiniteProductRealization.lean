import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
import Mathlib.MeasureTheory.Constructions.Pi

/-!
Independent specifications for the realization and transformation assertions of
Theorem 2.4 (paper.tex:558–574). Each factor has its specified measurable space;
the product has the product sigma-algebra. The finite index type may be empty.
The transformation assertion has an arbitrary index type and dependent source
and target spaces. Neither completeness nor topology is assumed.
-/

open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch02.FiniteProductRealization

universe u v w z

/-- The canonical product measure constructs the required probability space.
Its evaluation maps are measurable, mutually independent, and have precisely
the prescribed pushforward laws. -/
def finiteProductRealizationType : Prop :=
  ∀ {I : Type v} [Fintype I] {S : I → Type w}
    [∀ i, MeasurableSpace (S i)]
    (μ : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (μ i)],
    IsProbabilityMeasure (Measure.pi μ) ∧
      (∀ i, Measurable (fun x : (j : I) → S j => x i)) ∧
      IndependenceInterfaces.IndependentRandomElementsValue
        (Measure.pi μ) (fun i (x : (j : I) → S j) => x i) ∧
      (∀ i, Measure.map (fun x : (j : I) → S j => x i) (Measure.pi μ) = μ i)

/-- Coordinatewise measurable transformations of independent random elements
are measurable and independent, for every index set. -/
def independentRandomElementsCompType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} {T : I → Type z}
    [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSpace (T i)]
    (X : ∀ i, Ω → S i) (g : ∀ i, S i → T i),
    (∀ i, Measurable (X i)) → (∀ i, Measurable (g i)) →
    IndependenceInterfaces.IndependentRandomElementsValue P X →
      (∀ i, Measurable (g i ∘ X i)) ∧
      IndependenceInterfaces.IndependentRandomElementsValue P (fun i => g i ∘ X i)

end Specs.ProbabilityFoundations.Ch02.FiniteProductRealization
