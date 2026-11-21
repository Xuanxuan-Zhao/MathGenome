import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.LawsAndTransfer

/-!
Independent specifications for the law assertion of Theorem 2.2
(paper.tex:513–516,536–542). Each target space has its given measurable
structure, and function spaces have the product sigma-algebra. No topology,
completion, countability, or nonemptiness assumption is imposed. In particular,
`Fintype` includes empty and singleton index types, and the finite-subfamily
test below includes the empty finset.
-/

open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch02.IndependenceJointLaws

universe u v w

/-- For a finite family, the joint law is the product of its marginal laws
exactly when the generated sigma-algebras are mutually independent. -/
def finiteJointLawType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i), (∀ i, Measurable (X i)) →
    (IndependenceInterfaces.IndependentRandomElementsValue P X ↔
      Measure.map (fun ω i => X i ω) P = Measure.pi (fun i => Measure.map (X i) P))

/-- For an arbitrary family, independence is characterized by the product-law
identity for every finite joint law. The index type has no size restriction. -/
def finiteSubfamilyJointLawsType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i), (∀ i, Measurable (X i)) →
    (IndependenceInterfaces.IndependentRandomElementsValue P X ↔
      ∀ s : Finset I,
        Measure.map (fun ω (i : s) => X i ω) P =
          Measure.pi (fun i : s => Measure.map (X i) P))

end Specs.ProbabilityFoundations.Ch02.IndependenceJointLaws
