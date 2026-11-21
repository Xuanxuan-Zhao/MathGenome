import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.CylinderFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceJointLaws

/-!
Theorem `thm:independent-product`, paper.tex:1332–1341.
All products below use the canonical product measurable structure, identified
with `cylinderSigma` by the upstream `cylinderSigma_eq_pi`. Thus the statements
concern exactly the cylinder sigma-algebra, including empty index sets, with
arbitrary specified measurable coordinate spaces and no completion.
-/

open MeasureTheory
open ProbabilityFoundations.Ch05.CylinderFramework

namespace Specs.ProbabilityFoundations.Ch05.IndependentProduct

universe u v w z

/-- Finite products of the specified probabilities are consistent, including
restriction to the empty support. -/
def FiniteProductConsistency : Prop :=
  ∀ {I : Type u} (S : I → Type v) [∀ i, MeasurableSpace (S i)]
    (μi : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (μi i)],
    Consistent S (fun F => Measure.pi (fun i : F => μi i))

/-- A probability on the product is determined by all its finite-dimensional
laws. No independence or regularity assumptions enter this assertion. -/
def FiniteDimensionalUniqueness : Prop :=
  ∀ {I : Type u} (S : I → Type v) [∀ i, MeasurableSpace (S i)]
    (μ ν : Measure (ProductSpace S)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    (∀ F, Measure.map (finiteProjection S F) μ =
      Measure.map (finiteProjection S F) ν) → μ = ν

/-- Independence together with the prescribed coordinate laws is equivalent
to the product identity for every finite-dimensional law. -/
def IndependenceCharacterization : Prop :=
  ∀ {I : Type u} (S : I → Type v) [∀ i, MeasurableSpace (S i)]
    (μi : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (μi i)]
    (ν : Measure (ProductSpace S)) [IsProbabilityMeasure ν],
    ((∀ i, Measure.map (fun x : ProductSpace S => x i) ν = μi i) ∧
      Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue ν
        (fun i (x : ProductSpace S) => x i)) ↔
    ∀ F, Measure.map (finiteProjection S F) ν = Measure.pi (fun i : F => μi i)

/-- Existence and uniqueness of a probability with the prescribed independent
coordinates. The probability certificate binds the independence predicate. -/
def IndependentProductExistenceUniqueness : Prop :=
  ∀ {I : Type u} (S : I → Type v) [∀ i, MeasurableSpace (S i)]
    (μi : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (μi i)],
    ∃! ν : Measure (ProductSpace S), ∃ hν : IsProbabilityMeasure ν,
      letI := hν
      (∀ i, Measure.map (fun x : ProductSpace S => x i) ν = μi i) ∧
        Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue ν
          (fun i (x : ProductSpace S) => x i)

/-- Processes on different probability spaces have equal product laws if all
their finite-dimensional laws agree. The index type may be arbitrary. -/
def ProcessLawDetermination : Prop :=
  ∀ {I : Type u} {Ω : Type w} {Ω' : Type z}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (S : I → Type v) [∀ i, MeasurableSpace (S i)]
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ∀ i, Ω → S i) (Y : ∀ i, Ω' → S i),
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) →
    (∀ F : Finset I,
      Measure.map (fun ω (i : F) => X i ω) P =
        Measure.map (fun ω (i : F) => Y i ω) Q) →
    Measure.map (fun ω i => X i ω) P = Measure.map (fun ω i => Y i ω) Q

end Specs.ProbabilityFoundations.Ch05.IndependentProduct
