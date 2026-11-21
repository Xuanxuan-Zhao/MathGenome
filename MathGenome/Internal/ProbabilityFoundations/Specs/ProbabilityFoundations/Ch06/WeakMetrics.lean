import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Independent specification of the definitions in paper.tex, §6.9, lines 2034–2050.
The measurable space is exactly the Borel sigma algebra of an arbitrary metric
space. No separability, completeness or tightness assumption is imposed.
The enlargement is expressed by existence of a point at distance less than the
radius, which implements distance to a nonempty set and the empty-set convention.
Probabilities in the real infimum are their finite real-valued masses.
-/

open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch06.WeakMetrics

universe u
noncomputable section

def enlargementType := ∀ {S : Type u} [MetricSpace S], ℝ → Set S → Set S

def enlargementValue : enlargementType :=
  fun a A => {x | ∃ y ∈ A, dist x y < a}

def prokhorovAdmissibleType := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S], ProbabilityMeasure S → ProbabilityMeasure S → ℝ → Prop

def prokhorovAdmissibleValue : prokhorovAdmissibleType := fun {S} _ _ _ μ ν a =>
  0 < a ∧ ∀ A : Set S, MeasurableSet A →
    (μ : Measure S).real A ≤ (ν : Measure S).real (enlargementValue a A) + a ∧
    (ν : Measure S).real A ≤ (μ : Measure S).real (enlargementValue a A) + a

def prokhorovDistType := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S], ProbabilityMeasure S → ProbabilityMeasure S → ℝ

def prokhorovDistValue : prokhorovDistType := fun μ ν =>
  sInf {a : ℝ | prokhorovAdmissibleValue μ ν a}

def isBoundedLipschitzTestType := ∀ {S : Type u} [MetricSpace S], (S → ℝ) → Prop

/-- The two bounds are separate; their sum is not constrained to be at most one. -/
def isBoundedLipschitzTestValue : isBoundedLipschitzTestType := fun f =>
  (∀ x, |f x| ≤ 1) ∧ LipschitzWith 1 f

def boundedLipschitzDistType := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S], ProbabilityMeasure S → ProbabilityMeasure S → ℝ

def boundedLipschitzDistValue : boundedLipschitzDistType := fun {S} _ _ _ μ ν =>
  sSup {r : ℝ | ∃ f : S → ℝ, isBoundedLipschitzTestValue f ∧
    r = |(∫ x, f x ∂(μ : Measure S)) - ∫ x, f x ∂(ν : Measure S)|}

def enlargementEmptyType : Prop := ∀ {S : Type u} [MetricSpace S] (a : ℝ),
  enlargementValue a (∅ : Set S) = ∅

def enlargementInfDistType : Prop := ∀ {S : Type u} [MetricSpace S]
  (A : Set S) (_hA : A.Nonempty) (a : ℝ) (x : S),
  x ∈ enlargementValue a A ↔ Metric.infDist x A < a

def enlargementThickeningType : Prop := ∀ {S : Type u} [MetricSpace S] (a : ℝ) (A : Set S),
  enlargementValue a A = Metric.thickening a A

def enlargementOpenType : Prop := ∀ {S : Type u} [MetricSpace S] (a : ℝ) (A : Set S),
  IsOpen (enlargementValue a A)

def boundedLipschitzTestIffType : Prop := ∀ {S : Type u} [MetricSpace S] (f : S → ℝ),
  isBoundedLipschitzTestValue f ↔
    (∀ x, |f x| ≤ 1) ∧ ∀ x y, |f x - f y| ≤ dist x y

def boundedLipschitzTestIntegrableType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (f : S → ℝ),
  isBoundedLipschitzTestValue f → ∀ μ : ProbabilityMeasure S, Integrable f (μ : Measure S)

def prokhorovAdmissibleOneType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S),
  prokhorovAdmissibleValue μ ν 1

def prokhorovRadiiBddBelowType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S),
  BddBelow {a : ℝ | prokhorovAdmissibleValue μ ν a}

def prokhorovDistBoundsType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S),
  0 ≤ prokhorovDistValue μ ν ∧ prokhorovDistValue μ ν ≤ 1

def prokhorovDistLeType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) (a : ℝ),
  prokhorovAdmissibleValue μ ν a → prokhorovDistValue μ ν ≤ a

def boundedLipschitzValuesNonemptyType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S),
  Set.Nonempty {r : ℝ | ∃ f : S → ℝ, isBoundedLipschitzTestValue f ∧
    r = |(∫ x, f x ∂(μ : Measure S)) - ∫ x, f x ∂(ν : Measure S)|}

def boundedLipschitzValuesBddAboveType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S),
  BddAbove {r : ℝ | ∃ f : S → ℝ, isBoundedLipschitzTestValue f ∧
    r = |(∫ x, f x ∂(μ : Measure S)) - ∫ x, f x ∂(ν : Measure S)|}

def boundedLipschitzDistBoundsType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S),
  0 ≤ boundedLipschitzDistValue μ ν ∧ boundedLipschitzDistValue μ ν ≤ 2

def testIntegralLeBoundedLipschitzDistType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S) (f : S → ℝ),
  isBoundedLipschitzTestValue f →
    |(∫ x, f x ∂(μ : Measure S)) - ∫ x, f x ∂(ν : Measure S)| ≤
      boundedLipschitzDistValue μ ν

end
end Specs.ProbabilityFoundations.Ch06.WeakMetrics
