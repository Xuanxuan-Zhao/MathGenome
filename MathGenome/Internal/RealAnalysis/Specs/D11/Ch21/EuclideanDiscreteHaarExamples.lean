import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import Mathlib.MeasureTheory.Measure.Count

/-!
Independent statements for the Euclidean and discrete examples in
paper.tex:5992–5997. The Euclidean statement spells out the additive form
of the two Haar predicates, on exactly the canonical Borel measure.
Discrete groups have no cardinality restriction. Regularity formulas retain
extended-real infima and suprema, including sets of infinite mass.
-/

namespace Specs.D11.Ch21.EuclideanDiscreteHaarExamples

open Set MeasureTheory MeasurableSpace
open scoped ENNReal
universe u

/-- Both additive translation invariances, nonzero mass and precisely Radon regularity. -/
def euclidean_twoSidedHaar : Prop :=
  ∀ (d : ℕ) [NeZero d],
    let μ := (Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value d).trim
      (OpensMeasurableSpace.borel_le : borel (_root_.D11.Ch03.Point d) ≤ (inferInstance : MeasurableSpace (_root_.D11.Ch03.Point d)))
    μ ≠ 0 ∧ Specs.D11.Ch18.RadonPredicates.isRadonValue μ ∧
      (∀ (a : _root_.D11.Ch03.Point d) (E : Set _),
        MeasurableSet[borel _] E → μ ((fun x => a + x) '' E) = μ E) ∧
      (∀ (a : _root_.D11.Ch03.Point d) (E : Set _),
        MeasurableSet[borel _] E → μ ((fun x => x + a) '' E) = μ E)

def discrete_sets_open_borel : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [DiscreteTopology X] (E : Set X),
    IsOpen E ∧ MeasurableSet[borel X] E

def discrete_compact_iff_finite : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [DiscreteTopology X] (K : Set X),
    IsCompact K ↔ K.Finite

def count_outerRegular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [DiscreteTopology X] (E : Set X),
    @Measure.count X (borel X) E =
      ⨅ (U : Set X) (_ : E ⊆ U) (_ : IsOpen U), @Measure.count X (borel X) U

/-- In fact compact inner regularity holds on every subset of a discrete space. -/
def count_compactInnerRegular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [DiscreteTopology X] (E : Set X),
    @Measure.count X (borel X) E =
      ⨆ (K : Set X) (_ : K ⊆ E) (_ : IsCompact K), @Measure.count X (borel X) K

def count_twoSidedHaar : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [DiscreteTopology G],
    Specs.D11.Ch21.HaarDefinition.leftHaarValue (@Measure.count G (borel G)) ∧
      Specs.D11.Ch21.HaarDefinition.rightHaarValue (@Measure.count G (borel G))

end Specs.D11.Ch21.EuclideanDiscreteHaarExamples
