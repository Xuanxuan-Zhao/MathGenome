import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import Mathlib.MeasureTheory.Measure.Continuity

/-!
Independent statements for paper.tex:256–273. All evaluations have domain
exactly the given sigma-algebra. `AlgebraMeasure` supplies only the empty-set
and binary disjoint-union laws; countable additivity is a conclusion/predicate,
never a field assumed of the input. Infinite values and empty spaces are allowed.
The proof `hA` merely views the given sigma-algebra as an algebra.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u

namespace D11.Ch01.CountableAdditivityCriterion

open D11.Ch01.MeasureDefinitions

variable {α : Type u} [MeasurableSpace α]
  {hA : IsSetAlgebra {s : Set α | MeasurableSet s}}

/-- Countable additivity on the original measurable domain. -/
def CountablyAdditive (p : AlgebraMeasure _ hA) : Prop :=
  ∀ E : ℕ → MeasurableDomain α,
    Pairwise (fun i j => Disjoint (E i).1 (E j).1) →
    p.value ⟨⋃ n, (E n).1, MeasurableSet.iUnion fun n => (E n).2⟩ =
      ∑' n, p.value (E n)

/-- Continuity from below, including sequences with an infinite limiting mass. -/
def ContinuousFromBelow (p : AlgebraMeasure _ hA) : Prop :=
  ∀ E : ℕ → MeasurableDomain α, Monotone (fun n => (E n).1) →
    Tendsto (fun n => p.value (E n)) atTop
      (𝓝 (p.value ⟨⋃ n, (E n).1, MeasurableSet.iUnion fun n => (E n).2⟩))

/-- Continuity from above only at the empty set. No finite-value clause is built in. -/
def ContinuousAtEmpty (p : AlgebraMeasure _ hA) : Prop :=
  ∀ E : ℕ → MeasurableDomain α, Antitone (fun n => (E n).1) →
    (⋂ n, (E n).1) = ∅ → Tendsto (fun n => p.value (E n)) atTop (𝓝 0)

end D11.Ch01.CountableAdditivityCriterion

namespace Specs.D11.Ch01.CountableAdditivityCriterion

open _root_.D11.Ch01.MeasureDefinitions
open _root_.D11.Ch01.CountableAdditivityCriterion

def countablyAdditive_iff_continuousFromBelow : Prop :=
  ∀ {α : Type u} [MeasurableSpace α]
    (hA : IsSetAlgebra {s : Set α | MeasurableSet s}) (p : AlgebraMeasure _ hA),
    CountablyAdditive p ↔ ContinuousFromBelow p

def countablyAdditive_of_continuousAtEmpty : Prop :=
  ∀ {α : Type u} [MeasurableSpace α]
    (hA : IsSetAlgebra {s : Set α | MeasurableSet s}) (p : AlgebraMeasure _ hA),
    ContinuousAtEmpty p → CountablyAdditive p

def continuousAtEmpty_of_countablyAdditive_of_finite : Prop :=
  ∀ {α : Type u} [MeasurableSpace α]
    (hA : IsSetAlgebra {s : Set α | MeasurableSet s}) (p : AlgebraMeasure _ hA),
    CountablyAdditive p → p.value ⟨univ, MeasurableSet.univ⟩ < ∞ →
      ContinuousAtEmpty p

def finite_countablyAdditive_iff_continuousAtEmpty : Prop :=
  ∀ {α : Type u} [MeasurableSpace α]
    (hA : IsSetAlgebra {s : Set α | MeasurableSet s}) (p : AlgebraMeasure _ hA),
    p.value ⟨univ, MeasurableSet.univ⟩ < ∞ →
      (CountablyAdditive p ↔ ContinuousAtEmpty p)

end Specs.D11.Ch01.CountableAdditivityCriterion
