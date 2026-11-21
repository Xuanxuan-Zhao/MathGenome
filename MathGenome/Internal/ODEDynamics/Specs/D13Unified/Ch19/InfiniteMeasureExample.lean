import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
Independent specification of Chapter 19's example "Finiteness cannot be dropped".
The standard `Int.instMeasurableSpace` is `⊤`, so every subset of ℤ is measurable.
The measure below is the native counting measure, not a probability measure.
Natural iterates and measure preservation use the canonical upstream definitions.
-/

namespace Specs.D13Unified.Ch19.InfiniteMeasureExample

open Set MeasureTheory
open scoped ENNReal
open Specs.D13Unified.Ch15.DiscreteDefinitions
open Specs.D13Unified.Ch19.MeasureDefinitions

def translationType := ℤ → ℤ

def translation : translationType := fun z => z + 1

def translation_preserves_countStatement : Prop :=
  PreservesMeasure translation (Measure.count : Measure ℤ)

def count_univ_infiniteStatement : Prop :=
  (Measure.count : Measure ℤ) Set.univ = ∞

def count_zero_singletonStatement : Prop :=
  (Measure.count : Measure ℤ) {0} = 1

def iterate_translationStatement : Prop :=
  ∀ (n : ℕ) (z : ℤ), iterate translation n z = z + (n : ℤ)

def positive_iterate_singleton_disjointStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    (iterate translation n '' ({0} : Set ℤ)) ∩ {0} = ∅

def no_positive_returnStatement : Prop :=
  ∀ z ∈ ({0} : Set ℤ), ∀ n : ℕ, 0 < n →
    iterate translation n z ∉ ({0} : Set ℤ)

/-- Even the almost-everywhere conclusion of recurrence is false for this
positive-measure set. The return times here are strictly positive. -/
def recurrence_failsStatement : Prop :=
  ¬ (∀ᵐ z ∂(Measure.count : Measure ℤ), z ∈ ({0} : Set ℤ) →
    Set.Infinite {n : ℕ | 0 < n ∧ iterate translation n z ∈ ({0} : Set ℤ)})

end Specs.D13Unified.Ch19.InfiniteMeasureExample
