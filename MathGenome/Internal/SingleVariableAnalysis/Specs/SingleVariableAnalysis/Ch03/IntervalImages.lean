import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.ClosedPreimage
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.IntermediateValues
import Mathlib.Topology.Connected.Basic
import Mathlib.Order.Interval.Set.OrdConnected

/-!
Independent specification for K03.03.interval_images, paper.tex:555–570.

The sets in a separation live in the domain subtype, so openness is relative
to that domain. Connectedness here permits the empty set: its canonical
Mathlib counterpart is `IsPreconnected`, not the nonempty `IsConnected`.
The interval predicate says exactly that every point between two members is
a member. No boundedness, closedness, openness or nonemptiness is imposed.
The range statements include functions defined intrinsically on a subtype.
-/
namespace Specs.SingleVariableAnalysis.Ch03.IntervalImages

open Specs.SingleVariableAnalysis.Ch03.Continuity
universe u v

def relativeConnectedType : Type (u + 1) :=
  {X : Type u} → [MetricSpace X] → Set X → Prop

def relativeConnectedValue : relativeConnectedType.{u} :=
  fun E => ¬ ∃ U V : Set E,
    IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧
      Disjoint U V ∧ U ∪ V = Set.univ

def realIntervalType : Type := Set ℝ → Prop

def realIntervalValue : realIntervalType :=
  fun I => ∀ ⦃a : ℝ⦄, a ∈ I → ∀ ⦃b : ℝ⦄, b ∈ I →
    ∀ ⦃x : ℝ⦄, a ≤ x → x ≤ b → x ∈ I

def relativeConnectedIffIsPreconnected : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X),
    relativeConnectedValue E ↔ IsPreconnected E

def realIntervalIffOrdConnected : Prop :=
  ∀ I : Set ℝ, realIntervalValue I ↔ Set.OrdConnected I

def realConnectedIffInterval : Prop :=
  ∀ I : Set ℝ, relativeConnectedValue I ↔ realIntervalValue I

def relativeConnectedImage : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X), relativeConnectedValue E →
    relativeContinuousValue f E → relativeConnectedValue (f '' E)

def connectedSpaceRange : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y), relativeConnectedValue (Set.univ : Set X) →
    relativeContinuousValue f Set.univ → relativeConnectedValue (Set.range f)

def continuousRealIntervalImage : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), realIntervalValue I →
    relativeContinuousValue f I → realIntervalValue (f '' I)

def continuousRealIntervalRange : Prop :=
  ∀ (I : Set ℝ) (f : I → ℝ), realIntervalValue I →
    relativeContinuousValue f Set.univ → realIntervalValue (Set.range f)

def relativeConnectedEmpty : Prop :=
  ∀ {X : Type u} [MetricSpace X], relativeConnectedValue (∅ : Set X)

def relativeConnectedSingleton : Prop :=
  ∀ {X : Type u} [MetricSpace X] (x : X), relativeConnectedValue ({x} : Set X)

def realIntervalEmpty : Prop := realIntervalValue ∅

def realIntervalSingleton : Prop := ∀ x : ℝ, realIntervalValue {x}

end Specs.SingleVariableAnalysis.Ch03.IntervalImages
