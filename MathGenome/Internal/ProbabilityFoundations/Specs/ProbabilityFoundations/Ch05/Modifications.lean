import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent specifications for paper.tex §5.4, including continuity uniqueness.
The time space has its relative topology; in particular `Time 0` is a singleton.
No completeness, moment estimate, or completion of the probability space is used. -/

open MeasureTheory Set TopologicalSpace

universe u v w

namespace ProbabilityFoundations.Ch05

abbrev Time (T : ℝ) := Set.Icc (0 : ℝ) T

namespace ModificationsSpec

def modificationType :=
  ∀ {ι : Type u} {Ω : Type v} {S : Type w} [MeasurableSpace Ω],
    Measure Ω → (ι → Ω → S) → (ι → Ω → S) → Prop

/-- Equality with probability one separately at each fixed time. -/
def modificationValue : modificationType.{u, v, w} :=
  fun P X Y => ∀ t, P {ω | X t ω = Y t ω} = 1

def indistinguishableType := modificationType.{u, v, w}

/-- A single measurable event works simultaneously at every time. -/
def indistinguishableValue : indistinguishableType.{u, v, w} :=
  fun P X Y => ∃ G, MeasurableSet G ∧ P G = 1 ∧ ∀ ω ∈ G, ∀ t, X t ω = Y t ω

def continuousPathsType :=
  ∀ {ι : Type u} {Ω : Type v} {S : Type w}
    [TopologicalSpace ι] [MeasurableSpace Ω] [TopologicalSpace S],
    Measure Ω → (ι → Ω → S) → Prop

/-- Continuity on an explicitly measurable full-probability event. -/
def continuousPathsValue : continuousPathsType.{u, v, w} :=
  fun P X => ∃ G, MeasurableSet G ∧ P G = 1 ∧
    ∀ ω ∈ G, Continuous (fun t => X t ω)

def fixedTimeEqualityMeasurable : Prop :=
  ∀ {T : ℝ} {Ω : Type v} {S : Type w} [MeasurableSpace Ω]
    [MetricSpace S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    (X Y : Time T → Ω → S),
    (∀ t, Measurable (X t)) → (∀ t, Measurable (Y t)) →
    ∀ t, MeasurableSet {ω | X t ω = Y t ω}

def continuousModificationsUnique : Prop :=
  ∀ {T : ℝ} {Ω : Type v} {S : Type w} [MeasurableSpace Ω]
    [MetricSpace S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y Z : Time T → Ω → S),
    (∀ t, Measurable (X t)) → (∀ t, Measurable (Y t)) →
    (∀ t, Measurable (Z t)) →
    modificationValue P X Y → modificationValue P X Z →
    continuousPathsValue P Y → continuousPathsValue P Z →
    indistinguishableValue P Y Z

end ModificationsSpec
end ProbabilityFoundations.Ch05
