import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.Modifications
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! Specifications for the final example of paper.tex, Chapter 5.
Both the sample and time spaces carry the relative topology and Borel sigma-algebra
of the closed unit interval. `volume` is its canonical Lebesgue probability. -/
open MeasureTheory Set

namespace ProbabilityFoundations.Ch05.DiscontinuousModificationExampleSpec

abbrev Interval := Time 1

def processType := Interval → Interval → ℝ

noncomputable def spike : processType := fun t ω => if ω = t then 1 else 0

def zero : processType := fun _ _ => 0

def probability : Prop := IsProbabilityMeasure (volume : Measure Interval)

def coordinatesMeasurable : Prop :=
  (∀ t, Measurable (spike t)) ∧ (∀ t, Measurable (zero t))

/-- This includes empty collections, repeated times, and both endpoints. -/
def finiteAgreement : Prop :=
  ∀ (n : ℕ) (ts : Fin n → Interval),
    volume (Set.range ts) = 0 ∧
    ∀ ω ∉ Set.range ts, (fun i => spike (ts i) ω) = (fun i => zero (ts i) ω)

def finiteDimensionalLaws : Prop :=
  ∀ (n : ℕ) (ts : Fin n → Interval),
    Measure.map (fun ω i => spike (ts i) ω) volume =
      Measure.map (fun ω i => zero (ts i) ω) volume

def pathsDiscontinuous : Prop :=
  ∀ ω : Interval, ¬ ContinuousAt (fun t => spike t ω) ω

def zeroPathsContinuous : Prop :=
  ∀ ω : Interval, Continuous (fun t => zero t ω)

def modification : Prop := ModificationsSpec.modificationValue volume spike zero

def almostSurelyContinuous : Prop :=
  ModificationsSpec.continuousPathsValue volume zero

def notIndistinguishable : Prop :=
  ¬ ModificationsSpec.indistinguishableValue volume spike zero

end ProbabilityFoundations.Ch05.DiscontinuousModificationExampleSpec
