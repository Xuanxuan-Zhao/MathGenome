import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions

/-!
Independent statement of `paper.tex`, Theorem `d13:19:invariant-probability`.
The measurable structure is the Borel sigma algebra, and preservation is
the canonical Chapter 19 predicate: measurability together with equality
of the pushforward and the original measure, equivalently equality on
preimages of every Borel set.
-/

namespace Specs.D13Unified.Ch19

open MeasureTheory

/-- Every continuous self-map of a nonempty compact metric space admits
an invariant Borel probability measure. -/
def InvariantProbability : Prop :=
  ∀ (K : Type*) [MetricSpace K] [CompactSpace K] [Nonempty K]
    [MeasurableSpace K] [BorelSpace K] (T : K → K), Continuous T →
    ∃ ν : ProbabilityMeasure K, MeasureDefinitions.PreservesMeasure T (ν : Measure K)

end Specs.D13Unified.Ch19
