import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import Mathlib.Topology.Metrizable.Basic

/-!
Independent specification of Lemma 6.12 (`lem:p06-compact-base`),
paper.tex lines 1749–1783. The topology is the initial topology of all
bounded continuous real integral tests, and the sigma algebra is Borel.
There is no nonemptiness hypothesis: the statements include the empty space.
-/

open MeasureTheory TopologicalSpace

namespace Specs.ProbabilityFoundations.Ch06.CompactLawSpace

universe u

/-- Borel probability laws on a compact metric space are weakly compact. -/
def compactLawSpaceType : Prop :=
  ∀ {H : Type u} [MetricSpace H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H],
    @CompactSpace (ProbabilityMeasure H) (WeakFramework.weakTopologyValue (S := H))

/-- The same weak topology is metrizable, including when there are no laws. -/
def metrizableLawSpaceType : Prop :=
  ∀ {H : Type u} [MetricSpace H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H],
    @MetrizableSpace (ProbabilityMeasure H) (WeakFramework.weakTopologyValue (S := H))

end Specs.ProbabilityFoundations.Ch06.CompactLawSpace
