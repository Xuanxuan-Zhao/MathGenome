import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.MetrizableCountability
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityImplications
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricTopology
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness

/-!
Theorem d10:08:metric-equivalence. A compatible metric supplies a
countably generated uniformity. Separability then gives second countability;
the Lindelöf implication uses countable subcovers of uniform balls.
The reverse implications are the general chapter 8 results.
There is no nonemptiness or completeness assumption.
-/

open TopologicalSpace
universe u

namespace D10Topology.Ch08

variable {X : Type u} [t : TopologicalSpace X]

theorem metrizable_secondCountable_iff_separable (hm : Ch09.Metrizable t) :
    SecondCountableTopology X ↔ SeparableSpace X := by
  rcases hm with ⟨d, rfl⟩
  let := d
  constructor
  · intro h
    let := h
    exact secondCountable_separable
  · intro h
    let := h
    exact UniformSpace.secondCountable_of_separable X

theorem metrizable_secondCountable_iff_lindelof (hm : Ch09.Metrizable t) :
    SecondCountableTopology X ↔ LindelofSpace X := by
  let : MetrizableSpace X := (Ch09.metrizable_iff_mathlib t).mp hm
  constructor
  · intro h
    let := h
    exact secondCountable_lindelof
  · intro h
    let := h
    infer_instance

theorem metrizable_separable_iff_lindelof (hm : Ch09.Metrizable t) :
    SeparableSpace X ↔ LindelofSpace X :=
  (metrizable_secondCountable_iff_separable hm).symm.trans
    (metrizable_secondCountable_iff_lindelof hm)

theorem metrizable_firstCountable (hm : Ch09.Metrizable t) : FirstCountable t := by
  rcases hm with ⟨d, rfl⟩
  exact firstCountable_iff_mathlib.mpr (Ch09.metric_first_countable d)

theorem compact_metrizable_secondCountable (hm : Ch09.Metrizable t)
    (hc : Ch05.CoverCompact X) : SecondCountableTopology X := by
  let : CompactSpace X := (Ch05.coverCompact_iff_compactSpace X).mp hc
  exact (metrizable_secondCountable_iff_lindelof hm).mpr inferInstance

end D10Topology.Ch08
