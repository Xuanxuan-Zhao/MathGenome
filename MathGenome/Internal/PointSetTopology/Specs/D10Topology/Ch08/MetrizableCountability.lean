import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricTopology
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness

/-!
Independent statements for paper.tex, Theorem d10:08:metric-equivalence
(lines 1063–1070). Metrizability means existence of a metric inducing the
specified topology, as fixed in chapter 9. The canonical countability
classes have the paper's basis, dense-set and open-cover meanings by the
chapter 8 conventions. First countability uses the paper's local bases,
and compactness uses the chapter 5 finite-open-subcover definition.
All types, including empty types, are allowed.
-/

open TopologicalSpace
universe u

namespace Specs.D10Topology.Ch08.MetrizableCountability

def metrizable_secondCountable_iff_separable : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    Ch09.MetricConventions.Metrizable t →
      (SecondCountableTopology X ↔ SeparableSpace X)

def metrizable_secondCountable_iff_lindelof : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    Ch09.MetricConventions.Metrizable t →
      (SecondCountableTopology X ↔ LindelofSpace X)

def metrizable_separable_iff_lindelof : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    Ch09.MetricConventions.Metrizable t →
      (SeparableSpace X ↔ LindelofSpace X)

def metrizable_firstCountable : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    Ch09.MetricConventions.Metrizable t →
      Ch04.FirstCountableSequences.FirstCountable t

def compact_metrizable_secondCountable : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    Ch09.MetricConventions.Metrizable t →
      Ch05.Compactness.CoverCompact X → SecondCountableTopology X

end Specs.D10Topology.Ch08.MetrizableCountability
