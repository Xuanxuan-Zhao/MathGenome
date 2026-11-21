import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformTopology

/-! Independent specification of paper.tex, `d10:12:uniformizable`.
The induced topology is the accepted entourage-section construction. Complete
regularity is the Chapter 7 point/closed-set separation property without T1.
There is no nonemptiness or point-separation assumption in the equivalence.
-/

universe u

namespace Specs.D10Topology.Ch12.UniformizableTopologies

def uniformTopology_completelyRegular : Prop :=
  ∀ {X : Type u} [UniformSpace X],
    @Ch07.SeparationConventions.completelyRegularValue X
      UniformTopology.uniformTopology

/-- Existence includes equality with the original topology, not merely
continuity of maps in one direction. -/
def uniformizable_iff_completelyRegular : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    (∃ uX : UniformSpace X, @UniformTopology.uniformTopology X uX = t) ↔
      Ch07.SeparationConventions.completelyRegularValue X

def separated_uniformTopology_tychonoff : Prop :=
  ∀ {X : Type u} [UniformSpace X], UniformConventions.Separated (X := X) →
    @Ch07.SeparationConventions.tychonoffValue X UniformTopology.uniformTopology

/-- Explicitly record the empty-space specialization of uniformizability. -/
def empty_uniformizable : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X] [IsEmpty X],
    ∃ uX : UniformSpace X, @UniformTopology.uniformTopology X uX = t

end Specs.D10Topology.Ch12.UniformizableTopologies
