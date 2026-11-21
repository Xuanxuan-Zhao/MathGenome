import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions

/-!
Independent statements for paper.tex, d10:08:regular-lindelof-normal.
Regularity and normality use the canonical predicates identified with the
paper's separation conditions in chapter 7, without an implicit T1 axiom.
Lindelöfness and second countability use the canonical classes identified
with the paper's cover and basis conditions in CountabilityConventions.
Neither statement assumes that the space or its closed subsets are nonempty.
-/

universe u

namespace Specs.D10Topology.Ch08.RegularLindelofNormal

def regular_lindelof_normal : Prop :=
  ∀ {X : Type u} [TopologicalSpace X],
    RegularSpace X → LindelofSpace X → NormalSpace X

def regular_secondCountable_t1_t4 : Prop :=
  ∀ {X : Type u} [TopologicalSpace X],
    RegularSpace X → SecondCountableTopology X → T1Space X →
      Ch07.SeparationConventions.t4Value X

end Specs.D10Topology.Ch08.RegularLindelofNormal
