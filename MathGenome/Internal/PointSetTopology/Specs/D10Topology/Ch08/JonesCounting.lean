import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import Mathlib.Topology.Constructions
import Mathlib.SetTheory.Cardinal.Order

/-!
Independent specification of paper.tex, d10:08:jones (lines 1107–1112).
The subsets D and E carry their actual subtype cardinalities; E carries
the induced topology. Normality does not include T1. Empty spaces and
finite or empty D and E are allowed.
-/

open Set
universe u

namespace Specs.D10Topology.Ch08.JonesCounting

/-- The injection underlying Jones's counting argument. -/
def normal_closed_discrete_powerset_embedding : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [NormalSpace X]
    (D E : Set X) [DiscreteTopology E], Dense D → IsClosed E →
      Nonempty (Set E ↪ Set D)

/-- Quantitative bound forced by normality and density. -/
def normal_closed_discrete_cardinal_bound : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [NormalSpace X]
    (D E : Set X) [DiscreteTopology E], Dense D → IsClosed E →
      (2 : Cardinal) ^ Cardinal.mk E ≤ (2 : Cardinal) ^ Cardinal.mk D

/-- Jones's lemma, with no T1 hypothesis on the ambient space. -/
def jones_counting : Prop :=
  ∀ {X : Type u} [TopologicalSpace X]
    (D E : Set X) [DiscreteTopology E], Dense D → IsClosed E →
      (2 : Cardinal) ^ Cardinal.mk D ≤ Cardinal.mk E →
        ¬ Ch07.SeparationConventions.normalValue X

end Specs.D10Topology.Ch08.JonesCounting
