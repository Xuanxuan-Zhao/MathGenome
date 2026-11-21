import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Subspaces

/-!
Independent statements of paper.tex, d10:08:second-implications (1037–1042).
The canonical countability classes have their paper meanings by the upstream
conventions. First countability retains the paper's countable-local-base
predicate. Every subset has its induced topology, including the empty subset.
There are no separation assumptions. Countable means at most countable.
-/

open Set TopologicalSpace
universe u v

namespace Specs.D10Topology.Ch08.CountabilityImplications

def secondCountable_firstCountable : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] [SecondCountableTopology X],
    Ch04.FirstCountableSequences.FirstCountable t

def secondCountable_separable : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [SecondCountableTopology X], SeparableSpace X

def secondCountable_lindelof : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [SecondCountableTopology X], LindelofSpace X

def secondCountable_subspace : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [SecondCountableTopology X] (A : Set X),
    SecondCountableTopology A

def secondCountable_subspace_separable : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [SecondCountableTopology X] (A : Set X),
    SeparableSpace A

def secondCountable_subspace_lindelof : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [SecondCountableTopology X] (A : Set X),
    LindelofSpace A

def secondCountable_discrete_subspace_countable : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [SecondCountableTopology X]
    (A : Set X) [DiscreteTopology A], A.Countable

/-- An indexed formulation, with an arbitrary universe for the index type. -/
def separable_disjoint_open_countable : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [SeparableSpace X]
    {ι : Type v} (U : ι → Set X),
    Pairwise (fun i j => Disjoint (U i) (U j)) →
    (∀ i, IsOpen (U i)) → (∀ i, (U i).Nonempty) → Countable ι

/-- The literal formulation as a family of subsets of X. -/
def separable_disjoint_open_family_countable : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [SeparableSpace X] (F : Set (Set X)),
    F.PairwiseDisjoint id → (∀ U ∈ F, IsOpen U) →
    (∀ U ∈ F, U.Nonempty) → F.Countable

end Specs.D10Topology.Ch08.CountabilityImplications
