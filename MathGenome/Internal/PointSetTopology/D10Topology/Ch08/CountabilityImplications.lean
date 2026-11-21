import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityImplications
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Subspaces

/-!
Countability implications in paper.tex, d10:08:second-implications.
The Mathlib implications used here require no separation axioms. In particular,
separability of every subspace follows through its second countability.
-/

open Set TopologicalSpace
universe u v

namespace D10Topology.Ch08

variable {X : Type u} [t : TopologicalSpace X]

theorem secondCountable_firstCountable [SecondCountableTopology X] : FirstCountable t :=
  firstCountable_iff_mathlib.mpr inferInstance

theorem secondCountable_separable [SecondCountableTopology X] : SeparableSpace X :=
  inferInstance

theorem secondCountable_lindelof [SecondCountableTopology X] : LindelofSpace X :=
  inferInstance

theorem secondCountable_subspace [SecondCountableTopology X] (A : Set X) :
    SecondCountableTopology A :=
  Ch03.subspace_inclusion_embedding A |>.secondCountableTopology

theorem secondCountable_subspace_separable [SecondCountableTopology X] (A : Set X) :
    SeparableSpace A := by
  let := secondCountable_subspace A
  exact secondCountable_separable

theorem secondCountable_subspace_lindelof [SecondCountableTopology X] (A : Set X) :
    LindelofSpace A := by
  let := secondCountable_subspace A
  exact secondCountable_lindelof

theorem secondCountable_discrete_subspace_countable [SecondCountableTopology X]
    (A : Set X) [DiscreteTopology A] : A.Countable := by
  let := secondCountable_subspace_separable A
  exact Set.countable_coe_iff.mp (separableSpace_iff_countable.mp inferInstance)

theorem separable_disjoint_open_countable [SeparableSpace X]
    {ι : Type v} (U : ι → Set X)
    (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
    (ho : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty) : Countable ι :=
  hd.countable_of_isOpen_disjoint ho hne

theorem separable_disjoint_open_family_countable [SeparableSpace X]
    (F : Set (Set X)) (hd : F.PairwiseDisjoint id)
    (ho : ∀ U ∈ F, IsOpen U) (hne : ∀ U ∈ F, U.Nonempty) : F.Countable :=
  hd.countable_of_isOpen ho hne

end D10Topology.Ch08
