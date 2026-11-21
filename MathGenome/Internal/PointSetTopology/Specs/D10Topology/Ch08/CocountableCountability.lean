import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.ElementaryTopologies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-! Independent statements for paper.tex, example d10:08:cocountable.
The underlying type is arbitrary, with its chapter 1 cocountable topology.
Uncountability means that the whole underlying set is not at most countable.
The positive assertions hold even without uncountability. -/

open Set TopologicalSpace
universe u
namespace Specs.D10Topology.Ch08.CocountableCountability

open Ch01.ElementaryTopologies

def cocountable_t1 : Prop :=
  ∀ X : Type u, @T1Space X (cocountableTopology X)

def cocountable_lindelof : Prop :=
  ∀ X : Type u, @LindelofSpace X (cocountableTopology X)

def cocountable_not_separable : Prop :=
  ∀ X : Type u, ¬ (univ : Set X).Countable →
    ¬ @SeparableSpace X (cocountableTopology X)

def cocountable_not_firstCountable : Prop :=
  ∀ X : Type u, ¬ (univ : Set X).Countable →
    ¬ CountabilityConventions.firstCountableValue (cocountableTopology X)

def cocountable_singleton_not_gdelta : Prop :=
  ∀ X : Type u, ¬ (univ : Set X).Countable → ∀ x : X,
    ¬ @IsGδ X (cocountableTopology X) ({x} : Set X)

end Specs.D10Topology.Ch08.CocountableCountability
