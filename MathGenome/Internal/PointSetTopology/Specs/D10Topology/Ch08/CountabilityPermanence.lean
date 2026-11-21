import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Subspaces
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.ContinuityTests

/-!
Independent statements for paper.tex, d10:08:permanence, subspaces and maps
(lines 1044–1048). Subsets have their canonical induced topology. First
countability uses the paper's countable neighborhood-base predicate already
fixed in chapter 4; the other conditions use the classes identified with the
paper's definitions in CountabilityConventions. No separation or nonemptiness
assumptions are imposed.
-/

open Set TopologicalSpace
universe u v

namespace Specs.D10Topology.Ch08.CountabilityPermanence
open _root_.Specs.D10Topology.Ch04.FirstCountableSequences

def firstCountable_subspace : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X], FirstCountable t →
    ∀ A : Set X, FirstCountable (inferInstance : TopologicalSpace A)

def lindelof_closed_subspace : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LindelofSpace X →
    ∀ A : Set X, IsClosed A → LindelofSpace A

def separable_open_subspace : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], SeparableSpace X →
    ∀ A : Set X, IsOpen A → SeparableSpace A

def separable_continuous_surjection : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y],
    SeparableSpace X → ∀ f : X → Y,
      Continuous f → Function.Surjective f → SeparableSpace Y

def lindelof_continuous_surjection : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y],
    LindelofSpace X → ∀ f : X → Y,
      Continuous f → Function.Surjective f → LindelofSpace Y

def firstCountable_open_continuous_surjection : Prop :=
  ∀ {X : Type u} [tX : TopologicalSpace X] {Y : Type v} [tY : TopologicalSpace Y],
    FirstCountable tX → ∀ f : X → Y,
      Continuous f → IsOpenMap f → Function.Surjective f → FirstCountable tY

def secondCountable_open_continuous_surjection : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y],
    SecondCountableTopology X → ∀ f : X → Y,
      Continuous f → IsOpenMap f → Function.Surjective f → SecondCountableTopology Y

end Specs.D10Topology.Ch08.CountabilityPermanence
