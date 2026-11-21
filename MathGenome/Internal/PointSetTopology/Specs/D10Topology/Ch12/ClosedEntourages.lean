import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.EntourageCalculus
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformTopology

/-! The three conclusions of `paper.tex`, d10:12:closed-entourages.
The only structure on X is its uniform structure. Thus `closure` and `IsClosed`
on X × X use the product of its induced topologies, with no separate topology
parameter. The upstream `uniformTopology_eq_canonical` identifies the paper's
entourage-section topology with this canonical topology. No separation or
nonemptiness assumption is imposed.
-/

open Set Filter
open scoped Uniformity Topology
universe u

namespace Specs.D10Topology.Ch12.ClosedEntourages

open UniformConventions EntourageCalculus

def closure_symmetric_entourage_subset_cube : Prop :=
  ∀ {X : Type u} [UniformSpace X] (V : Set (X × X)), V ∈ 𝓤 X →
    relationInverse V = V → closure V ⊆ relationPower V 3

def closed_symmetric_entourage : Prop :=
  ∀ {X : Type u} [UniformSpace X] (U : Set (X × X)), U ∈ 𝓤 X →
    ∃ C ∈ 𝓤 X, IsClosed C ∧ relationInverse C = C ∧ C ⊆ U

def closed_symmetric_entourage_cube : Prop :=
  ∀ {X : Type u} [UniformSpace X] (U : Set (X × X)), U ∈ 𝓤 X →
    ∃ C ∈ 𝓤 X, IsClosed C ∧ relationInverse C = C ∧
      C ⊆ U ∧ relationPower C 3 ⊆ U

end Specs.D10Topology.Ch12.ClosedEntourages
