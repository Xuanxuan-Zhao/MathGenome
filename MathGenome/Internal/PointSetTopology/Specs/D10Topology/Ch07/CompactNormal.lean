import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-!
Independent statements for paper.tex, d10:07:compact-normal.
Compactness is the open-cover property. Normality has no T1 condition;
T4 means normality together with T1. No nonemptiness hypothesis is imposed
on the space or on either closed set.
-/

open Set
universe u

namespace Specs.D10Topology.Ch07.CompactNormal

def compact_hausdorff_closed_separation : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X],
    Ch05.Compactness.CoverCompact X →
      ∀ A B : Set X, IsClosed A → IsClosed B → Disjoint A B →
        ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint U V

def compact_hausdorff_normal : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X],
    Ch05.Compactness.CoverCompact X → SeparationConventions.normalValue X

def compact_hausdorff_t4 : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X],
    Ch05.Compactness.CoverCompact X → SeparationConventions.t4Value X

end Specs.D10Topology.Ch07.CompactNormal
