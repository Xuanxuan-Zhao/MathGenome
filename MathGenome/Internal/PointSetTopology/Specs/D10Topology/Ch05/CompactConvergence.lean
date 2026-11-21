import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Ultranets
import Mathlib.Data.List.TFAE

/-! Independent specification of paper.tex d10:05:compact-convergence.
Compactness is the open-cover definition. FilterClusters and FilterConverges
use the canonical neighborhood definition; properness is explicit. The net
predicates and actual Moore–Smith subnet data are the shared Chapter 4 objects.

All net criteria quantify over nonempty directed preorders. The arbitrary
universe v allows indices as large as desired; max u v also accommodates
canonical filter nets (whose indices contain subsets of X). The individual
forward results allow any index universe v, including smaller universes.
There are no separation, nonemptiness-of-X, or uniqueness assumptions.
-/

open Set Filter
universe u v
namespace Specs.D10Topology.Ch05.CompactConvergence
open Ch04.ProperFilters Ch04.NetsAndSubnets

def compact_net_cluster : Prop :=
  ∀ {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] [t : TopologicalSpace X],
    Compactness.CoverCompact X → ∀ a : D → X, ∃ x : X, Clusters t a x

def compact_net_convergent_subnet : Prop :=
  ∀ {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] [t : TopologicalSpace X],
    Compactness.CoverCompact X → ∀ a : D → X, ∃ x : X, HasConvergentSubnet t a x

def compact_ultranet_converges : Prop :=
  ∀ {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] [t : TopologicalSpace X],
    Compactness.CoverCompact X → ∀ a : D → X, Ultranets.IsUltranet a →
      ∃ x : X, Converges t a x

def compact_iff_filter_cluster_points : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    Compactness.CoverCompact X ↔ (∀ F : Filter X, F.NeBot → ∃ x : X, FilterClusters F x)

def compact_iff_net_cluster_points : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    Compactness.CoverCompact X ↔ (∀ (D : Type (max u v)) [Preorder D] [Nonempty D] [IsDirectedOrder D]
      (a : D → X), ∃ x : X, Clusters t a x)

def compact_iff_convergent_subnets : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    Compactness.CoverCompact X ↔ (∀ (D : Type (max u v)) [Preorder D] [Nonempty D] [IsDirectedOrder D]
      (a : D → X), ∃ x : X, HasConvergentSubnet t a x)

def compact_iff_ultrafilter_convergence : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    Compactness.CoverCompact X ↔ (∀ F : Filter X, Ultrafilters.IsUltrafilter F →
      ∃ x : X, FilterConverges F x)

def compact_iff_ultranet_convergence : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    Compactness.CoverCompact X ↔ (∀ (D : Type (max u v)) [Preorder D] [Nonempty D] [IsDirectedOrder D]
      (a : D → X), Ultranets.IsUltranet a → ∃ x : X, Converges t a x)

def compactness_convergence_equivalences : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    List.TFAE [
      (Compactness.CoverCompact X),
      (∀ F : Filter X, F.NeBot → ∃ x : X, FilterClusters F x),
      (∀ (D : Type (max u v)) [Preorder D] [Nonempty D] [IsDirectedOrder D]
      (a : D → X), ∃ x : X, Clusters t a x),
      (∀ (D : Type (max u v)) [Preorder D] [Nonempty D] [IsDirectedOrder D]
      (a : D → X), ∃ x : X, HasConvergentSubnet t a x),
      (∀ F : Filter X, Ultrafilters.IsUltrafilter F →
      ∃ x : X, FilterConverges F x),
      (∀ (D : Type (max u v)) [Preorder D] [Nonempty D] [IsDirectedOrder D]
      (a : D → X), Ultranets.IsUltranet a → ∃ x : X, Converges t a x)]

end Specs.D10Topology.Ch05.CompactConvergence
