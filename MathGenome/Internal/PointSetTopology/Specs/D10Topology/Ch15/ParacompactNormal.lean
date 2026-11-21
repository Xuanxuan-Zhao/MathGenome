import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.LocallyFiniteConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-!
Independent statements for paper.tex, d10:15:normal.
Paracompactness has no separation assumption. Normality and regularity
use the manuscript's conventions without T1; T4 is normality together
with T1. Closed subsets carry the canonical subspace topology, including
the empty subset, and their hereditary assertion assumes no Hausdorffness.
-/

universe u

namespace Specs.D10Topology.Ch15.ParacompactNormal

open Specs.D10Topology.Ch15.LocallyFiniteConventions
open Specs.D10Topology.Ch07.SeparationConventions

def paracompact_hausdorff_normal : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    Paracompact X → t2Value X → normalValue X

def paracompact_hausdorff_t4 : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    Paracompact X → t2Value X → t4Value X

def paracompact_hausdorff_regular : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    Paracompact X → t2Value X → regularValue X

def closed_subspace_paracompact : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], Paracompact X →
    ∀ Y : Set X, IsClosed Y → Paracompact Y

end Specs.D10Topology.Ch15.ParacompactNormal
