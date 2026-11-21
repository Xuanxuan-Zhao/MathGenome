import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Ultrafilters

/-!
Independent statements for paper.tex, Theorem `d10:12:compact-complete-tb`
(lines 1688–1695). Compactness is the Chapter 5 open-cover property for the
topology induced by the uniform space. Completeness quantifies over proper
filters satisfying the small-square condition. Total boundedness uses finite
covers by sections U[x], with centers in X and the empty cover permitted.
Neither nonemptiness nor separatedness is assumed.
-/

open Set Filter
universe u

namespace Specs.D10Topology.Ch12.CompactCompleteTotalBounded

open UniformConventions
open Specs.D10Topology.Ch05.Compactness

/-- The full equivalence for every uniform space, including nonseparated ones. -/
def compact_iff_complete_totallyBounded : Prop :=
  ∀ (X : Type u) [UniformSpace X],
    CoverCompact X ↔ Complete X ∧ TotallyBoundedSpace X

/-- All three properties hold on the empty space, where there is no proper
ultrafilter. This uses the degenerate empty uniformity convention. -/
def empty_uniform_space_properties : Prop :=
  ∀ (X : Type u) [UniformSpace X] [IsEmpty X],
    CoverCompact X ∧ Complete X ∧ TotallyBoundedSpace X ∧
      ∀ F : Filter X, ¬ Specs.D10Topology.Ch05.Ultrafilters.IsUltrafilter F

end Specs.D10Topology.Ch12.CompactCompleteTotalBounded
