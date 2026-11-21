import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.CompactNormal
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.CompactImagesAndSeparation
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions

/-!
Compact Hausdorff spaces are normal and T4 (paper.tex, d10:07:compact-normal).
Closed subsets are compact, so the previously proved separation theorem for
two disjoint compact subsets supplies their open neighborhoods. That theorem
includes empty compact subsets, and the present statements include empty spaces.
-/

open Set
universe u

namespace D10Topology.Ch07

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- Disjoint closed subsets of a compact Hausdorff space have disjoint
open neighborhoods, with no nonemptiness restrictions. -/
theorem compact_hausdorff_closed_separation (hX : Ch05.CoverCompact X)
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint U V :=
  Ch05.disjoint_compact_separation A B
    (Ch05.closed_subset_compact hX A hA) (Ch05.closed_subset_compact hX B hB) hAB

theorem compact_hausdorff_normal (hX : Ch05.CoverCompact X) : Normal X :=
  (normal_iff_disjoint_open X).mpr (compact_hausdorff_closed_separation hX)

theorem compact_hausdorff_t4 (hX : Ch05.CoverCompact X) : T4 X :=
  ⟨compact_hausdorff_normal hX, inferInstance⟩

end D10Topology.Ch07
