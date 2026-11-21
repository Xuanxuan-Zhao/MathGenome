import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness

/-!
Independent statements for the last assertion of `paper.tex`,
`d10:08:permanence` (lines 1045 and 1052).
The product uses the canonical binary product topology. Compactness is
the upstream finite-open-subcover property; Lindelöfness is the canonical
class identified with the countable-open-subcover property in the upstream
countability conventions. Neither nonemptiness nor separation is assumed.
-/

open Set
universe u v w

namespace Specs.D10Topology.Ch08.LindelofCompactProduct

open Specs.D10Topology.Ch05.Compactness

/-- The open-cover formulation, allowing an index type in any universe. -/
def lindelof_compact_product_countable_subcover : Prop :=
  ∀ {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K],
    LindelofSpace X → CoverCompact K →
      ∀ {ι : Type w} (U : ι → Set (X × K)),
        (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
          ∃ J : Set ι, J.Countable ∧ (⋃ i ∈ J, U i) = univ

/-- A Lindelöf space times a compact space is Lindelöf, also for empty factors. -/
def lindelof_compact_product : Prop :=
  ∀ {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K],
    LindelofSpace X → CoverCompact K → LindelofSpace (X × K)

end Specs.D10Topology.Ch08.LindelofCompactProduct
