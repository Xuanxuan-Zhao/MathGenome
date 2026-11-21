import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BoundedWeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BoundedWeakstarTopology
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BoundedWeakstarDual

/-! Assembly of the complete bounded weak-star topology theorem.
The two prerequisites use definitionally the same null-sequence seminorms and
topology. Completeness is confined to the continuous-dual identification. -/

namespace ExpandedFA.P1.BoundedWeakStar

/-- The bounded weak-star topology theorem for real and complex normed spaces,
including the continuous-dual characterization for Banach preduals. -/
theorem bounded_weak_star : Spec.CompleteStatement :=
  ⟨BoundedWeakstarTopology.finite_supremum,
    BoundedWeakstarTopology.topology_construction,
    BoundedWeakstarTopology.bounded_agreement,
    BoundedWeakstarTopology.finest_topology,
    BoundedWeakstarTopology.closed_criterion,
    BoundedWeakstarDual.continuous_dual_identification⟩

end ExpandedFA.P1.BoundedWeakStar
