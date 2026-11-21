import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02CompleteSubspace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Banach
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-! Complete and closed subspaces, Proposition `fa2:p1:c02:complete-subspace`. -/

namespace ExpandedFA.P1.C02CompleteSubspace

open ExpandedFA.P1.C01Banach

/-- A complete subspace is closed, including in an incomplete ambient space. -/
theorem complete_subspace_closed : Spec.CompleteSubspaceClosed := by
  intro 𝕜 E _ _ _ M hM
  have hcomplete : CompleteSpace M := (isBanachSpace_iff_completeSpace M).mp hM
  exact (completeSpace_coe_iff_isComplete.mp hcomplete).isClosed

/-- A subspace of a Banach space is complete precisely when it is closed. -/
theorem complete_subspace_iff_closed : Spec.CompleteSubspaceIffClosed := by
  intro 𝕜 E _ _ _ hE M
  constructor
  · exact complete_subspace_closed 𝕜 E M
  · intro hM
    let : CompleteSpace E := (isBanachSpace_iff_completeSpace E).mp hE
    exact (isBanachSpace_iff_completeSpace M).mpr hM.isComplete.completeSpace_coe

end ExpandedFA.P1.C02CompleteSubspace
