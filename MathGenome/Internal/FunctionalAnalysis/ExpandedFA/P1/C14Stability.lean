import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14Stability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.ReflexiveSubspaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.ReflexiveDualEquivalence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.ReflexiveQuotients

/-! Assembly of the three clauses of `fa2:p1:c14:stability`. -/

namespace ExpandedFA.P1.C14Stability

universe u v

/-- Subspace, quotient and continuous linear dual stability of reflexivity. -/
theorem reflexivity_stability : Spec.Stability.{u, v} := by
  intro 𝕜 E _ _ _ _ M hM
  let : IsClosed (M : Set E) := hM
  refine ⟨?_, ReflexiveDualEquivalence.reflexive_iff_dual_reflexive 𝕜 E⟩
  intro hE
  exact ⟨ReflexiveSubspaces.reflexive_closed_subspace 𝕜 E hE M hM,
    ReflexiveQuotients.reflexive_closed_quotient 𝕜 E hE M hM⟩

end ExpandedFA.P1.C14Stability
