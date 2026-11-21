import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ReflexiveDualEquivalence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.ReflexiveSubspaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14IsomorphismInvariance
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
Dual stability in `fa2:p1:c14:stability`.
For the forward implication, compose a triple-dual functional with J_E.
For the converse, E″ is reflexive, and the canonical isometric image of
the Banach space E is a closed subspace of E″. Closed-subspace stability
and invariance under continuous linear equivalence finish the argument.
-/

namespace ExpandedFA.P1.ReflexiveDualEquivalence

universe u v

theorem reflexive_dual_of_reflexive : Spec.ReflexiveDualOfReflexive.{u, v} := by
  intro 𝕜 E _ _ _ hE
  change C04CanonicalMap.IsReflexive 𝕜 E at hE
  change C04CanonicalMap.IsReflexive 𝕜 (C04Dual.ContinuousDual 𝕜 E)
  intro Φ
  refine ⟨Φ.comp (C04CanonicalMap.canonicalEvaluation 𝕜 E), ?_⟩
  ext ξ
  obtain ⟨x, rfl⟩ := hE ξ
  rfl

theorem reflexive_iff_dual_reflexive : Spec.ReflexiveDualEquivalence.{u, v} := by
  intro 𝕜 E _ _ _ _
  change C04CanonicalMap.IsReflexive 𝕜 E ↔
    C04CanonicalMap.IsReflexive 𝕜 (C04Dual.ContinuousDual 𝕜 E)
  constructor
  · exact reflexive_dual_of_reflexive 𝕜 E
  · intro hdual
    have hbidual : C04CanonicalMap.IsReflexive 𝕜 (C04Dual.Bidual 𝕜 E) :=
      reflexive_dual_of_reflexive 𝕜 (C04Dual.ContinuousDual 𝕜 E) hdual
    letI : CompleteSpace (C04Dual.Bidual 𝕜 E) :=
      C04DualComplete.dual_completeSpace 𝕜 (C04Dual.ContinuousDual 𝕜 E)
    let J : E →ₗᵢ[𝕜] C04Dual.Bidual 𝕜 E :=
      { (C04CanonicalMap.canonicalEvaluation 𝕜 E).toLinearMap with
        norm_map' := C05BidualIsometry.canonicalEvaluation_norm 𝕜 E }
    have hclosed : IsClosed (LinearMap.range J.toLinearMap : Set (C04Dual.Bidual 𝕜 E)) :=
      (C05BidualIsometry.canonicalEvaluation_closed_range_iff_banach 𝕜 E).mpr
        ((C01Banach.isBanachSpace_iff_completeSpace E).mpr inferInstance)
    have hrange : C04CanonicalMap.IsReflexive 𝕜 (LinearMap.range J.toLinearMap) :=
      ReflexiveSubspaces.reflexive_closed_subspace 𝕜 (C04Dual.Bidual 𝕜 E) hbidual
        (LinearMap.range J.toLinearMap) hclosed
    exact (C14IsomorphismInvariance.reflexivity_iff_of_equiv 𝕜 E
      (LinearMap.range J.toLinearMap) J.equivRange.toContinuousLinearEquiv).mpr hrange

end ExpandedFA.P1.ReflexiveDualEquivalence
