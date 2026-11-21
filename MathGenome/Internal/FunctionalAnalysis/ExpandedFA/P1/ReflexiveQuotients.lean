import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ReflexiveQuotients
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02QuotientComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Restriction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.ReflexiveSubspaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.ReflexiveDualEquivalence

/-!
Quotient stability, `fa2:p1:c14:stability`.
The continuous dual of E/M is isometric to the closed annihilator M⊥ in E′.
Dual stability and closed-subspace stability make M⊥ reflexive. Transport
along that isometry and dual equivalence for the Banach quotient finish
the proof, without any claim about the image of the closed unit ball.
-/

namespace ExpandedFA.P1.ReflexiveQuotients

universe u v

theorem reflexive_quotient_dual_isometry : Spec.QuotientDualIsometry.{u, v} :=
  C05Restriction.restriction_closed_quotient_dual_isometry

theorem reflexive_closed_quotient : Spec.QuotientReflexive.{u, v} := by
  intro 𝕜 E _ _ _ _ hE M hM
  letI : IsClosed (M : Set E) := hM
  letI : CompleteSpace (E ⧸ M) :=
    (C01Banach.isBanachSpace_iff_completeSpace (E ⧸ M)).mp
      (C02QuotientComplete.quotient_complete 𝕜 E M hM
        ((C01Banach.isBanachSpace_iff_completeSpace E).mpr inferInstance))
  letI : CompleteSpace (C04Dual.ContinuousDual 𝕜 E) :=
    C04DualComplete.dual_completeSpace 𝕜 E
  let N := C04Annihilators.annihilator 𝕜 E (M : Set E)
  have hN : IsClosed (N : Set (C04Dual.ContinuousDual 𝕜 E)) :=
    C04DualMaps.annihilator_isClosed 𝕜 E (M : Set E)
  have hdual : C04CanonicalMap.IsReflexive 𝕜 (C04Dual.ContinuousDual 𝕜 E) :=
    ReflexiveDualEquivalence.reflexive_dual_of_reflexive 𝕜 E hE
  have hNreflexive : C04CanonicalMap.IsReflexive 𝕜 N :=
    ReflexiveSubspaces.reflexive_closed_subspace 𝕜
      (C04Dual.ContinuousDual 𝕜 E) hdual N hN
  obtain ⟨e, _⟩ := reflexive_quotient_dual_isometry 𝕜 E M hM
  have hquotientDual : C04CanonicalMap.IsReflexive 𝕜 ((E ⧸ M) →L[𝕜] 𝕜) :=
    (C14IsomorphismInvariance.reflexivity_iff_of_equiv 𝕜
      ((E ⧸ M) →L[𝕜] 𝕜) N e.toContinuousLinearEquiv).mpr hNreflexive
  exact (ReflexiveDualEquivalence.reflexive_iff_dual_reflexive 𝕜 (E ⧸ M)).mpr
    hquotientDual

end ExpandedFA.P1.ReflexiveQuotients
