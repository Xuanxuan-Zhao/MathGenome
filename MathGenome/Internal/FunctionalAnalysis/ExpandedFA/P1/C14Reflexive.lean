import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14Reflexive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry

/-!
Automatic completeness in Definition `fa2:p1:c14:reflexive`.
The shared reflexivity predicate means surjectivity of canonical evaluation.
The accepted bidual-isometry theorem proves that this forces completeness:
the bidual is Banach and the isometric canonical map has closed, full range.
No completeness assumption is imposed on the original normed space.
-/

namespace ExpandedFA.P1.C14Reflexive

universe u v

/-- Surjectivity of canonical evaluation implies the sequential Banach property. -/
theorem reflexive_banach : Spec.ReflexiveBanach.{u, v} :=
  C05BidualIsometry.reflexive_banach

/-- A reflexive normed space is complete for its given norm. -/
theorem reflexive_completeSpace : Spec.ReflexiveCompleteSpace.{u, v} := by
  intro 𝕜 E _ _ _ h
  exact (C01Banach.isBanachSpace_iff_completeSpace E).mp (reflexive_banach 𝕜 E h)

end ExpandedFA.P1.C14Reflexive
