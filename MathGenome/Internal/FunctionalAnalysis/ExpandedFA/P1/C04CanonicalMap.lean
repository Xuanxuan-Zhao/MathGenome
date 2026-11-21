import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Dual

/-! The canonical evaluation map and the definition of reflexivity in
Definition `fa2:p1:c04:canonical-map`. The codomain uses the shared bidual,
including its native linear operations, operator norm and topology. -/

namespace ExpandedFA.P1.C04CanonicalMap

universe u v

/-- The canonical map J_E : E → E″, defined by J_E(x)(f) = f(x). -/
noncomputable def canonicalEvaluation (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : E →L[𝕜] C04Dual.Bidual 𝕜 E :=
  ContinuousLinearMap.apply 𝕜 𝕜

@[simp]
theorem canonicalEvaluation_apply (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : E) (f : C04Dual.ContinuousDual 𝕜 E) :
    canonicalEvaluation 𝕜 E x f = f x :=
  rfl

/-- A normed space is reflexive when its canonical evaluation map is onto. -/
def IsReflexive (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  Function.Surjective (canonicalEvaluation 𝕜 E)

theorem isReflexive_iff_surjective (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    IsReflexive 𝕜 E ↔ Function.Surjective (canonicalEvaluation 𝕜 E) :=
  Iff.rfl

end ExpandedFA.P1.C04CanonicalMap
