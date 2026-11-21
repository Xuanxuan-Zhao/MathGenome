import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach

/-!
Independent statements for Definition `fa2:p1:c14:reflexive`,
paper.tex:2700–2706. Reflexivity is the shared surjectivity predicate
for canonical evaluation into the continuous scalar-linear bidual.
Completeness is a conclusion in the original norm; the space may be zero.
-/

namespace ExpandedFA.P1.C14Reflexive.Spec

universe u v

/-- A reflexive normed space is Banach in the manuscript's sequential sense. -/
def ReflexiveBanach : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
      C01Banach.Spec.IsBanachSpaceValue E

/-- The same automatic completeness in the native norm uniformity. -/
def ReflexiveCompleteSpace : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E → CompleteSpace E

end ExpandedFA.P1.C14Reflexive.Spec
