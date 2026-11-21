import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-!
Independent specification of Milman--Pettis, `fa2:p1:c14:milman-pettis`,
paper.tex:2861–2864, with the chapter's conventions at 2690–2704.
Completeness refers to the given norm. Uniform convexity is the manuscript's
closed-unit-ball predicate. Reflexivity means that scalar-linear evaluation
onto the continuous bidual is surjective. Both real and complex fields and
the zero space are included, without separability assumptions.
-/
namespace ExpandedFA.P1.C14MilmanPettis.Spec
universe u v

/-- Every uniformly convex Banach space is reflexive. -/
def MilmanPettis : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E →
      C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E

end ExpandedFA.P1.C14MilmanPettis.Spec
