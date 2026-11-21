import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-!
The dual-equivalence clause of `fa2:p1:c14:stability`, paper.tex:2767–2794.
Both predicates use the respective space's canonical evaluation map, and
the dual is the continuous scalar-linear dual with its operator norm.
The equivalence retains the Banach hypothesis on E and includes zero spaces.
-/

namespace ExpandedFA.P1.ReflexiveDualEquivalence.Spec

universe u v

/-- The forward implication needs no completeness assumption on E. -/
def ReflexiveDualOfReflexive : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
      C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (E →L[𝕜] 𝕜)

/-- A real or complex Banach space is canonically reflexive if and only if
its continuous scalar-linear dual is canonically reflexive. -/
def ReflexiveDualEquivalence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
      C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (E →L[𝕜] 𝕜)

end ExpandedFA.P1.ReflexiveDualEquivalence.Spec
