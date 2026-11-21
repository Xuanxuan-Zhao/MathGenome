import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Topology.Bases

/-!
Independent statements of Lemma `fa2:p1:c14:dual-separability` (paper.tex
2800–2805). The duals below carry their operator norms and the associated
norm topologies. No weak-star topology is substituted for either norm
topology. Both scalar fields and the zero space are included.
-/

namespace ExpandedFA.P1.C14DualSeparability.Spec

universe u v

/-- Norm separability of the continuous linear dual forces separability
of the given normed space; completeness and reflexivity are not assumed. -/
def SpaceSeparableOfDualSeparable : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    TopologicalSpace.SeparableSpace (X →L[𝕜] 𝕜) →
      TopologicalSpace.SeparableSpace X

/-- A separable reflexive Banach space has norm-separable continuous
linear dual. Reflexivity is the shared canonical-surjectivity predicate. -/
def DualSeparableOfSeparableReflexive : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    TopologicalSpace.SeparableSpace X →
      C04CanonicalMap.Spec.IsReflexiveValue 𝕜 X →
        TopologicalSpace.SeparableSpace (X →L[𝕜] 𝕜)

end ExpandedFA.P1.C14DualSeparability.Spec
