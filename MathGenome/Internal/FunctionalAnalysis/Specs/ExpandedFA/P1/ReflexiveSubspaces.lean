import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair

/-!
Independent statements for the subspace clause of
`fa2:p1:c14:stability`, paper.tex:2767–2777.
The submodule has the inherited norm. Its dual consists of continuous
scalar-linear functionals for that norm, and reflexivity means surjectivity
of its own canonical evaluation map. The weak topology is intrinsic to
that dual, for both real and complex scalars, including the zero subspace.
-/

namespace ExpandedFA.P1.ReflexiveSubspaces.Spec

universe u v

/-- The ambient weak topology induces the intrinsic inherited-norm weak
topology on a scalar-linear subspace. Closedness is not needed here. -/
def SubspaceWeakTopology : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E),
    TopologicalSpace.induced (fun m : M => (m : E))
        (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
          (topDualPairing 𝕜 E)) =
      C12DualPairSpec.DualPairTopologyValue 𝕜 M (M →L[𝕜] 𝕜)
        (topDualPairing 𝕜 M)

/-- Every closed scalar-linear subspace of a reflexive real or complex
Banach space is canonically reflexive for its inherited norm. -/
def ClosedSubspaceReflexive : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ (M : Submodule 𝕜 E), IsClosed (M : Set E) →
      C04CanonicalMap.Spec.IsReflexiveValue 𝕜 M

end ExpandedFA.P1.ReflexiveSubspaces.Spec
