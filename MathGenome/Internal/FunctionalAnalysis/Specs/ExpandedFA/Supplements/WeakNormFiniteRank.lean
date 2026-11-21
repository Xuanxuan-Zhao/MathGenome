import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Independent statement of paper.tex, lines 6047–6052.
The dual and the bounded operator use the original norm topologies. Only the
source topology in `Continuous` is replaced by the weak topology. No
completeness assumption is imposed on either normed space. -/
namespace ExpandedFA.Supplements.WeakNormFiniteRankSpec

universe u v w

/-- Global weak-to-norm continuity is equivalent to finite-dimensional range,
for real or complex normed spaces, including zero spaces. -/
def Statement : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    @Continuous E F
      (ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue
        𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      inferInstance T ↔ FiniteDimensional 𝕜 T.range

end ExpandedFA.Supplements.WeakNormFiniteRankSpec
