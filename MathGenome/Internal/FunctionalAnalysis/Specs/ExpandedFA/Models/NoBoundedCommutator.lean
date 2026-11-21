import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.RCLike.Basic

namespace Specs.ExpandedFA.Models

/-- The no bounded canonical commutator proposition, including the nonzero-space
qualification. `RCLike` covers both real and complex scalar fields. -/
def NoBoundedCommutator : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [Nontrivial E] (A B : E →L[𝕜] E),
    A * B - B * A ≠ 1

end Specs.ExpandedFA.Models
