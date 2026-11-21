import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach

/-!
Independent statements for Proposition `fa2:p1:c04:dual-complete`,
paper.tex lines 759–764.

The dual is the space of continuous scalar-linear maps with its original
operator norm. `RCLike` covers both real and complex scalars, whose norms
are absolute value and modulus respectively. The domain is any normed
space: no completeness or nontriviality assumption is made on it.
-/

namespace ExpandedFA.P1.C04DualComplete.Spec

universe u v

/-- Completeness of the continuous dual in its operator-norm metric. -/
def DualCompleteSpace : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    CompleteSpace (E →L[𝕜] 𝕜)

/-- Every norm-Cauchy sequence in the dual converges there in norm,
using the manuscript's sequential definition of a Banach space. -/
def DualBanach : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C01Banach.Spec.IsBanachSpaceValue (E →L[𝕜] 𝕜)

/-- Evaluation satisfies the stated absolute-value estimate for every
functional and vector, including zero. -/
def EvaluationBound : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : E →L[𝕜] 𝕜) (x : E),
    ‖f x‖ ≤ ‖f‖ * ‖x‖

end ExpandedFA.P1.C04DualComplete.Spec
