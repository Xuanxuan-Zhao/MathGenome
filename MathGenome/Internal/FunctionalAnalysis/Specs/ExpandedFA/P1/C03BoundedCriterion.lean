import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Operations
import Mathlib.Analysis.Normed.Operator.Basic

/-!
Independent statement of Theorem `fa2:p1:c03:bounded-criterion`, paper.tex
lines 586–593. The map is initially algebraically linear. All continuity and
boundedness use the given norm metrics. `RCLike` includes both real and complex
scalars; neither completeness nor nontriviality of the spaces is assumed.
-/

namespace ExpandedFA.P1.C03BoundedCriterion.Spec

/-- All five conditions are equivalent, expressed as four equivalences with
continuity. Boundedness is metric boundedness, including for the empty set.
In particular, continuity is not an assumption on the input linear map. -/
def BoundednessCriterion : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →ₗ[𝕜] F),
    (Continuous T ↔ ContinuousAt T (0 : E)) ∧
    (Continuous T ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖T x‖ ≤ C * ‖x‖) ∧
    (Continuous T ↔ Bornology.IsBounded (T '' Metric.closedBall (0 : E) 1)) ∧
    (Continuous T ↔ ∀ s : Set E, Bornology.IsBounded s →
      Bornology.IsBounded (T '' s))

end ExpandedFA.P1.C03BoundedCriterion.Spec
