import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.GDelta.Basic

/-!
Independent statement of the first assertion of `fa2:p1:nonmeagre-range`,
paper.tex:6124–6154. The range is the actual set of values in the given
codomain topology. Only the domain is assumed complete. `RCLike` includes
both manuscript scalar fields, and no nontriviality is imposed on either
vector space. `CompleteSpace` refers to the displayed norm's uniformity.
The separate finite-codimension assertion is allocated to a different goal.
-/

namespace ExpandedFA.Supplements.NonmeagreImage.Spec

/-- A bounded linear image of a Banach space which is nonmeagre in the
ambient normed codomain is the whole codomain, the map is open, and the
codomain is complete in its original norm. -/
def ImageConclusion : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    ¬ IsMeagre (Set.range T) →
      Function.Surjective T ∧ IsOpenMap T ∧ CompleteSpace F

end ExpandedFA.Supplements.NonmeagreImage.Spec
