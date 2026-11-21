import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Convex.Hull

/-!
Independent statement of `fa2:p1:c24:compact-hull`, paper.tex:5095–5099.

The space is Banach for its given norm. For either real or complex scalars,
convex combinations use the underlying real vector space obtained by
restriction of scalars. The norm, topology, and uniformity are unchanged.
There is no nonemptiness or nontriviality premise.
-/

namespace ExpandedFA.P1.C24CompactHullSpec

/-- The norm-closed real convex hull of a compact set in a Banach space
is compact in the same norm topology. -/
def CompactHull : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ Q : Set E, IsCompact Q → IsCompact (closure (convexHull ℝ Q))

end ExpandedFA.P1.C24CompactHullSpec
