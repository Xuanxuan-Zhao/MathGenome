import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Independent statement of Corollary `fa2:p1:c07:weak-boundedness`,
paper.tex:1434–1447. Boundedness is metric boundedness for the given norm.
The tests are all continuous scalar-linear functionals, with a separate
bound permitted for each functional. The original space need not be
complete; the set may be empty and the space may be zero.
-/

namespace ExpandedFA.P1.C07WeakBoundedness.Spec

universe u v

/-- Norm boundedness is equivalent to boundedness under every continuous
linear functional, for real and complex normed spaces. -/
def WeakBoundedness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    Bornology.IsBounded A ↔
      ∀ f : E →L[𝕜] 𝕜, Bornology.IsBounded (f '' A)

end ExpandedFA.P1.C07WeakBoundedness.Spec
