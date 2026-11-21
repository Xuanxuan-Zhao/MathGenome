import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm
import Mathlib.Topology.Order.LiminfLimsup

/-!
Independent statement of `fa2:p1:c07:pointwise-limit`, paper.tex:1449–1456.
The limit is a given function into the original normed space F. Only E is
assumed complete. A continuous linear map with this underlying function
expresses both linearity and boundedness, using the shared operator interface.

The real `Filter.liminf` has its ordinary finite meaning here: the conclusion
also provides a finite upper bound on all the nonnegative operator norms.
The zero vector spaces are included, over either real or complex scalars.
-/

namespace ExpandedFA.P1.C07PointwiseLimit.Spec

open Filter
open scoped Topology

universe u v w

/-- An existing pointwise limit on a Banach domain is bounded linear, the
approximating operator norms are uniformly bounded, and the limit satisfies
the sharp lower-limit norm estimate. -/
def PointwiseLimit : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E]
    (A : ℕ → E →L[𝕜] F) (T : E → F),
    (∀ x, Tendsto (fun n => A n x) atTop (𝓝 (T x))) →
      ∃ S : E →L[𝕜] F,
        (S : E → F) = T ∧
        (∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖A n‖ ≤ M) ∧
        0 ≤ liminf (fun n => ‖A n‖) atTop ∧
        ‖S‖ ≤ liminf (fun n => ‖A n‖) atTop

end ExpandedFA.P1.C07PointwiseLimit.Spec
