import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.WeakVariants.UnboundedAdjointClosures

/-! Statements for `fa2:p2:weakstar-adjoint-closures`, paper.tex 8939–8979.
The four adjoint statements use the exact upstream adjoint and weak-star topology.
Closedness in the maximality assertion means closedness of the graph, as in the
source proof and the assigned Problem 16.A clarification. The domain is dense;
it is not asserted to be closed. No density or closedness is assumed beforehand.
The full-domain map is algebraic linear, with no assumed continuity. -/
namespace ExpandedFA.Monotone.ElementaryMaximality.Spec
universe u v w
open ExpandedFA.Unbounded

abbrev WeakStarRangeClosure : Prop :=
  ExpandedFA.WeakVariants.UnboundedAdjointClosures.Spec.WeakStarRangeClosure.{u,v,w}
abbrev WeakStarDomainClosure : Prop :=
  ExpandedFA.WeakVariants.UnboundedAdjointClosures.Spec.WeakStarDomainClosure.{u,v,w}
abbrev NormRangeClosure : Prop :=
  ExpandedFA.WeakVariants.UnboundedAdjointClosures.Spec.NormRangeClosure.{u,v,w}
abbrev NormDomainClosure : Prop :=
  ExpandedFA.WeakVariants.UnboundedAdjointClosures.Spec.NormDomainClosure.{u,v,w}

def MaximalClosed : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : Operator ℝ X (X →L[ℝ] ℝ)),
    Monotone.Spec.LinearMaximalMonotoneValue X B → IsClosed (B.graph : Set (X × (X →L[ℝ] ℝ)))

def MaximalDense : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : Operator ℝ X (X →L[ℝ] ℝ)),
    Monotone.Spec.LinearMaximalMonotoneValue X B → Dense (B.domain : Set X)

def EverywhereMaximal : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →ₗ[ℝ] (X →L[ℝ] ℝ)),
    Monotone.Spec.MonotoneMapValue X B →
      Monotone.Spec.MaximalMonotoneValue X (Monotone.Spec.MapGraphValue X B)

def EverywhereBounded : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : X →ₗ[ℝ] (X →L[ℝ] ℝ)),
    Monotone.Spec.MonotoneMapValue X B →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ‖B x‖ ≤ C * ‖x‖

end ExpandedFA.Monotone.ElementaryMaximality.Spec
