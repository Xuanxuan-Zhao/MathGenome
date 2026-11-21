import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.OperatorDomains

/-! Independent statement of the graph-domain clause of
`fa2:p2:positive-graph-estimate`, paper.tex:8854–8898.
Boundedness below of the nonempty real range expresses that the infimum is
strictly greater than minus infinity. The domain is the exact subspace carried
by the partial linear map; the estimate uses the sum graph norm. -/
namespace ExpandedFA.Monotone.PositiveGraphSpec

open ExpandedFA.Unbounded
universe u

def QuadraticEstimate : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (A : Operator ℝ X (X →L[ℝ] ℝ)),
    A.IsClosed → (∀ y : A.domain, 0 ≤ A y (y : X)) →
    ((∀ x : A.domain, BddBelow (Set.range (fun y : A.domain =>
        A y (y : X) - A y (x : X)))) ↔
      ∃ k : ℝ, 0 ≤ k ∧ ∀ x y : A.domain,
        |A y (x : X)| ^ 2 ≤ k * (‖(x : X)‖ + ‖A x‖) ^ 2 * A y (y : X))

end ExpandedFA.Monotone.PositiveGraphSpec
