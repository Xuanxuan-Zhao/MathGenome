import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.PositiveGraphQuadratic
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Independent statements for `fa2:p2:positive-graph-estimate`.
The first clause retains the exact partial domain. For the full-domain clauses
we start with an algebraic linear map with closed graph, and require a bounded
realization agreeing everywhere. Thus continuity is a conclusion, not an extra
hypothesis. The transpose on the canonical image of X in X'' is `B.flip`:
`B.flip y x = B x y`. No symmetry, density or nonzero-space assumption is made. -/

namespace ExpandedFA.Monotone.PositiveFullDomainSpec

universe u

/-- The graph-domain part, using the upstream canonical domain representation. -/
def GraphEstimate : Prop := PositiveGraphSpec.QuadraticEstimate.{u}

/-- All full-domain assertions, including the bounded realization and the exact
transpose formula. The same arbitrary positive α occurs in both estimates. -/
def FullDomainEstimates : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (A : X →ₗ[ℝ] (X →L[ℝ] ℝ)),
    IsClosed (A.graph : Set (X × (X →L[ℝ] ℝ))) →
    (∀ y : X, 0 ≤ A y y) →
    ∃ B : X →L[ℝ] (X →L[ℝ] ℝ), B.toLinearMap = A ∧
      (∀ x y : X, B.flip y x = A x y) ∧
      ∀ α : ℝ, 0 < α →
        ((∀ y : X, ‖B y‖ ^ 2 ≤ α * B y y) ↔
          ∀ x y : X, -α * ‖x‖ ^ 2 / 4 ≤ B y y - B y x) ∧
        ((∀ y : X, ‖B y‖ ^ 2 ≤ α * B y y) ↔
          ∀ y : X, ‖B.flip y‖ ^ 2 ≤ α * B.flip y y)

end ExpandedFA.Monotone.PositiveFullDomainSpec
