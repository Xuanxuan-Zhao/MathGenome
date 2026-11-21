import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientNorm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm

/-!
Independent statements for the factorization clause of
`fa2:p1:c02:quotient-map` (paper.tex, lines 370–396).

The algebraic quotient is by the original subspace, with no norm or
closedness hypothesis in the algebraic assertion. The bounded assertion
uses precisely the distance norm of `C02QuotientNorm`, for a closed subspace.
Neither vector space is assumed complete or nonzero.
-/

noncomputable section

namespace ExpandedFA.P1.QuotientFactorization.Spec

/-- A linear map vanishing on any subspace descends uniquely to its algebraic
quotient, with its value specified on every representative. -/
def AlgebraicFactorization : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    (M : Submodule 𝕜 E) (T : E →ₗ[𝕜] F),
    (∀ m ∈ M, T m = 0) →
    ∃! U : (E ⧸ M) →ₗ[𝕜] F, ∀ x : E, U (M.mkQ x) = T x

/-- On a closed distance-norm quotient the induced map is bounded and has
exactly the original operator norm. Uniqueness is among all bounded linear
factorizations, without imposing any norm condition on the competitor. -/
def BoundedFactorization : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)),
    letI := C02QuotientNorm.Spec.quotientNormedGroupValue 𝕜 E M hM
    ∀ (T : E →L[𝕜] F), (∀ m ∈ M, T m = 0) →
    ∃ U : (E ⧸ M) →L[𝕜] F,
      (∀ x : E, U (M.mkQ x) = T x) ∧
      ‖U‖ = ‖T‖ ∧
      ∀ V : (E ⧸ M) →L[𝕜] F,
        (∀ x : E, V (M.mkQ x) = T x) → V = U

end ExpandedFA.P1.QuotientFactorization.Spec
