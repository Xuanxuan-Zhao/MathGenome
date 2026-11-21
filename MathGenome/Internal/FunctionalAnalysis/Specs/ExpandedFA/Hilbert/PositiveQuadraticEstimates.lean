import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint

/-!
Independent statements for the positive-form estimates used in
`paper.tex` 7432–7435, in `fa2:p2:projection-lattice`.

The operator is bounded on the original real or complex Hilbert space.
Self-adjointness uses the shared Hilbert adjoint; positivity is explicitly
nonnegativity of its real quadratic values. No C*-algebra order, strict
positivity, injectivity, separability, or nonzero-space assumption is imposed.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.PositiveQuadraticEstimates.Spec
universe u v

/-- The diagonal scalars really are nonnegative real numbers. -/
def DiagonalNonnegativeReal : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : H →L[𝕜] H), Adjoint.Spec.AdjointValue 𝕜 H H D = D →
    (∀ x : H, 0 ≤ RCLike.re ⟪x, D x⟫_𝕜) →
    ∀ x : H, (RCLike.re ⟪x, D x⟫_𝕜 : 𝕜) = ⟪x, D x⟫_𝕜 ∧
      0 ≤ RCLike.re ⟪x, D x⟫_𝕜

/-- Cauchy–Schwarz for the possibly degenerate positive form ⟪y,Dx⟫. -/
def QuadraticCauchySchwarz : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : H →L[𝕜] H), Adjoint.Spec.AdjointValue 𝕜 H H D = D →
    (∀ x : H, 0 ≤ RCLike.re ⟪x, D x⟫_𝕜) →
    ∀ x y : H, ‖⟪y, D x⟫_𝕜‖ ^ 2 ≤
      RCLike.re ⟪y, D y⟫_𝕜 * RCLike.re ⟪x, D x⟫_𝕜

/-- The exact quantitative estimate with the original operator norm. -/
def NormQuadraticEstimate : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : H →L[𝕜] H), Adjoint.Spec.AdjointValue 𝕜 H H D = D →
    (∀ x : H, 0 ≤ RCLike.re ⟪x, D x⟫_𝕜) →
    ∀ x : H, ‖D x‖ ^ 2 ≤ ‖D‖ * RCLike.re ⟪x, D x⟫_𝕜

end ExpandedFA.Hilbert.PositiveQuadraticEstimates.Spec
