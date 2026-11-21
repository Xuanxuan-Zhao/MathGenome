import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint

/-!
Independent statement for `paper.tex` 7852–7880,
`fa2:p2:bounded-form-representation`.

The two Hilbert spaces have independent universe levels. The shared bounded
form is conjugate linear in the first slot and scalar linear in the second;
its native iterated operator norm is the least nonnegative form bound by the
conventions interface. The adjoint is the shared Hilbert adjoint H₂ → H₁.
Neither space is required to be nonzero, and no coercivity or symmetry is assumed.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.TwoSpaceForms.Spec
universe u v w

/-- Existence, both representations, exact norm, and uniqueness among all
bounded scalar-linear operators satisfying the first representation. -/
def FormRepresentation : Prop :=
  ∀ (𝕜 : Type u) (H₁ : Type v) (H₂ : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace 𝕜 H₁] [InnerProductSpace 𝕜 H₂]
    [CompleteSpace H₁] [CompleteSpace H₂]
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H₁ H₂),
    ∃ S : H₁ →L[𝕜] H₂,
      (∀ (x : H₁) (y : H₂), a x y = ⟪S x, y⟫_𝕜) ∧
      (∀ (x : H₁) (y : H₂),
        a x y = ⟪x, Adjoint.Spec.AdjointValue 𝕜 H₁ H₂ S y⟫_𝕜) ∧
      ‖S‖ = ‖a‖ ∧
      ∀ T : H₁ →L[𝕜] H₂,
        (∀ (x : H₁) (y : H₂), a x y = ⟪T x, y⟫_𝕜) → T = S

end ExpandedFA.Hilbert.TwoSpaceForms.Spec
