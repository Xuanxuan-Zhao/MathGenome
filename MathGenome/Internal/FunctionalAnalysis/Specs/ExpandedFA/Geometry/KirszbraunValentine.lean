import Mathlib.Analysis.InnerProductSpace.Basic

/-! Independent statement of Kirszbraun–Valentine, paper.tex:12989–13042.
The two scalar fields may independently be real or complex. The norms and
metrics are the given ones. The domain is an arbitrary subset; in particular
it need not be nonempty, bounded, closed, separable, or countable. -/
namespace ExpandedFA.Geometry.KirszbraunValentine.Spec
universe u v w z

/-- Extension with the original nonnegative real Lipschitz bound. -/
def Extension : Prop :=
  ∀ (𝕜₁ : Type u) (𝕜₂ : Type v) (H₁ : Type w) (H₂ : Type z)
    [RCLike 𝕜₁] [RCLike 𝕜₂]
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜₁ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜₂ H₂] [CompleteSpace H₂]
    (S : Set H₁) (L : ℝ), 0 ≤ L →
    ∀ f : S → H₂,
      (∀ s t : S, ‖f s - f t‖ ≤ L * ‖(s : H₁) - (t : H₁)‖) →
      ∃ g : H₁ → H₂,
        (∀ x y : H₁, ‖g x - g y‖ ≤ L * ‖x - y‖) ∧
        (∀ s : S, g s = f s)

end ExpandedFA.Geometry.KirszbraunValentine.Spec
