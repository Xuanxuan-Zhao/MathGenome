import Mathlib.Analysis.InnerProductSpace.Basic

/-! Independent statement of the finite ball-intersection stage of
Kirszbraun–Valentine, paper.tex:13007–13026. Both spaces use the original
norms; the scalar fields can independently be real or complex. The finite
index set may be empty. No dimension restriction is imposed. -/
namespace ExpandedFA.Geometry.HilbertBallIntersection.Spec
universe u v w z t

def FiniteBallIntersection : Prop :=
  ∀ (𝕜₁ : Type u) (𝕜₂ : Type v) (H₁ : Type w) (H₂ : Type z)
    [RCLike 𝕜₁] [RCLike 𝕜₂]
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜₁ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜₂ H₂] [CompleteSpace H₂]
    (ι : Type t) [Fintype ι] (s : ι → H₁) (y : ι → H₂),
    (∀ i j, ‖y i - y j‖ ≤ ‖s i - s j‖) →
    ∀ x : H₁, (⋂ i, Metric.closedBall (y i) ‖s i - x‖).Nonempty

end ExpandedFA.Geometry.HilbertBallIntersection.Spec
