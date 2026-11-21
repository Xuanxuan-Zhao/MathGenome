import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Convex.Basic

universe u v w

namespace Specs.NumAnalysis206.Newton

/-- The segment remainder estimate, with the canonical real structure on a real or
complex Banach space. The total function is only required to be differentiable on `U`. -/
def SegmentRemainderStatement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (X : Type v) (Y : Type w) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y],
  letI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  ∀ (F : X → Y) (U D : Set X) (L : ℝ),
    IsOpen U → DifferentiableOn 𝕜 F U → D ⊆ U → Convex ℝ D → 0 ≤ L →
    (∀ x ∈ D, ∀ y ∈ D, ‖fderiv 𝕜 F x - fderiv 𝕜 F y‖ ≤ L * ‖x - y‖) →
    ∀ x ∈ D, ∀ y ∈ D,
      ‖F y - F x - fderiv 𝕜 F x (y - x)‖ ≤ (L / 2) * ‖y - x‖ ^ 2

end Specs.NumAnalysis206.Newton
