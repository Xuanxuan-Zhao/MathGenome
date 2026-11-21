import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UniformConvexity
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Independent statements for the Hilbert clause of `fa2:p1:c14:uc-examples`,
paper.tex:2894–2903. The closed-unit-ball estimate holds for all real or
complex inner product spaces, hence in particular every Hilbert space.
Neither completeness nor nontriviality is needed; ε = 2 is included.
-/

namespace ExpandedFA.P1.HilbertUniformConvexity.Spec

universe u v

/-- The prescribed modulus is positive and gives the full midpoint estimate. -/
def ExplicitModulus : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (ε : ℝ), 0 < ε → ε ≤ 2 →
    0 < 1 - Real.sqrt (1 - ε ^ 2 / 4) ∧
      ∀ x y : H, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ε ≤ ‖x - y‖ →
        ‖(2 : 𝕜)⁻¹ • (x + y)‖ ≤ 1 - (1 - Real.sqrt (1 - ε ^ 2 / 4))

/-- Uniform convexity in the shared manuscript predicate. -/
def UniformConvexity : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H],
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 H

end ExpandedFA.P1.HilbertUniformConvexity.Spec
