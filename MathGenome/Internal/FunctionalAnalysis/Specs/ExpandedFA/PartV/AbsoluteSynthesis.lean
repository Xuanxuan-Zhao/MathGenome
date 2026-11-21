import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Independent statement of `fa2:p5:absolute-synthesis`, paper.tex:23488–23497.
The scalar field is real or complex; the dual is scalar-linear. The coefficient
space has its native ℓ¹ norm. `HasSum` and summability of the term norms explicitly
assert an exact, absolutely norm-convergent synthesis. The zero space is allowed. -/
open scoped lp

namespace ExpandedFA.PartV.AbsoluteSynthesis.Spec

universe u v

def QuantitativeAbsoluteSynthesis : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (v : ℕ → X) (β : ℝ),
    (∀ n, ‖v n‖ ≤ 1) → 0 < β →
    (∀ ℓ : X →L[𝕜] 𝕜, β * ‖ℓ‖ ≤ ⨆ n : ℕ, ‖ℓ (v n)‖) →
    ∀ (x : X) (ε : ℝ), 0 < ε →
    ∃ a : ℓ¹(ℕ, 𝕜),
      HasSum (fun n => a n • v n) x ∧
      Summable (fun n => ‖a n • v n‖) ∧
      ‖a‖ < β⁻¹ * ‖x‖ + ε

end ExpandedFA.PartV.AbsoluteSynthesis.Spec
