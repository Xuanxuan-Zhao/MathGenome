import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic

/-! Independent statement of the bounded-operator assertion in
`paper.tex`, Theorem `fa2:p3:product-formula`, lines 14939–14941.
Multiplication of continuous endomorphisms is composition. The real time
parameter acts through the canonical map into the real or complex scalar field.
The integer number of steps is positive; the constant is independent of both
that integer and the time in the prescribed compact interval. -/

namespace ExpandedFA.Semigroups.BoundedStrangErrorSpec

/-- Uniform second-order error for bounded Strang splitting on every real or
complex Banach space, including the zero space, the interval `{0}`, and empty
intervals when the finite real upper endpoint is negative. -/
def BoundedStrangError : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] (A B : X →L[𝕜] X) (T : ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 ≤ t → t ≤ T →
      ‖(NormedSpace.exp ((algebraMap ℝ 𝕜 (t / (2 * (n : ℝ)))) • A) *
          NormedSpace.exp ((algebraMap ℝ 𝕜 (t / (n : ℝ))) • B) *
          NormedSpace.exp ((algebraMap ℝ 𝕜 (t / (2 * (n : ℝ)))) • A)) ^ n -
        NormedSpace.exp ((algebraMap ℝ 𝕜 t) • (A + B))‖ ≤ C / (n : ℝ) ^ 2

end ExpandedFA.Semigroups.BoundedStrangErrorSpec
