import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.Monodromy
import Mathlib.LinearAlgebra.Matrix.ZPow

/-! The translation identity of paper.tex, d13:08:translation.
The principal matrix is the shared canonical evolution `U(·, 0)` on all
real time, and monodromy is its value at T. Integer matrix powers use
Mathlib's nonsingular inverse for negative exponents. Invertibility is
a proved upstream conclusion, not an additional hypothesis here. -/

noncomputable section

namespace Specs.D13Unified.Ch08.Translation
open Specs.D13Unified.Ch08.Monodromy

/-- One-period translation, with the original real-time, scalar-field,
continuity, and positive-period hypotheses. -/
def OnePeriod : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    ∀ t : ℝ, principalMatrixValue A (t + T) =
      principalMatrixValue A t * monodromyValue A T

/-- All integer translates, including zero and negative integers; r is
any real number, without a restriction to a fundamental interval. -/
def IntegerTranslation : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    ∀ (k : ℤ) (r : ℝ), principalMatrixValue A ((k : ℝ) * T + r) =
      principalMatrixValue A r * monodromyValue A T ^ k

end Specs.D13Unified.Ch08.Translation
