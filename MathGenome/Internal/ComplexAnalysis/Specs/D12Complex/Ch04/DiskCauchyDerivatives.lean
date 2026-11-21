import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DiskCauchyFormula
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Independent statements for the all-derivatives and estimate portion of
paper.tex:875–922. `iteratedDeriv` is the actual iterated complex derivative;
its existence is asserted by `HasDerivAt`, not inferred from its total value.
The contour is precisely the counterclockwise path of the value-formula Spec.
No continuity of any derivative is a hypothesis. -/

noncomputable section
open Set Metric

namespace Specs.D12Complex.Ch04.DiskCauchyDerivatives
open _root_.D12Complex

/-- All derivatives on an arbitrary open set exist and are holomorphic. -/
def holomorphicOn_iteratedDeriv_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f → ∀ n : ℕ,
    HolomorphicOn U (iteratedDeriv n f) ∧
    ∀ z ∈ U, HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f z) z

/-- In particular every iterated derivative is continuous. -/
def continuousOn_iteratedDeriv_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f → ∀ n : ℕ,
    ContinuousOn (iteratedDeriv n f) U

/-- Formula at every interior point, on the original circle, including n = 0. -/
def disk_cauchy_derivatives_type : Prop :=
  ∀ (a z : ℂ) (r : ℝ) (U : Set ℂ) (f : ℂ → ℂ),
    0 < r → HolomorphicOn U f → closedBall a r ⊆ U → ‖z - a‖ < r →
    ∀ n : ℕ, iteratedDeriv n f z =
      (n.factorial : ℂ) / (2 * Real.pi * Complex.I) *
        (Specs.D12Complex.Ch04.DiskCauchyFormula.circlePath_value a r).integral
          (fun w => f w / (w - z) ^ (n + 1))

/-- The estimate holds for every boundary upper bound, in every order. -/
def disk_cauchy_estimate_type : Prop :=
  ∀ (a : ℂ) (r : ℝ) (U : Set ℂ) (f : ℂ → ℂ) (M : ℝ),
    0 < r → HolomorphicOn U f → closedBall a r ⊆ U →
    (∀ w ∈ sphere a r, ‖f w‖ ≤ M) → ∀ n : ℕ,
      ‖iteratedDeriv n f a‖ ≤ (n.factorial : ℝ) * M / r ^ n

/-- The boundary maximum is attained, and gives the stated sharp constants,
including n = 0. This avoids imposing a separate boundedness premise. -/
def disk_cauchy_estimate_max_type : Prop :=
  ∀ (a : ℂ) (r : ℝ) (U : Set ℂ) (f : ℂ → ℂ),
    0 < r → HolomorphicOn U f → closedBall a r ⊆ U →
    ∃ b ∈ sphere a r, (∀ w ∈ sphere a r, ‖f w‖ ≤ ‖f b‖) ∧
      ∀ n : ℕ, ‖iteratedDeriv n f a‖ ≤ (n.factorial : ℝ) * ‖f b‖ / r ^ n

end Specs.D12Complex.Ch04.DiskCauchyDerivatives
