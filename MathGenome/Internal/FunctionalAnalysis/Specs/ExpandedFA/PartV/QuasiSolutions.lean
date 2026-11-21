import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
Independent statements for the first three assertions of
`paper.tex`, `fa2:p5:quasi-solution` (23126–23140).
The last assertion, identifying a discrepancy solution with a Tikhonov
solution, belongs to the separate DiscrepancyTikhonov obligation.
Both Hilbert spaces have their original norms, and may be zero or nonseparable.
Closed balls have arbitrary centers and nonnegative radii.
-/

namespace ExpandedFA.PartV.QuasiSolutions.Spec
universe u v w

def ResidualMinimumOnBall : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
    (A : X →L[𝕜] Y) (f : Y) (c : X) (r : ℝ), 0 ≤ r →
    ∃ x ∈ Metric.closedBall c r,
      ∀ z ∈ Metric.closedBall c r, ‖A x - f‖ ≤ ‖A z - f‖

def UniqueResidualMinimumOnBall : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
    (A : X →L[𝕜] Y), Function.Injective A →
    ∀ (f : Y) (c : X) (r : ℝ), 0 ≤ r →
    ∃! x : X, x ∈ Metric.closedBall c r ∧
      ∀ z ∈ Metric.closedBall c r, ‖A x - f‖ ≤ ‖A z - f‖

def UniqueMinimumNormDiscrepancy : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
    (A : X →L[𝕜] Y) (f : Y) (δ : ℝ), 0 ≤ δ →
    (∃ x : X, ‖A x - f‖ ≤ δ) →
    ∃! x : X, ‖A x - f‖ ≤ δ ∧
      ∀ z : X, ‖A z - f‖ ≤ δ → ‖x‖ ≤ ‖z‖

end ExpandedFA.PartV.QuasiSolutions.Spec
