import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.TikhonovMinimizer
import Mathlib.Analysis.Real.Sqrt

/-!
Independent statements for the exact and noisy convergence clauses of
paper.tex, fa2:p5:tikhonov (23017–23040). The regularizer is the same
normal-equation operator as in the minimizer interface. Parameters approach
zero through positive reals. The kernel complement selects the minimum-norm
solution. No compactness or closed-range hypothesis is imposed.
-/

noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.PartV.TikhonovConvergence.Spec
universe u v w

local notation "R" => TikhonovMinimizer.Spec.regularizer

/-- Recovery of every solvable datum's minimum-norm preimage. -/
def ExactConvergence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G],
  ∀ (A : H →L[𝕜] G) (x : H), x ∈ A.ker.orthogonal →
    Tendsto (fun α : ℝ => R A α (A x)) (𝓝[>] (0 : ℝ)) (𝓝 x)

/-- The exact/noise decomposition, for arbitrary exact and perturbed data. -/
def ErrorDecomposition : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G],
  ∀ (A : H →L[𝕜] G) (α : ℝ) (f g : G) (x : H),
    R A α g - x = (R A α f - x) + R A α (g - f)

/-- The sharp noise amplification bound, including noise level zero. -/
def NoiseBound : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G],
  ∀ (A : H →L[𝕜] G) (α : ℝ), 0 < α →
    ∀ (δ : ℝ) (f g : G), ‖g - f‖ ≤ δ →
      ‖R A α (g - f)‖ ≤ δ / (2 * Real.sqrt α)

/-- The full deterministic error estimate. -/
def TotalErrorBound : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G],
  ∀ (A : H →L[𝕜] G) (α : ℝ), 0 < α →
    ∀ (δ : ℝ) (f g : G) (x : H), ‖g - f‖ ≤ δ →
      ‖R A α g - x‖ ≤ ‖R A α f - x‖ + δ / (2 * Real.sqrt α)

/-- Every admissible parameter choice and every data family obeying the
noise bound recovers the minimum-norm solution. No continuity of either
family is required. -/
def NoisyConvergence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G],
  ∀ (A : H →L[𝕜] G) (x : H), x ∈ A.ker.orthogonal →
    ∀ (α : ℝ → ℝ) (g : ℝ → G),
      (∀ δ > 0, 0 < α δ) →
      Tendsto α (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) →
      Tendsto (fun δ => δ / Real.sqrt (α δ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) →
      (∀ δ > 0, ‖g δ - A x‖ ≤ δ) →
      Tendsto (fun δ => R A (α δ) (g δ)) (𝓝[>] (0 : ℝ)) (𝓝 x)

end ExpandedFA.PartV.TikhonovConvergence.Spec
