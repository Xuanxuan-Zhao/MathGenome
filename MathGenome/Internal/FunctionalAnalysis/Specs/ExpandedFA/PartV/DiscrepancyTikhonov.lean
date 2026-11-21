import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.TikhonovMinimizer
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
The final assertion of `paper.tex`, fa2:p5:quasi-solution, and the residual
properties explicitly assigned with it. Both Hilbert spaces and both scalar
fields retain their original norms. No closed-range, compactness, separability
or nonzero-space assumption is made. The lower discrepancy endpoint is strict.
The distance limit uses the whole datum, including its adjoint-kernel component.
-/
noncomputable section
open Filter Set
open scoped Topology InnerProductSpace
namespace ExpandedFA.PartV.DiscrepancyTikhonov.Spec
universe u v w
variable {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]
local notation "R" => TikhonovMinimizer.Spec.regularizer

def ResidualContinuity (A : H →L[𝕜] G) (f : G) : Prop :=
  ContinuousOn (fun α : ℝ => ‖A (R A α f) - f‖) (Ioi 0)

def ResidualMonotonicity (A : H →L[𝕜] G) (f : G) : Prop :=
  MonotoneOn (fun α : ℝ => ‖A (R A α f) - f‖) (Ioi 0)

def ResidualLimitZero (A : H →L[𝕜] G) (f : G) : Prop :=
  Tendsto (fun α : ℝ => ‖A (R A α f) - f‖) (𝓝[>] (0 : ℝ))
    (𝓝 (Metric.infDist f (closure (A.range : Set G))))

def ResidualLimitInfinity (A : H →L[𝕜] G) (f : G) : Prop :=
  Tendsto (fun α : ℝ => ‖A (R A α f) - f‖) atTop (𝓝 ‖f‖)

/-- The residual's component in ker A* is constant for all parameters. -/
def KernelComponent (A : H →L[𝕜] G) (f : G) : Prop :=
  ∀ (α : ℝ), 0 < α → ∀ y ∈ A.adjoint.ker,
    ⟪y, A (R A α f) - f⟫_𝕜 = -⟪y, f⟫_𝕜

/-- Every regularized solution with the prescribed residual is precisely the
unique minimum-norm feasible point. This also states the converse identification. -/
def MinimumNormAtResidual (A : H →L[𝕜] G) (f : G) : Prop :=
  ∀ (α : ℝ), 0 < α → ∀ x : H,
    (‖A x - f‖ ≤ ‖A (R A α f) - f‖ ∧
      ∀ z : H, ‖A z - f‖ ≤ ‖A (R A α f) - f‖ → ‖x‖ ≤ ‖z‖) ↔
      x = R A α f

def DiscrepancySolution (A : H →L[𝕜] G) (f : G) : Prop :=
  ∀ δ : ℝ, Metric.infDist f (closure (A.range : Set G)) < δ → δ < ‖f‖ →
    ∃ α : ℝ, 0 < α ∧ ‖A (R A α f) - f‖ = δ ∧
      ∀ x : H, (‖A x - f‖ ≤ δ ∧
        ∀ z : H, ‖A z - f‖ ≤ δ → ‖x‖ ≤ ‖z‖) ↔ x = R A α f

end ExpandedFA.PartV.DiscrepancyTikhonov.Spec

namespace ExpandedFA.PartV.DiscrepancyTikhonov.Spec
universe u v w

/- Full quantified theorem types for independent declaration comparison. -/

def ResidualContinuityStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (f : G), ResidualContinuity A f

def ResidualMonotonicityStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (f : G), ResidualMonotonicity A f

def ResidualLimitZeroStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (f : G), ResidualLimitZero A f

def ResidualLimitInfinityStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (f : G), ResidualLimitInfinity A f

def KernelComponentStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (f : G), KernelComponent A f

def MinimumNormAtResidualStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (f : G), MinimumNormAtResidual A f

def DiscrepancySolutionStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (f : G), DiscrepancySolution A f

end ExpandedFA.PartV.DiscrepancyTikhonov.Spec
