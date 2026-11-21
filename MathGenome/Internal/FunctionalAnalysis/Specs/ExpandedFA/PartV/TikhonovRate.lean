import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.TikhonovMinimizer
import Mathlib.Analysis.Asymptotics.Defs

/-!
Independent statements for paper.tex, fa2:p5:tikhonov-rate (23043–23060).
The datum is exactly A x, and the target lies perpendicular to ker A.
The source space is the actual range of A* A, without a closed-range,
compactness, dimension, injectivity, or separability hypothesis.
-/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace ExpandedFA.PartV.TikhonovRate.Spec
universe u v w

/-- The quantitative source-condition estimate, for every source representative. -/
def SourceBound : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (x : H), x ∈ A.ker.orthogonal →
    ∀ w : H, x = A.adjoint (A w) → ∀ α : ℝ, 0 < α →
      ‖TikhonovMinimizer.Spec.regularizer A α (A x) - x‖ ≤ α * ‖w‖

/-- Linear exact-data bias rate characterizes membership in the actual normal range. -/
def RangeCriterion : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (x : H), x ∈ A.ker.orthogonal →
      (x ∈ (A.adjoint.comp A).range ↔
        (fun α : ℝ => TikhonovMinimizer.Spec.regularizer A α (A x) - x)
          =O[𝓝[>] (0 : ℝ)] (fun α : ℝ => α))

end ExpandedFA.PartV.TikhonovRate.Spec
