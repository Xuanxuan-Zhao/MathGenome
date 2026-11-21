import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.Picard
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The instability and explicit example in `fa2:p5:picard`, paper.tex
21868–21884. Coordinates `n : ℕ` denote manuscript coordinates `j = n+1`.
The range always carries the ambient norm, and the estimate is tested only
on the orthogonal complement of the full kernel. -/
noncomputable section
universe u v w
namespace ExpandedFA.PartV.PicardInstability.Spec
open Filter
open scoped Topology

abbrev SquareSpace (𝕜 : Type u) [RCLike 𝕜] := lp (fun _ : ℕ => 𝕜) 2

def NoInverseEstimate {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G] (K : H →L[𝕜] G) : Prop :=
  ¬ ∃ C : ℝ, ∀ x : H, x ∈ K.ker.orthogonal → ‖x‖ ≤ C * ‖K x‖

def InfiniteRankInstability : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (K : H →L[𝕜] G),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    ¬ FiniteDimensional 𝕜 K.range → NoInverseEstimate K

/-- Nonexistence for the reciprocal datum and unstable unique solvability for
vanishing data, all for the same genuinely compact injective diagonal. -/
def DiagonalExample : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ (K : SquareSpace 𝕜 →L[𝕜] SquareSpace 𝕜) (f : SquareSpace 𝕜),
      (∀ x n, K x n = x n / ((n+1 : ℕ) : 𝕜)) ∧
      (∀ n, f n = 1 / ((n+1 : ℕ) : 𝕜)) ∧
      Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap ∧
      Function.Injective K ∧ f ∉ K.range ∧
      (∀ n, K (lp.single 2 n 1) = lp.single 2 n (1 / ((n+1 : ℕ) : 𝕜))) ∧
      Tendsto (fun n => K (lp.single 2 n 1)) atTop (𝓝 0) ∧
      (∀ n, ‖(lp.single 2 n 1 : SquareSpace 𝕜)‖ = 1 ∧
        ∀ x, K x = K (lp.single 2 n 1) ↔ x = lp.single 2 n 1) ∧
      NoInverseEstimate K

end ExpandedFA.PartV.PicardInstability.Spec
