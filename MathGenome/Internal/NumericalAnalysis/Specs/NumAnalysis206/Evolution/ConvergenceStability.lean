import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.Definitions

/-! Independent statement of paper.tex, W18, on a fixed positive horizon. -/
namespace Specs.NumAnalysis206.Evolution

open _root_.NumAnalysis206.Evolution

universe u v

/-- Mesh-uniform strong convergence for every vector gives one common positive
step cutoff and one finite operator norm bound, including the zeroth power. -/
def convergenceImpliesStability : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (C : ℝ → X →L[𝕜] X) (T : StronglyContinuousSemigroup 𝕜 X)
    (T₀ : ℝ), 0 < T₀ → StronglyConvergent C T T₀ → SmallStepStable C T₀

end Specs.NumAnalysis206.Evolution
