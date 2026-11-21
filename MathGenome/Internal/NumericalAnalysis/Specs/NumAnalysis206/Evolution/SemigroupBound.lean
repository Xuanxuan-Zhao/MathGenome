import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.Definitions

/-!
Independent statement of the compact-horizon bound in paper.tex, immediately
before W18. The shared semigroup interface assumes only strong continuity.
-/

namespace Specs.NumAnalysis206.Evolution

open _root_.NumAnalysis206.Evolution

universe u v

/-- A strongly continuous semigroup on a real or complex Banach space has a
finite, nonnegative operator norm bound on each fixed positive horizon. -/
def semigroupCompactBound : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (T : StronglyContinuousSemigroup 𝕜 X) (T₀ : ℝ), 0 < T₀ →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, t ∈ Set.Icc 0 T₀ → ‖T t‖ ≤ K

end Specs.NumAnalysis206.Evolution
