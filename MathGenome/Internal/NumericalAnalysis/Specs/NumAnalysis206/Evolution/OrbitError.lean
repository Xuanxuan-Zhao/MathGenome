import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.Definitions
import Mathlib.Algebra.BigOperators.Intervals

/-! Independent statements for the quantitative part of W19, paper.tex:656–678.
The maxima and the semigroup are the canonical W16 objects. -/
namespace Specs.NumAnalysis206.Evolution

open _root_.NumAnalysis206.Evolution

universe u v

/-- The noncommutative telescoping identity, including the empty sum at n = 0.
It holds at all nonnegative mesh times, with no horizon restriction needed. -/
def orbitTelescoping : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (C : ℝ → X →L[𝕜] X) (T : StronglyContinuousSemigroup 𝕜 X)
    (x : X) (h : ℝ), 0 < h → ∀ n : ℕ,
    (C h ^ n) x - T ((n : ℝ) * h) x =
      ∑ j ∈ Finset.range n,
        (C h ^ (n - 1 - j)) ((C h - T h) (T ((j : ℝ) * h) x))

/-- The full finite-horizon quantitative estimate, for any supplied small-step
stability constants. No consistency or commutation assumption is imposed. -/
def stabilityOrbitErrorBound : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (C : ℝ → X →L[𝕜] X) (T : StronglyContinuousSemigroup 𝕜 X)
    (T₀ h₀ M : ℝ), 0 < T₀ → 0 < h₀ →
    (∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ n : ℕ,
      (n : ℝ) * h ≤ T₀ → ‖C h ^ n‖ ≤ M) →
    ∀ (x : X) (h : ℝ), 0 < h → h ≤ h₀ →
      meshError C T T₀ h x ≤ M * T₀ * orbitDefect C T T₀ h x

/-- If a positive step exceeds the horizon, only the zero mesh time remains. -/
def meshErrorBeyondHorizon : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (C : ℝ → X →L[𝕜] X) (T : StronglyContinuousSemigroup 𝕜 X)
    (T₀ h : ℝ) (x : X), 0 < h → T₀ < h →
      meshError C T T₀ h x = 0 ∧ orbitDefect C T T₀ h x = 0

end Specs.NumAnalysis206.Evolution
