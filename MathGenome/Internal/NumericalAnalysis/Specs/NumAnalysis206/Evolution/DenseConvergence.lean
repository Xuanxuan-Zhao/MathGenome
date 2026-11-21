import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.Definitions

/-! Independent statements for the complete W19 (paper.tex:656–683).
The dense class is an arbitrary subset, and all limits are from positive steps.
The quantitative estimate is retained alongside the convergence conclusion. -/

open Filter Topology

namespace Specs.NumAnalysis206.Evolution

open _root_.NumAnalysis206.Evolution

universe u v

/-- Extension from a fixed comparison vector on the same finite horizon.
`K` can be any nonnegative compact-horizon bound for the exact semigroup. -/
def meshErrorExtensionEstimate : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (C : ℝ → X →L[𝕜] X) (T : StronglyContinuousSemigroup 𝕜 X)
    (T₀ h₀ M K : ℝ), 0 < T₀ → 0 < h₀ → 0 ≤ M → 0 ≤ K →
    (∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ n : ℕ,
      (n : ℝ) * h ≤ T₀ → ‖C h ^ n‖ ≤ M) →
    (∀ t : ℝ, t ∈ Set.Icc 0 T₀ → ‖T t‖ ≤ K) →
    ∀ (x y : X) (h : ℝ), 0 < h → h ≤ h₀ →
      meshError C T T₀ h x ≤ meshError C T T₀ h y + (M + K) * ‖x - y‖

/-- W19 for specified stability constants: the quantitative error estimate and
convergence for every vector when orbit consistency holds on a dense subset. -/
def stabilityAndDenseOrbitConvergence : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (C : ℝ → X →L[𝕜] X) (T : StronglyContinuousSemigroup 𝕜 X)
    (T₀ h₀ M : ℝ), 0 < T₀ → 0 < h₀ →
    (∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ n : ℕ,
      (n : ℝ) * h ≤ T₀ → ‖C h ^ n‖ ≤ M) →
    (∀ (x : X) (h : ℝ), 0 < h → h ≤ h₀ →
      meshError C T T₀ h x ≤ M * T₀ * orbitDefect C T T₀ h x) ∧
    (∀ D : Set X, Dense D → (∀ y ∈ D, UniformOrbitConsistent C T T₀ y) →
      StronglyConvergent C T T₀)

/-- The W16 predicate suffices; neither a linear structure on the dense class
nor consistency outside that class is assumed. -/
def denseOrbitConvergence : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (C : ℝ → X →L[𝕜] X) (T : StronglyContinuousSemigroup 𝕜 X)
    (T₀ : ℝ), 0 < T₀ → SmallStepStable C T₀ →
    ∀ D : Set X, Dense D → (∀ y ∈ D, UniformOrbitConsistent C T T₀ y) →
      StronglyConvergent C T T₀

end Specs.NumAnalysis206.Evolution
