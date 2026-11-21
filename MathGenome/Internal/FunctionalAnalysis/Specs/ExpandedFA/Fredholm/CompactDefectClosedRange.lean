import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Independent propositions for paper.tex:10322–10377, finite-kernel,
distance estimate, closed-range and power stages of Riesz--Schauder.
The ambient normed space need not be complete. Compact closure is in E.
The final statement allows algebraic linear maps: compactness implies continuity. -/
namespace ExpandedFA.Fredholm.CompactDefectClosedRangeSpec
universe u v

def KernelClosedFiniteDimensional : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    IsClosed (LinearMap.ker (LinearMap.id - K.toLinearMap) : Set E) ∧
    FiniteDimensional 𝕂 (LinearMap.ker (LinearMap.id - K.toLinearMap))

def DistanceEstimate : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    ∃ c : ℝ, 0 < c ∧ ∀ x : E,
      c * Metric.infDist x (LinearMap.ker (LinearMap.id - K.toLinearMap) : Set E) ≤
        ‖(ContinuousLinearMap.id 𝕂 E - K) x‖

def ClosedRange : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    IsClosed (LinearMap.range (ContinuousLinearMap.id 𝕂 E - K).toLinearMap : Set E)

def PowersClosedRangeFiniteKernel : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    ∀ m : ℕ, 1 ≤ m →
      IsClosed (LinearMap.ker ((ContinuousLinearMap.id 𝕂 E - K) ^ m).toLinearMap : Set E) ∧
      FiniteDimensional 𝕂 (LinearMap.ker ((ContinuousLinearMap.id 𝕂 E - K) ^ m).toLinearMap) ∧
      IsClosed (LinearMap.range ((ContinuousLinearMap.id 𝕂 E - K) ^ m).toLinearMap : Set E)

/-- Full obligation with no separate boundedness hypothesis on K. -/
def LinearCompactDefect : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →ₗ[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K →
    let A := LinearMap.id - K
    FiniteDimensional 𝕂 A.ker ∧
    (∃ c : ℝ, 0 < c ∧ ∀ x : E, c * Metric.infDist x (A.ker : Set E) ≤ ‖A x‖) ∧
    IsClosed (A.range : Set E) ∧
    ∀ n : ℕ, 1 ≤ n →
      FiniteDimensional 𝕂 (A ^ n).ker ∧ IsClosed ((A ^ n).range : Set E)

end ExpandedFA.Fredholm.CompactDefectClosedRangeSpec
