import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-! Independent interface for paper.tex, Theorem `d13:19:mean-ergodic`.
The endomorphism is a linear isometry, with no surjectivity assumption. -/
namespace Specs.D13Unified.Ch19.MeanErgodic

open Filter Topology
universe u v
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

/-- The fixed vectors of the isometry. -/
def fixedSpace (U : H →ₗᵢ[𝕜] H) : Submodule 𝕜 H :=
  (U.toContinuousLinearMap - ContinuousLinearMap.id 𝕜 H).ker

/-- Closure of the range of `I - U`. -/
def coboundarySpace (U : H →ₗᵢ[𝕜] H) : Submodule 𝕜 H :=
  (LinearMap.range (LinearMap.id - U.toLinearMap)).topologicalClosure

/-- Cesàro averages; the empty average at zero is zero. -/
def average (U : H →ₗᵢ[𝕜] H) (n : ℕ) : H →L[𝕜] H :=
  (n : 𝕜)⁻¹ • ∑ j ∈ Finset.range n, (U ^ j).toContinuousLinearMap

/-- Orthogonal projection onto the fixed space, using its closedness and
ambient Hilbert completeness. -/
noncomputable def fixedProjection [CompleteSpace H] (U : H →ₗᵢ[𝕜] H) : H →L[𝕜] H := by
  letI : CompleteSpace (fixedSpace U) :=
    (U.toContinuousLinearMap - ContinuousLinearMap.id 𝕜 H).isClosed_ker.isComplete.completeSpace_coe
  exact (fixedSpace U).starProjection

/-- Full Hilbert-space conclusion, including the decomposition and quantitative
coboundary estimate used for the closure argument. -/
def mean_ergodic_type : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (U : H →ₗᵢ[𝕜] H),
    IsClosed (fixedSpace U : Set H) ∧
    (coboundarySpace U)ᗮ = fixedSpace U ∧
    IsCompl (fixedSpace U) (coboundarySpace U) ∧
    (∀ n h, ‖average U n h‖ ≤ ‖h‖) ∧
    (∀ (n : ℕ) (g : H),
      average U n (g - U g) = (n : 𝕜)⁻¹ • (g - (U ^ n) g) ∧
      ‖average U n (g - U g)‖ ≤ 2 * ‖g‖ / (n : ℝ)) ∧
    ∀ h : H, Tendsto (fun n => average U n h) atTop (𝓝 (fixedProjection U h))

end Specs.D13Unified.Ch19.MeanErgodic
