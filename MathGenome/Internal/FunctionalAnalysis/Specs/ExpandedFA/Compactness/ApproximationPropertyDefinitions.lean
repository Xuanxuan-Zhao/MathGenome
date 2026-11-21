import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Order.Compact

/-!
Independent specifications for `fa2:p2:ap-definition`, paper.tex:9489–9494.

The approximants are bounded scalar-linear endomorphisms. Finite rank means
that their algebraic range is finite dimensional over the original field.
The error is the supremum of the norm errors over the compact set. In ℝ,
`sSup ∅ = 0`, so an empty compact set imposes no restriction at a positive
tolerance. The pointwise characterizations below also cover this case.

AP has no common operator-norm bound. BAP requires one nonnegative bound,
chosen before both the compact set and the positive tolerance. These
definitions make sense for normed spaces, hence in particular for the Banach
spaces of the source, over either ℝ or ℂ.
-/

namespace ExpandedFA.Compactness.ApproximationPropertyDefinitionsSpec

universe u v
noncomputable section

def HasApproximationPropertyType :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X], Prop

def HasApproximationPropertyValue : HasApproximationPropertyType :=
  fun 𝕜 X _ _ _ =>
    ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ F : X →L[𝕜] X,
        FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) ∧
        sSup ((fun x : X => ‖F x - x‖) '' K) < ε

def HasBoundedApproximationPropertyType :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X], Prop

def HasBoundedApproximationPropertyValue : HasBoundedApproximationPropertyType :=
  fun 𝕜 X _ _ _ =>
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
        ∃ F : X →L[𝕜] X,
          FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) ∧
          ‖F‖ ≤ M ∧ sSup ((fun x : X => ‖F x - x‖) '' K) < ε

/-- Compactness and continuity identify the strict uniform error with the
pointwise strict inequalities, including the empty compact set. -/
def ApproximationErrorLtIff : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
  ∀ (F : X →L[𝕜] X) (K : Set X), IsCompact K →
    ∀ ε : ℝ, 0 < ε →
      (sSup ((fun x : X => ‖F x - x‖) '' K) < ε ↔
        ∀ x ∈ K, ‖F x - x‖ < ε)

def ApproximationPropertyIffPointwise : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
  HasApproximationPropertyValue 𝕜 X ↔
    ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ F : X →L[𝕜] X,
        FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) ∧
        ∀ x ∈ K, ‖F x - x‖ < ε

def BoundedApproximationPropertyIffPointwise : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
  HasBoundedApproximationPropertyValue 𝕜 X ↔
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
        ∃ F : X →L[𝕜] X,
          FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) ∧
          ‖F‖ ≤ M ∧ ∀ x ∈ K, ‖F x - x‖ < ε

def BoundedApproximationPropertyImpliesApproximationProperty : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
  HasBoundedApproximationPropertyValue 𝕜 X →
    HasApproximationPropertyValue 𝕜 X

end
end ExpandedFA.Compactness.ApproximationPropertyDefinitionsSpec
