import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-!
Independent specifications for `paper.tex:6342–6361`,
`fa2:p1:positive-extension`.

The cone is presented as a set containing zero, closed under addition and
nonnegative real scaling. Its induced relation is `x ≤ y` iff `y - x ∈ C`.
No antisymmetry, closedness, topology, or completeness is assumed in the
algebraic assertion. The compact-function assertion permits empty `K`.
-/

universe u

namespace Specs.ExpandedFA.Supplements.PositiveExtension

/-- Positive extension for any majorizing subspace of a real vector space
ordered by a convex cone, including cones containing nonzero lines. -/
def positiveExtensionType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E]
    (C : Set E), (0 : E) ∈ C →
    (∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) →
    (∀ (t : ℝ), 0 ≤ t → ∀ x ∈ C, t • x ∈ C) →
    ∀ (Y : Submodule ℝ E), (∀ x : E, ∃ y : Y, (y : E) - x ∈ C) →
    ∀ (f : Y →ₗ[ℝ] ℝ), (∀ y : Y, (y : E) ∈ C → 0 ≤ f y) →
    ∃ F : E →ₗ[ℝ] ℝ,
      (∀ y : Y, F (y : E) = f y) ∧ (∀ x ∈ C, 0 ≤ F x)

/-- An algebraic positive functional on a subspace containing the constants
extends to a continuous positive functional with norm equal to its value on
the constant one. Neither continuity of the given functional nor nonemptiness
of the compact Hausdorff space is assumed. -/
def positiveExtensionContinuousMapType : Prop :=
  ∀ {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (Y : Submodule ℝ C(K, ℝ)) (h1 : (1 : C(K, ℝ)) ∈ Y)
    (f : Y →ₗ[ℝ] ℝ),
    (∀ y : Y, (∀ x : K, 0 ≤ (y : C(K, ℝ)) x) → 0 ≤ f y) →
    ∃ F : C(K, ℝ) →L[ℝ] ℝ,
      (∀ y : Y, F (y : C(K, ℝ)) = f y) ∧
      (∀ g : C(K, ℝ), (∀ x : K, 0 ≤ g x) → 0 ≤ F g) ∧
      ‖F‖ = f ⟨1, h1⟩

end Specs.ExpandedFA.Supplements.PositiveExtension
