import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Quotient

/-! Independent statements for paper.tex:8787–8834. Nonemptiness ensures that
`P-P` is a subspace. This also permits cones defined using strictly positive
scalars which need not contain zero. No salience assumption is imposed. -/

universe u

namespace Specs.ExpandedFA.Ordered.PositiveAutomaticContinuity

/-- The actual algebraic subspace `P - P`, with its inherited topology. -/
def differenceSubspace {X : Type u} [AddCommGroup X] [Module ℝ X]
    (P : ConvexCone ℝ X) (hne : (P : Set X).Nonempty) : Submodule ℝ X where
  carrier := {x | ∃ y ∈ P, ∃ z ∈ P, x = y - z}
  zero_mem' := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, hy, y, hy, by simp⟩
  add_mem' := by
    rintro _ _ ⟨y, hy, z, hz, rfl⟩ ⟨v, hv, w, hw, rfl⟩
    exact ⟨y + v, P.add_mem hy hv, z + w, P.add_mem hz hw,
      (add_sub_add_comm y v z w).symm⟩
  smul_mem' := by
    rintro r _ ⟨y, hy, z, hz, rfl⟩
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · refine ⟨(-r) • z, P.smul_mem (neg_pos.mpr hr) hz,
        (-r) • y, P.smul_mem (neg_pos.mpr hr) hy, ?_⟩
      simp [neg_smul, sub_eq_add_neg, add_comm]
    · obtain ⟨w, hw⟩ := hne
      exact ⟨w, hw, w, hw, by simp⟩
    · exact ⟨r • y, P.smul_mem hr hy, r • z, P.smul_mem hr hz, smul_sub ..⟩

/-- No completeness or closedness hypothesis is imposed in this direction. -/
def necessaryCondition : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : ConvexCone ℝ X) (hne : (P : Set X).Nonempty),
    (∀ f : X →ₗ[ℝ] ℝ, (∀ x ∈ P, 0 ≤ f x) → Continuous f) →
    IsClosed (differenceSubspace P hne : Set X) ∧
      FiniteDimensional ℝ (X ⧸ differenceSubspace P hne)

/-- Every positive algebraic functional is continuous under the stated
Banach, closed-cone, and closed finite-codimension assumptions. -/
def sufficientCondition : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (P : ConvexCone ℝ X) (hne : (P : Set X).Nonempty),
    IsClosed (P : Set X) → IsClosed (differenceSubspace P hne : Set X) →
    FiniteDimensional ℝ (X ⧸ differenceSubspace P hne) →
    ∀ f : X →ₗ[ℝ] ℝ, (∀ x ∈ P, 0 ≤ f x) → Continuous f

/-- The quantitative generating-cone conclusion, including the zero space. -/
def boundedDecompositions : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (P : ConvexCone ℝ X), IsClosed (P : Set X) →
    (∀ x : X, ∃ y ∈ P, ∃ z ∈ P, x = y - z) →
    ∃ C : ℝ, 0 < C ∧ ∀ x : X, ∃ y ∈ P, ∃ z ∈ P,
      x = y - z ∧ ‖y‖ ≤ C * ‖x‖ ∧ ‖z‖ ≤ C * ‖x‖

end Specs.ExpandedFA.Ordered.PositiveAutomaticContinuity
