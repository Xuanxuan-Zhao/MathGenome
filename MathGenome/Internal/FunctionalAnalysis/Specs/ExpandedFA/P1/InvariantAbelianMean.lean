import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Independent statement of the abelian-group clause of
`paper.tex:5384–5412`. The discrete topology is used solely to represent
**all** bounded real functions; no topology is assumed on the group.
Set functions have domain `Set G`, the full power set. -/

universe u

namespace ExpandedFA.P1.AbelianMean

/-- All bounded real functions, with the uniform norm. -/
abbrev BoundedRealFunction (G : Type u) :=
  @BoundedContinuousFunction G ℝ ⊥ inferInstance

section
variable {G : Type u}

/-- The constant bounded function. -/
def constant (G : Type u) (c : ℝ) : BoundedRealFunction G :=
  @BoundedContinuousFunction.const G ℝ ⊥ inferInstance c

/-- Precomposition by a left translation. -/
noncomputable def translate [Group G] (a : G) :
    BoundedRealFunction G →ₗ[ℝ] BoundedRealFunction G := by
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  exact (BoundedContinuousFunction.compContinuousCLM (𝕜 := ℝ)
    (β := ℝ) ⟨fun x => a * x, continuous_of_discreteTopology⟩).toLinearMap

/-- The bounded indicator of an arbitrary subset. -/
noncomputable def indicator (A : Set G) : BoundedRealFunction G := by
  classical
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  exact BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => if x ∈ A then (1 : ℝ) else 0) 1
    (by intro x; split_ifs <;> simp)

/-- A positive, normalized, norm-one real continuous linear invariant mean. -/
def IsInvariantMean [Group G]
    (L : BoundedRealFunction G →L[ℝ] ℝ) : Prop :=
  ‖L‖ = 1 ∧
  (∀ c : ℝ, L (constant G c) = c) ∧
  (∀ f : BoundedRealFunction G, (∀ x, 0 ≤ f x) → 0 ≤ L f) ∧
  (∀ a : G, ∀ f : BoundedRealFunction G, L (translate a f) = L f)

/-- A positive finitely additive invariant probability on the full power set. -/
def IsInvariantProbability [Group G] (μ : Set G → ℝ) : Prop :=
  (∀ A, 0 ≤ μ A) ∧ μ ∅ = 0 ∧ μ Set.univ = 1 ∧
  (∀ A B, Disjoint A B → μ (A ∪ B) = μ A + μ B) ∧
  (∀ a : G, ∀ A : Set G, μ ((fun x => a * x) '' A) = μ A)

end
end ExpandedFA.P1.AbelianMean

namespace Specs.ExpandedFA.P1.InvariantAbelianMean
open ExpandedFA.P1.AbelianMean

/-- Both the invariant mean and the finitely additive probability it induces. -/
def invariantAbelianMeanType : Prop :=
  ∀ (G : Type u) [CommGroup G],
    ∃ (L : BoundedRealFunction G →L[ℝ] ℝ) (μ : Set G → ℝ),
      IsInvariantMean L ∧ IsInvariantProbability μ ∧
      ∀ A : Set G, μ A = L (indicator A)

end Specs.ExpandedFA.P1.InvariantAbelianMean
