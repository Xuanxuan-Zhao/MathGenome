import MathGenome.Internal.LinearPDE.P201Specs.Heat.CubeDirichletKernel

/-! Independent statements for the one-cube step of `pde:heat-harnack`,
`paper.tex` 3022–3045. Cubes may have different centers and side lengths.
Closed containment encodes compact containment of these bounded open cubes.
The constant is selected before the ambient domain, time interval, or solution.
Classical caloricity means the shared C^{2,1} definition, with no boundary data.
-/
noncomputable section
open Set Metric MeasureTheory
namespace P201Specs.Heat.CubeHarnack
open Cube

/-- The comparison used in the source, stated for arbitrary positive initial
and final interior times. In particular `s ∈ [t-r²,t]` and `q=t+δ` are allowed.
There is no condition on the initial values at the faces of the cube. -/
def kernelComparisonStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ (Ω : Domain n) (T : ℝ), 0 < T → closedCube ℓ a ⊆ (Ω : Set (Space n)) →
  ∀ u : SpaceTime n → ℝ,
    IsClassicalCaloricOn u ((Ω : Set (Space n)) ×ˢ Ioo 0 T) →
    (∀ z ∈ (Ω : Set (Space n)) ×ˢ Ioo 0 T, 0 ≤ u z) →
  ∀ s q : ℝ, 0 < s → s < q → q < T →
  ∀ y ∈ closedCube ℓ a,
    kernelSolution ℓ a (fun z => u (z,s)) (q-s) y ≤ u (y,q)

/-- Full one-cube inequality. The spatial ball in the source is open; its
closure still lies in the larger cube `Q`, which suffices for the center
estimate. The hypotheses on `t₁,t₂` ensure all relevant times are interior. -/
def oneCubeHarnackStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
  ∀ (ℓ : ℝ), 0 < ℓ → ∀ a : Space n,
  ∀ (ℓ' : ℝ), 0 < ℓ' → ∀ a' : Space n,
  ∀ (ℓstar : ℝ), 0 < ℓstar → ∀ astar : Space n,
    closedCube ℓstar astar ⊆ cube ℓ' a' →
    closedCube ℓ' a' ⊆ cube ℓ a →
  ∀ r δ : ℝ, 0 < r → 0 < δ →
    (∀ x ∈ cube ℓstar astar, ball x r ⊆ cube ℓ' a') →
  ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Domain n) (T : ℝ), 0 < T → closedCube ℓ a ⊆ (Ω : Set (Space n)) →
    ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ < t₂ → t₂ < T → r^2 < t₁ →
    ∀ u : SpaceTime n → ℝ,
      IsClassicalCaloricOn u ((Ω : Set (Space n)) ×ˢ Ioo 0 T) →
      (∀ z ∈ (Ω : Set (Space n)) ×ˢ Ioo 0 T, 0 ≤ u z) →
    ∀ x ∈ cube ℓstar astar, ∀ y ∈ cube ℓstar astar,
    ∀ t : ℝ, t₁ ≤ t → t + δ ≤ t₂ →
      u (x,t) ≤ C * u (y,t+δ)

end P201Specs.Heat.CubeHarnack
