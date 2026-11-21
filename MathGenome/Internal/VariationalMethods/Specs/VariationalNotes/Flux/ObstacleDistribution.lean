import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.ObstacleMinimizer
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.WeakDivergence

/-! Full distributional conclusion of paper.tex, Theorem `thm:hilbert-obstacle`.
Tests are ambient zero extensions of smooth functions compactly supported in Ω.
`IsTestClass` relates them to their unique zero-boundary Sobolev class; this
relation is the existing upstream interface, not an extra restriction on tests.
Continuous representatives need only be continuous on Ω and may differ on null
sets from the original obstacle and from the canonical L² representative. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
namespace VariationalNotes.Flux
open Sobolev

/-- The pairing of -Δu-ℓ with a smooth test represented by v. -/
def obstacleResidual {d : ℕ} (Ω : Opens (Domain d))
    (ℓ : H1Zero Ω 1 →L[ℝ] ℝ) (u v : H1Zero Ω 1) : ℝ :=
  dirichletPairing Ω u v - ℓ v

def obstacleNonnegative {d : ℕ} (Ω : Opens (Domain d))
    (ℓ : H1Zero Ω 1 →L[ℝ] ℝ) (u : H1Zero Ω 1) : Prop :=
  ∀ (φ : P102.U4.TestSpace ℝ Ω) (v : H1Zero Ω 1),
    WeakDivergenceSpec.IsTestClass Ω Exponent.two φ v →
    (∀ x, 0 ≤ φ x) → 0 ≤ obstacleResidual Ω ℓ u v

/-- The open noncontact region, including its domain restriction. -/
def obstacleInactiveSet {d : ℕ} (Ω : Opens (Domain d))
    (U Ψ : Domain d → ℝ) : Set (Domain d) :=
  {x | x ∈ Ω ∧ Ψ x < U x}

def obstacleInactiveEquation {d : ℕ} (Ω : Opens (Domain d))
    (ℓ : H1Zero Ω 1 →L[ℝ] ℝ) (ψ : Domain d → ℝ) (u : H1Zero Ω 1) : Prop :=
  ∀ (U Ψ : Domain d → ℝ), ContinuousOn U Ω → ContinuousOn Ψ Ω →
    (scalarValue Ω u : Domain d → ℝ) =ᵐ[domainMeasure Ω] U →
    ψ =ᵐ[domainMeasure Ω] Ψ →
    IsOpen (obstacleInactiveSet Ω U Ψ) ∧
      ∀ (φ : P102.U4.TestSpace ℝ Ω) (v : H1Zero Ω 1),
        WeakDivergenceSpec.IsTestClass Ω Exponent.two φ v →
        tsupport (φ : Domain d → ℝ) ⊆ obstacleInactiveSet Ω U Ψ →
        obstacleResidual Ω ℓ u v = 0

namespace ObstacleDistributionExpected

/-- The complete theorem: existence, uniqueness, VI characterization, positivity,
and the equation on the noncontact region whenever continuous representatives exist. -/
def FullTheorem : Prop :=
  ∀ {n : ℕ} (Ω : Opens (Domain (n+1))), Bornology.IsBounded (Ω : Set (Domain (n+1))) →
    ∀ (ℓ : H1Zero Ω 1 →L[ℝ] ℝ) (ψ : Domain (n+1) → ℝ),
      AEMeasurable ψ (domainMeasure Ω) → (obstacleSet Ω ψ).Nonempty →
      (∃! u : H1Zero Ω 1, u ∈ obstacleSet Ω ψ ∧
        ∀ v ∈ obstacleSet Ω ψ, dirichletEnergy Ω ℓ u ≤ dirichletEnergy Ω ℓ v) ∧
      (∀ u : H1Zero Ω 1, u ∈ obstacleSet Ω ψ →
        ((∀ v ∈ obstacleSet Ω ψ, dirichletEnergy Ω ℓ u ≤ dirichletEnergy Ω ℓ v) ↔
          ∀ v ∈ obstacleSet Ω ψ, ℓ (v-u) ≤ dirichletPairing Ω u (v-u))) ∧
      (∀ u : H1Zero Ω 1, u ∈ obstacleSet Ω ψ →
        (∀ v ∈ obstacleSet Ω ψ, dirichletEnergy Ω ℓ u ≤ dirichletEnergy Ω ℓ v) →
        obstacleNonnegative Ω ℓ u ∧ obstacleInactiveEquation Ω ℓ ψ u)

end ObstacleDistributionExpected
end VariationalNotes.Flux
