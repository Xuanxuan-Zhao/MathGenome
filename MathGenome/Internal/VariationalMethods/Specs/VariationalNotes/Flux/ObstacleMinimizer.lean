import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-! The variational existence stage of paper.tex, thm:hilbert-obstacle.
The scalar space is the one-coordinate Euclidean Sobolev space. No boundary
regularity or integrability of the obstacle is imposed. Measurability uses
the restricted measure, with no condition outside the domain. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
namespace VariationalNotes.Flux
open Sobolev

/-- Scalar values of a zero-boundary Sobolev class, as an actual L² class. -/
def scalarValue {d : ℕ} (Ω : Opens (Domain d)) :
    H1Zero Ω 1 →L[ℝ] P102.U4.DomainLp ℝ Ω Exponent.two.ennreal :=
  (coordinateLp Ω Exponent.two (0 : Fin 1)).comp
    ((value Ω 1 Exponent.two).comp (zeroSubmodule Ω 1 Exponent.two).subtypeL)

def obstacleSet {d : ℕ} (Ω : Opens (Domain d)) (ψ : Domain d → ℝ) :
    Set (H1Zero Ω 1) := {u | ∀ᵐ x ∂domainMeasure Ω, ψ x ≤ scalarValue Ω u x}

/-- The weak Dirichlet pairing, with Frobenius matrix convention. -/
def dirichletPairing {d : ℕ} (Ω : Opens (Domain d)) (u v : H1Zero Ω 1) : ℝ :=
  ∫ x, frobenius (gradient Ω 1 Exponent.two u.val x)
    (gradient Ω 1 Exponent.two v.val x) ∂domainMeasure Ω

def dirichletEnergy {d : ℕ} (Ω : Opens (Domain d))
    (ℓ : H1Zero Ω 1 →L[ℝ] ℝ) (u : H1Zero Ω 1) : ℝ :=
  (∫ x, ‖gradient Ω 1 Exponent.two u.val x‖ ^ 2 ∂domainMeasure Ω) / 2 - ℓ u

namespace ObstacleExpected

def ClosedConvex : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)) (ψ : Domain d → ℝ), AEMeasurable ψ (domainMeasure Ω) →
    IsClosed (obstacleSet Ω ψ) ∧ Convex ℝ (obstacleSet Ω ψ)

def UniqueMinimizer : Prop :=
  ∀ {n : ℕ} (Ω : Opens (Domain (n+1))), Bornology.IsBounded (Ω : Set (Domain (n+1))) →
    ∀ (ℓ : H1Zero Ω 1 →L[ℝ] ℝ) (ψ : Domain (n+1) → ℝ), AEMeasurable ψ (domainMeasure Ω) →
      (obstacleSet Ω ψ).Nonempty →
      ∃! u : H1Zero Ω 1, u ∈ obstacleSet Ω ψ ∧
        ∀ v ∈ obstacleSet Ω ψ, dirichletEnergy Ω ℓ u ≤ dirichletEnergy Ω ℓ v

def MinimizationIff : Prop :=
  ∀ {n : ℕ} (Ω : Opens (Domain (n+1))), Bornology.IsBounded (Ω : Set (Domain (n+1))) →
    ∀ (ℓ : H1Zero Ω 1 →L[ℝ] ℝ) (ψ : Domain (n+1) → ℝ), AEMeasurable ψ (domainMeasure Ω) →
      ∀ u : H1Zero Ω 1, u ∈ obstacleSet Ω ψ →
        ((∀ v ∈ obstacleSet Ω ψ, dirichletEnergy Ω ℓ u ≤ dirichletEnergy Ω ℓ v) ↔
          ∀ v ∈ obstacleSet Ω ψ, ℓ (v-u) ≤ dirichletPairing Ω u (v-u))

end ObstacleExpected
end VariationalNotes.Flux
