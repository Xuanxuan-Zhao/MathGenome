import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.DirichletDuality
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Corollary `cor:p-dirichlet-flux`, paper.tex 4459–4473.
All energies are on the original scalar zero-boundary Sobolev space; integration
against `domainMeasure Ω` means Lebesgue integration over Ω. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
namespace VariationalNotes.Flux.PowerEnergySpecs
open Sobolev WeakDivergenceSpec

/-- The original Euclidean power integrand. -/
def energy {d : ℕ} (p : ℝ) (z : Vector d) : ℝ := ‖z‖ ^ p / p

def primalObjective {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ) (u : W1pZero Ω 1 p) : ℝ :=
  (∫ x, energy p.real (Primal.gradientMap Ω p u x) ∂domainMeasure Ω) - ℓ u

def dualObjective {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (hp : 1 < p.real) (σ : Flux Ω p hp) : ℝ :=
  -(∫ x, energy (p.real / (p.real - 1)) (σ x) ∂domainMeasure Ω)

/-- The supremum formula is also required at w = 0. -/
def PowerConjugate : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∀ w : Vector d,
    IntegralConjugacySpecs.pointwiseConjugate (fun _ : Unit => energy p) () w =
      (energy (p / (p - 1)) w : EReal)

def StrictConvexPower : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → StrictConvexOn ℝ univ (energy (d := d) p)

/-- Finite attained minimum and maximum, the original negative-divergence
constraint, and uniqueness of the primal minimizer for every continuous load.
No smoothness or nonemptiness assumption on the bounded open domain is made. -/
def PowerFlux : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent) (hp : 1 < p.real) (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ),
    (∀ u, Integrable (fun x => energy p.real (Primal.gradientMap Ω p u x))
      (domainMeasure Ω)) ∧
    (∀ σ : Flux Ω p hp, Integrable
      (fun x => energy (p.real / (p.real - 1)) (σ x)) (domainMeasure Ω)) ∧
    (∀ σ : Flux Ω p hp,
      AllVariations Ω p hp σ ℓ ↔ DistributionConstraint Ω p hp σ ℓ) ∧
    ∃ (m : ℝ) (u : W1pZero Ω 1 p) (σ : Flux Ω p hp),
      primalObjective Ω p ℓ u = m ∧
      (∀ v, m ≤ primalObjective Ω p ℓ v) ∧
      AllVariations Ω p hp σ ℓ ∧ dualObjective Ω p hp σ = m ∧
      (∀ τ : Flux Ω p hp, AllVariations Ω p hp τ ℓ → dualObjective Ω p hp τ ≤ m) ∧
      (∀ v, (∀ w, primalObjective Ω p ℓ v ≤ primalObjective Ω p ℓ w) → v = u) ∧
      IsGLB (range (primalObjective Ω p ℓ)) m ∧
      IsLUB (dualObjective Ω p hp '' {τ | AllVariations Ω p hp τ ℓ}) m

end VariationalNotes.Flux.PowerEnergySpecs
