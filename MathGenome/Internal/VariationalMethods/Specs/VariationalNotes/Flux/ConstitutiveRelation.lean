import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.DirichletDuality
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Subgradients

/-! The general assertion of `prop:optimal-flux`, paper.tex 4478–4506.
The subgradient tests every vector in the original finite-dimensional fiber.
Flux feasibility retains exactly the upstream load constraint. -/
noncomputable section
open MeasureTheory TopologicalSpace Set

namespace VariationalNotes.Flux.ConstitutiveRelationSpecs
open Sobolev WeakDivergenceSpec IntegralConjugacySpecs

/-- The original real primal objective. -/
def primalValue {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (F : Ω → Vector d → ℝ) (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ)
    (u : W1pZero Ω 1 p) : ℝ :=
  (∫ x : Ω, F x (Primal.gradientMap Ω p u x.val) ∂(volume.comap Subtype.val)) - ℓ u

/-- The conjugate is finite a.e. under the theorem's hypotheses. -/
def dualValue {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
    (F : Ω → Vector d → ℝ) (σ : Flux Ω p hp) : ℝ :=
  -(∫ x : Ω, (pointwiseConjugate F x (σ x.val)).toReal ∂(volume.comap Subtype.val))

def gap {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
    (F : Ω → Vector d → ℝ) (u : W1pZero Ω 1 p) (σ : Flux Ω p hp) (x : Ω) : ℝ :=
  F x (Primal.gradientMap Ω p u x.val) + (pointwiseConjugate F x (σ x.val)).toReal -
    inner ℝ (σ x.val) (Primal.gradientMap Ω p u x.val)

/-- Vector slopes, under the Euclidean identification with the continuous dual. -/
def fiberSubdifferential {d : ℕ} (f : Vector d → ℝ) (z : Vector d) : Set (Vector d) :=
  {w | ∀ y : Vector d, f z + inner ℝ w (y - z) ≤ f y}

/-- Integrability, weak duality, zero-gap criteria, and simultaneous optimality
for every primal admissible function and every feasible flux. -/
def DomainOptimality {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (hp : 1 < p.real) (F : Ω → Vector d → ℝ)
    (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ) : Prop :=
  ∀ (u : W1pZero Ω 1 p) (σ : Flux Ω p hp), AllVariations Ω p hp σ ℓ →
    Integrable (gap Ω p hp F u σ) (volume.comap Subtype.val) ∧
    (∀ᵐ x : Ω ∂(volume.comap Subtype.val), 0 ≤ gap Ω p hp F u σ x) ∧
    (∫ x : Ω, gap Ω p hp F u σ x ∂(volume.comap Subtype.val)) =
      primalValue Ω p F ℓ u - dualValue Ω p hp F σ ∧
    0 ≤ (∫ x : Ω, gap Ω p hp F u σ x ∂(volume.comap Subtype.val)) ∧
    ((∫ x : Ω, gap Ω p hp F u σ x ∂(volume.comap Subtype.val)) = 0 ↔
      ∀ᵐ x : Ω ∂(volume.comap Subtype.val),
        F x (Primal.gradientMap Ω p u x.val) +
          (pointwiseConjugate F x (σ x.val)).toReal =
            inner ℝ (σ x.val) (Primal.gradientMap Ω p u x.val)) ∧
    ((∫ x : Ω, gap Ω p hp F u σ x ∂(volume.comap Subtype.val)) = 0 ↔
      ∀ᵐ x : Ω ∂(volume.comap Subtype.val),
        σ x.val ∈ fiberSubdifferential (F x) (Primal.gradientMap Ω p u x.val)) ∧
    (((∀ v, primalValue Ω p F ℓ u ≤ primalValue Ω p F ℓ v) ∧
      (∀ τ : Flux Ω p hp, AllVariations Ω p hp τ ℓ →
        dualValue Ω p hp F τ ≤ dualValue Ω p hp F σ)) ↔
      ∀ᵐ x : Ω ∂(volume.comap Subtype.val),
        σ x.val ∈ fiberSubdifferential (F x) (Primal.gradientMap Ω p u x.val))

/-- All hypotheses of the Dirichlet–flux theorem, with the original
Lebesgue–Carathéodory convention and without boundary regularity. -/
def OptimalFlux : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent) (hp : 1 < p.real)
    (F : Ω → Vector d → ℝ) (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ),
    ((∀ z, AEMeasurable (fun x => F x z) (volume.comap Subtype.val)) ∧
      ∀ᵐ x ∂(volume.comap Subtype.val), Continuous (F x)) →
  ∀ (a₀ a₁ : ℝ) (a : Ω → ℝ), 0 < a₀ → 0 ≤ a₁ →
    Integrable a (volume.comap Subtype.val) →
    (∀ᵐ x ∂(volume.comap Subtype.val), 0 ≤ a x) →
    (∀ᵐ x ∂(volume.comap Subtype.val), ∀ z,
      a₀ * ‖z‖ ^ p.real - a x ≤ F x z ∧ F x z ≤ a x + a₁ * ‖z‖ ^ p.real) →
    (∀ᵐ x ∂(volume.comap Subtype.val), ConvexOn ℝ univ (F x)) →
    DomainOptimality Ω p hp F ℓ

end VariationalNotes.Flux.ConstitutiveRelationSpecs
