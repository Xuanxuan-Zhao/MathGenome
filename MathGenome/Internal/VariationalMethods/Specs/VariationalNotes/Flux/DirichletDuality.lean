import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.PrimalAttainment
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.WeakDivergence
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.IntegralConjugacy
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.BanachFenchel

noncomputable section
universe u
open MeasureTheory TopologicalSpace Set
namespace VariationalNotes.Flux.DirichletDualitySpecs
open Sobolev Primal WeakDivergenceSpec IntegralConjugacySpecs

/-- The conjugate of the negative load, on the whole Banach space. -/
def NegativeLoadConjugate : Prop := by
  classical
  exact ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ℓ q : X →L[ℝ] ℝ),
    ConvexAnalysis.Specs.conjugate (fun u => ((-ℓ u : ℝ) : WithTop ℝ)) q =
      if q = -ℓ then (0 : EReal) else ⊤

/-- The original objectives, finiteness, feasibility, and both attained extrema.
All evaluations use the given integrand, including its pointwise conjugate. -/
def DomainConclusion {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (hp : 1 < p.real) (F : Ω → Vector d → ℝ)
    (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ) : Prop :=
    let J := fun u : W1pZero Ω 1 p =>
      (∫ x : Ω, F x (Primal.gradientMap Ω p u x.val) ∂(volume.comap Subtype.val)) - ℓ u
    let H := fun σ : Flux Ω p hp =>
      -(∫ x : Ω, (pointwiseConjugate F x (σ x.val)).toReal ∂(volume.comap Subtype.val))
    (∀ u, Integrable (fun x : Ω => F x (Primal.gradientMap Ω p u x.val))
      (volume.comap Subtype.val)) ∧
    (∀ σ : Flux Ω p hp,
      (∀ᵐ x : Ω ∂(volume.comap Subtype.val),
        pointwiseConjugate F x (σ x.val) ≠ ⊤ ∧ pointwiseConjugate F x (σ x.val) ≠ ⊥) ∧
      Integrable (fun x : Ω => (pointwiseConjugate F x (σ x.val)).toReal)
        (volume.comap Subtype.val)) ∧
    (∀ σ : Flux Ω p hp,
      (AllVariations Ω p hp σ ℓ ↔ DistributionConstraint Ω p hp σ ℓ)) ∧
    ∃ (m : ℝ) (u : W1pZero Ω 1 p) (σ : Flux Ω p hp),
      J u = m ∧ (∀ v, m ≤ J v) ∧
      AllVariations Ω p hp σ ℓ ∧ H σ = m ∧
      (∀ τ : Flux Ω p hp, AllVariations Ω p hp τ ℓ → H τ ≤ m) ∧
      IsGLB (range J) m ∧ IsLUB (H '' {τ | AllVariations Ω p hp τ ℓ}) m

/-- Full Lebesgue–Carathéodory scope: base sections are measurable for the
completed measure; no common Borel representative is assumed. -/
def DirichletFlux : Prop :=
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
    DomainConclusion Ω p hp F ℓ

end VariationalNotes.Flux.DirichletDualitySpecs
