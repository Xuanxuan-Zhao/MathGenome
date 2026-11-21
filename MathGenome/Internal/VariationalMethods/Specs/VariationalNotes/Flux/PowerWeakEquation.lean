import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.PowerEnergy
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.ConstitutiveRelation

/-! Power assertion and converse of `prop:optimal-flux`, paper.tex 4478–4510.
The zero-boundary scalar Sobolev space, restricted Lebesgue measure, and
Euclidean gradient are exactly the shared upstream objects. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
namespace VariationalNotes.Flux.PowerWeakEquationSpecs
open Sobolev WeakDivergenceSpec PowerEnergySpecs

/-- The value at zero is explicit, including when 1 < p < 2. -/
def B {d : ℕ} (p : ℝ) (z : Vector d) : Vector d :=
  if z = 0 then 0 else ‖z‖ ^ (p - 2) • z

def BType := {d : ℕ} → ℝ → Vector d → Vector d

def Constitutive {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
    (u : W1pZero Ω 1 p) (σ : Flux Ω p hp) : Prop :=
  ∀ᵐ x ∂domainMeasure Ω, σ x = B p.real (Primal.gradientMap Ω p u x)

def WeakSolution {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ) (u : W1pZero Ω 1 p) : Prop :=
  ∀ v : W1pZero Ω 1 p,
    (∫ x, inner ℝ (B p.real (Primal.gradientMap Ω p u x))
      (Primal.gradientMap Ω p v x) ∂domainMeasure Ω) = ℓ v

def OptimalPair {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
    (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ) (u : W1pZero Ω 1 p) (σ : Flux Ω p hp) : Prop :=
  (∀ v, primalObjective Ω p ℓ u ≤ primalObjective Ω p ℓ v) ∧
  AllVariations Ω p hp σ ℓ ∧
  (∀ τ : Flux Ω p hp, AllVariations Ω p hp τ ℓ →
    dualObjective Ω p hp τ ≤ dualObjective Ω p hp σ)

def PowerSubdifferential : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 < p → ∀ z : Vector d,
    ConstitutiveRelationSpecs.fiberSubdifferential (energy p) z = {B p z}

def PowerFluxIntegrability : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
    (u : W1pZero Ω 1 p),
    MemLp (fun x => B p.real (Primal.gradientMap Ω p u x))
      (conjugate p hp).ennreal (domainMeasure Ω)

def PowerOptimality : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent) (hp : 1 < p.real) (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ)
    (u : W1pZero Ω 1 p) (σ : Flux Ω p hp),
    (OptimalPair Ω p hp ℓ u σ ↔ AllVariations Ω p hp σ ℓ ∧ Constitutive Ω p hp u σ) ∧
    (OptimalPair Ω p hp ℓ u σ ↔ WeakSolution Ω p ℓ u ∧ Constitutive Ω p hp u σ)

/-- Every weak solution is the unique minimizer and provides an optimal
feasible flux; every minimizer solves the weak equation. Existence is included. -/
def PowerWeakSolutions : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent) (hp : 1 < p.real) (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ),
    (∃! u : W1pZero Ω 1 p, WeakSolution Ω p ℓ u) ∧
    ∀ u : W1pZero Ω 1 p,
      (WeakSolution Ω p ℓ u ↔ ∀ v, primalObjective Ω p ℓ u ≤ primalObjective Ω p ℓ v) ∧
      (WeakSolution Ω p ℓ u →
        (∀ v, (∀ w, primalObjective Ω p ℓ v ≤ primalObjective Ω p ℓ w) → v = u) ∧
        ∃ σ : Flux Ω p hp, OptimalPair Ω p hp ℓ u σ ∧ Constitutive Ω p hp u σ)

end VariationalNotes.Flux.PowerWeakEquationSpecs
