import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.ReversibleDirichletForm
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.TotalVariation
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Order.ConditionallyCompleteLattice.Finset

open scoped BigOperators
universe u v
namespace P207.Markov.SpectralMixing
noncomputable section
open WeightedSpace

/-- The actual weighted mean-zero subspace. -/
def meanZero {S : Type u} [Fintype S] (π : ProbabilityLaw S) (hπ : ∀ i, 0 < π i) :
    Submodule ℝ (WeightedSpace π hπ) where
  carrier := {f | ∑ i, (π i).toReal * f i = 0}
  zero_mem' := by
    change (∑ i, (π i).toReal * (0 : ℝ)) = 0
    simp
  add_mem' := by
    intro f g hf hg
    change (∑ i, (π i).toReal * f i) = 0 at hf
    change (∑ i, (π i).toReal * g i) = 0 at hg
    change (∑ i, (π i).toReal * (f i + g i)) = 0
    simp only [mul_add, Finset.sum_add_distrib, hf, hg, add_zero]
  smul_mem' := by
    intro r f hf
    change (∑ i, (π i).toReal * f i) = 0 at hf
    change (∑ i, (π i).toReal * (r * f i)) = 0
    simp only [mul_left_comm _ r, ← Finset.mul_sum, hf, mul_zero]

/-- Invariance is an obligation, not a spectral certificate. -/
def Invariant {S : Type u} [Fintype S] (π : ProbabilityLaw S) (hπ : ∀ i, 0 < π i)
    (P : StochasticMatrix S) : Prop :=
  ∀ f ∈ meanZero π hπ, transitionLinear π hπ P f ∈ meanZero π hπ

/-- The genuine restriction, with the invariance proof supplied explicitly. -/
def restricted {S : Type u} [Fintype S] (π : ProbabilityLaw S) (hπ : ∀ i, 0 < π i)
    (P : StochasticMatrix S) (h : Invariant π hπ P) :
    meanZero π hπ →ₗ[ℝ] meanZero π hπ :=
  (transitionLinear π hπ P).restrict h

/-- Absolute values of actual real eigenvalues; no chosen bound is involved. -/
def eigenAbsSet {E : Type*} [AddCommGroup E] [Module ℝ E] (T : E →ₗ[ℝ] E) : Set ℝ :=
  {a | ∃ lam : ℝ, Module.End.HasEigenvalue T lam ∧ a = |lam|}

def radius {E : Type*} [AddCommGroup E] [Module ℝ E] (T : E →ₗ[ℝ] E) : ℝ :=
  sSup (eigenAbsSet T)

/-- Half-lazification acts on functions as (I+P)/2. -/
def halfLazy {E : Type*} [AddCommGroup E] [Module ℝ E] (T : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  (1 / 2 : ℝ) • (LinearMap.id + T)

/-- Density of the point-start law, relative to the stationary probability. -/
def density {S : Type u} [Fintype S] (π : ProbabilityLaw S) (hπ : ∀ i, 0 < π i)
    (P : StochasticMatrix S) (i : S) (n : ℕ) : WeightedSpace π hπ :=
  fun x => (power P n i x).toReal / (π x).toReal

/-- Center the density by the constant function one. -/
def centeredDensity {S : Type u} [Fintype S] (π : ProbabilityLaw S)
    (hπ : ∀ i, 0 < π i) (P : StochasticMatrix S) (i : S) (n : ℕ) :
    WeightedSpace π hπ := fun x => density π hπ P i n x - 1

namespace Spec

-- Explicit value bindings for the canonical constructions above.
def meanZeroType := {S : Type u} → [Fintype S] → (π : ProbabilityLaw S) →
  (hπ : ∀ i, 0 < π i) → Submodule ℝ (WeightedSpace π hπ)
def meanZeroValue : meanZeroType.{u} := @meanZero

def InvariantType := {S : Type u} → [Fintype S] → (π : ProbabilityLaw S) →
  (hπ : ∀ i, 0 < π i) → StochasticMatrix S → Prop
def InvariantValue : InvariantType.{u} := @Invariant

def restrictedType := {S : Type u} → [Fintype S] → (π : ProbabilityLaw S) →
  (hπ : ∀ i, 0 < π i) → (P : StochasticMatrix S) → Invariant π hπ P →
  (meanZero π hπ →ₗ[ℝ] meanZero π hπ)
def restrictedValue : restrictedType.{u} := @restricted

def eigenAbsSetType := {E : Type v} → [AddCommGroup E] → [Module ℝ E] →
  (E →ₗ[ℝ] E) → Set ℝ
def eigenAbsSetValue : eigenAbsSetType.{v} := @eigenAbsSet

def radiusType := {E : Type v} → [AddCommGroup E] → [Module ℝ E] → (E →ₗ[ℝ] E) → ℝ
def radiusValue : radiusType.{v} := @radius

def halfLazyType := {E : Type v} → [AddCommGroup E] → [Module ℝ E] →
  (E →ₗ[ℝ] E) → (E →ₗ[ℝ] E)
def halfLazyValue : halfLazyType.{v} := @halfLazy

def densityType := {S : Type u} → [Fintype S] → (π : ProbabilityLaw S) →
  (hπ : ∀ i, 0 < π i) → StochasticMatrix S → S → ℕ → WeightedSpace π hπ
def densityValue : densityType.{u} := @density

def centeredDensityValue : densityType.{u} := @centeredDensity

/-- Full source theorem, including construction of the spectrum and its maximum.
The positivity and invariance witnesses are conclusions, not extra assumptions. -/
def spectral_tv : Prop :=
  ∀ {S : Type u} [Fintype S] [Nontrivial S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S),
    Irreducible P → IsReversible P π →
    ∃ (hπ : ∀ i, 0 < π i) (h : Invariant π hπ P),
      let T := restricted π hπ P h
      (∃ (b : OrthonormalBasis (Fin (Module.finrank ℝ (meanZero π hπ))) ℝ (meanZero π hπ))
         (lam : Fin (Module.finrank ℝ (meanZero π hπ)) → ℝ),
        (∀ k, Module.End.HasEigenvector T (lam k) (b k)) ∧
        (∀ a, Module.End.HasEigenvalue T a ↔ ∃ k, lam k = a)) ∧
      IsGreatest (eigenAbsSet T) (radius T) ∧
      (∀ i n, totalVariation (power P n i) π ≤
        (1 / 2 : ℝ) * Real.sqrt ((π i).toReal⁻¹ - 1) * radius T ^ n) ∧
      (∀ a, Module.End.HasEigenvalue (halfLazy (transitionLinear π hπ P)) a → 0 ≤ a) ∧
      IsGreatest (eigenAbsSet (halfLazy T)) (radius (halfLazy T)) ∧
      radius (halfLazy T) < 1
end Spec
end
end P207.Markov.SpectralMixing
