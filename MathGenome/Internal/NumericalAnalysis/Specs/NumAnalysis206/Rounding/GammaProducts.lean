import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section

open scoped BigOperators

namespace Specs.NumAnalysis206.Rounding

def gammaType : Type := ℕ → ℝ → ℝ
def gammaValue : gammaType := fun n u => (n : ℝ) * u / (1 - (n : ℝ) * u)
def budgetDomainType : Type := ℕ → ℝ → Prop
def budgetDomainValue : budgetDomainType := fun n u =>
  0 ≤ u ∧ u < 1 ∧ (n : ℝ) * u < 1

def gammaNonneg : Prop := ∀ {n : ℕ} {u : ℝ}, budgetDomainValue n u → 0 ≤ gammaValue n u

def budgetDomainMono : Prop := ∀ {n N : ℕ} {u : ℝ},
  n ≤ N → budgetDomainValue N u → budgetDomainValue n u

def gammaMono : Prop := ∀ {n N : ℕ} {u : ℝ},
  n ≤ N → budgetDomainValue N u → gammaValue n u ≤ gammaValue N u

def factorsPositive : Prop := ∀ {n : ℕ} {u : ℝ} (δ : ℕ → ℝ) (ρ : ℕ → ℤ),
  budgetDomainValue n u → (∀ i < n, |δ i| ≤ u) →
  (∀ i < n, ρ i = -1 ∨ ρ i = 1) →
  ∀ i < n, 0 < 1 + δ i ∧ 1 + δ i ≠ 0 ∧
    0 < (1 + δ i) ^ (ρ i) ∧ (1 + δ i) ^ (ρ i) ≠ 0

def signedProducts : Prop := ∀ {n : ℕ} {u : ℝ} (δ : ℕ → ℝ) (ρ : ℕ → ℤ),
  budgetDomainValue n u → (∀ i < n, |δ i| ≤ u) →
  (∀ i < n, ρ i = -1 ∨ ρ i = 1) →
  ∃ θ : ℝ, (∏ i ∈ Finset.range n, (1 + δ i) ^ (ρ i)) = 1 + θ ∧
    |θ| ≤ gammaValue n u ∧ (n = 0 → θ = 0)

def emptyProduct : Prop := ∀ (u : ℝ) (δ : ℕ → ℝ) (ρ : ℕ → ℤ),
  (∏ i ∈ Finset.range 0, (1 + δ i) ^ (ρ i)) = 1 + (0 : ℝ) ∧ gammaValue 0 u = 0

end Specs.NumAnalysis206.Rounding
