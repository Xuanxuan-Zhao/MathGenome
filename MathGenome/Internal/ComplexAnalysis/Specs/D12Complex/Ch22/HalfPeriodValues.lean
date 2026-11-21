import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TorusSurface
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.WeierstrassEquations

/-! Half-period and branch-value conclusions of paper.tex:3895–3939.
Zeros are stated off the lattice: assigned scalar values at poles are irrelevant.
Orders are germ orders on the plane, which are the orders in quotient charts. -/
noncomputable section

namespace Specs.D12Complex.Ch22.HalfPeriodValues
open _root_.D12Complex.TorusSurface
open WeierstrassSeries (weierstrassP)
open WeierstrassEquations (g₂ g₃)

def halfPeriod (ω₁ ω₂ : ℂ) : Fin 3 → ℂ :=
  ![ω₁ / 2, ω₂ / 2, (ω₁ + ω₂) / 2]

def branchValue (ω₁ ω₂ : ℂ) (i : Fin 3) : ℂ :=
  weierstrassP ω₁ ω₂ (halfPeriod ω₁ ω₂ i)

def classes_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    Function.Injective (fun i => projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)) ∧
    (∀ i, halfPeriod ω₁ ω₂ i ∉ lattice ω₁ ω₂) ∧
    (∀ q : Torus ω₁ ω₂, (q ≠ 0 ∧ (2 : ℕ) • q = 0) ↔
      ∃ i, q = projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i))

def zeros_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ z ∉ lattice ω₁ ω₂, deriv (weierstrassP ω₁ ω₂) z = 0 ↔
      ∃ i, projection ω₁ ω₂ z = projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)

def simple_zeros_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ i,
    meromorphicOrderAt (deriv (weierstrassP ω₁ ω₂)) (halfPeriod ω₁ ω₂ i) = 1

def all_simple_zeros_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ z ∉ lattice ω₁ ω₂,
    deriv (weierstrassP ω₁ ω₂) z = 0 →
      meromorphicOrderAt (deriv (weierstrassP ω₁ ω₂)) z = 1

def distinct_values_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    Function.Injective (branchValue ω₁ ω₂)

def factorization_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ X : ℂ,
    4 * X ^ 3 - g₂ ω₁ ω₂ * X - g₃ ω₁ ω₂ =
      4 * ∏ i : Fin 3, (X - branchValue ω₁ ω₂ i)

def discriminant_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    g₂ ω₁ ω₂ ^ 3 - 27 * g₃ ω₁ ω₂ ^ 2 ≠ 0

def double_zeros_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ i,
    meromorphicOrderAt
      (fun z => weierstrassP ω₁ ω₂ z - branchValue ω₁ ω₂ i)
      (halfPeriod ω₁ ω₂ i) = 2

def second_derivative_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ i,
    deriv (deriv (weierstrassP ω₁ ω₂)) (halfPeriod ω₁ ω₂ i) ≠ 0

end Specs.D12Complex.Ch22.HalfPeriodValues
