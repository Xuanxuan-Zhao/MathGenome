import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M04.Trace
import MathGenome.Internal.Specs.D05.M08.NewtonIdentities.Series

/-! Newton identities, paper.tex:1238–1252. The finite sum is indexed by
`j = i - 1`, so its exponents are `j+1`. No splitting is assumed. -/
noncomputable section
namespace D05.M08.NewtonIdentities
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Signed characteristic coefficient, used only in degrees `k ≤ finrank K V`. -/
def elementaryCoeff (T : V →ₗ[K] V) (k : ℕ) : K :=
  (-1) ^ k * (Specs.D05.M08.Charpoly.charpoly_value T).coeff (Module.finrank K V - k)
end D05.M08.NewtonIdentities

namespace Specs.D05.M08.NewtonIdentities
open _root_.D05.M08.NewtonIdentities

def coefficient_zero : Prop := ∀ {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] (T : V →ₗ[K] V), elementaryCoeff T 0 = 1

def characteristic_expansion : Prop := ∀ {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] (T : V →ₗ[K] V),
  Charpoly.charpoly_value T = ∑ k ∈ Finset.range (Module.finrank K V + 1),
    Polynomial.C ((-1)^k * elementaryCoeff T k) * Polynomial.X ^ (Module.finrank K V - k)

/-- This is the coefficient version of `E(t) = t^n χ_T(t⁻¹)`. -/
def determinant_coefficients : Prop := ∀ {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V]
  (b : Module.Basis (Fin (Module.finrank K V)) K V) (T : V →ₗ[K] V)
  (k : ℕ), k ≤ Module.finrank K V →
    PowerSeries.coeff k (determinantSeries (LinearMap.toMatrix b b T)) =
      (-1)^k * elementaryCoeff T k

/-- The undivided identity holds in every characteristic. -/
def newton_identity : Prop := ∀ {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] (T : V →ₗ[K] V) (k : ℕ),
  1 ≤ k → k ≤ Module.finrank K V →
    (k : K) * elementaryCoeff T k = ∑ j ∈ Finset.range k,
      (-1)^j * elementaryCoeff T (k-(j+1)) * LinearMap.trace K V (T^(j+1))

/-- The source formulation for any coefficients giving the displayed expansion. -/
def newton_for_expansion : Prop := ∀ {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] (T : V →ₗ[K] V) (e : ℕ → K),
  Charpoly.charpoly_value T = ∑ k ∈ Finset.range (Module.finrank K V + 1),
    Polynomial.C ((-1)^k * e k) * Polynomial.X ^ (Module.finrank K V - k) →
  e 0 = 1 ∧ ∀ k, 1 ≤ k → k ≤ Module.finrank K V →
    (k : K) * e k = ∑ j ∈ Finset.range k,
      (-1)^j * e (k-(j+1)) * LinearMap.trace K V (T^(j+1))

/-- Only this division step requires characteristic zero. -/
def recursive_formula : Prop := ∀ {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] (T : V →ₗ[K] V) (k : ℕ),
  1 ≤ k → k ≤ Module.finrank K V →
    elementaryCoeff T k = (k : K)⁻¹ * ∑ j ∈ Finset.range k,
      (-1)^j * elementaryCoeff T (k-(j+1)) * LinearMap.trace K V (T^(j+1))

/-- Initial value and recurrence determine all characteristic coefficients. -/
def recursive_uniqueness : Prop := ∀ {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] (T : V →ₗ[K] V)
  (e : ℕ → K), e 0 = 1 →
  (∀ k, 1 ≤ k → k ≤ Module.finrank K V →
    (k : K) * e k = ∑ j ∈ Finset.range k,
      (-1)^j * e (k-(j+1)) * LinearMap.trace K V (T^(j+1))) →
  ∀ k, k ≤ Module.finrank K V → e k = elementaryCoeff T k

def zero_dimension : Prop := ∀ {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] (T : V →ₗ[K] V),
  Module.finrank K V = 0 → Charpoly.charpoly_value T = 1 ∧
    elementaryCoeff T 0 = 1 ∧ ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ Module.finrank K V
end Specs.D05.M08.NewtonIdentities
