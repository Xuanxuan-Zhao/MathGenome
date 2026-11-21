import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.EntireZeros

/-! Independent propositions for D12.16.04, paper.tex:2798–2805.
Natural multiplicities are certified by equality to the actual analytic orders.
Finite products include the empty product; the infinite product has genus n.
No growth or finite-order hypothesis is imposed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Specs.D12Complex.Ch16.EntireFactorization
open _root_.D12Complex

/-- Matching finite local orders remove every apparent quotient singularity. -/
def quotient_extension_type : Prop :=
  ∀ (f P : ℂ → ℂ) (d : ℂ → ℕ), HolomorphicOn univ f →
    HolomorphicOn univ P →
    (∀ z, analyticOrderAt f z = (d z : ℕ∞)) →
    (∀ z, analyticOrderAt P z = (d z : ℕ∞)) →
    ∃ q : ℂ → ℂ, HolomorphicOn univ q ∧ (∀ z, q z ≠ 0) ∧
      (∀ z, P z ≠ 0 → q z = f z / P z) ∧ ∀ z, f z = q z * P z

def entire_logarithm_type : Prop :=
  ∀ q : ℂ → ℂ, HolomorphicOn univ q → (∀ z, q z ≠ 0) →
    ∃ g : ℂ → ℂ, HolomorphicOn univ g ∧ ∀ z, Complex.exp (g z) = q z

/-- This conclusion constructs the locally finite divisor; it is not an input. -/
def zero_divisor_type : Prop :=
  ∀ f : ℂ → ℂ, HolomorphicOn univ f → (∃ z, f z ≠ 0) →
    ∃ d : ℂ → ℕ, LocallyFiniteSupport d ∧
      ∀ z, analyticOrderAt f z = (d z : ℕ∞)

/-- Finite nonzero zeros use E₀, repeated d(a) times, and a separate center power. -/
def finite_factorization_type : Prop :=
  ∀ (f : ℂ → ℂ) (d : ℂ → ℕ) (s : Finset ℂ), HolomorphicOn univ f →
    (∀ z, analyticOrderAt f z = (d z : ℕ∞)) →
    (∀ z, z ∈ s ↔ z ≠ 0 ∧ d z ≠ 0) →
    ∃ g : ℂ → ℂ, HolomorphicOn univ g ∧ ∀ z,
      f z = z ^ d 0 * Complex.exp (g z) *
        ∏ a ∈ s, CanonicalFactors.factor_value 0 (z / a) ^ d a

/-- The equivalence enumerates each multiplicity slot exactly once. -/
def infinite_factorization_type : Prop :=
  ∀ (f : ℂ → ℂ) (d : ℂ → ℕ), HolomorphicOn univ f →
    (∀ z, analyticOrderAt f z = (d z : ℕ∞)) → LocallyFiniteSupport d →
    {z : ℂ | z ≠ 0 ∧ d z ≠ 0}.Infinite →
    ∃ (e : ℕ ≃ EntireZeros.Occurrences_value d) (g : ℂ → ℂ),
      Tendsto (fun n => ‖(e n).1.1‖) atTop atTop ∧ HolomorphicOn univ g ∧
      ∀ z, f z = z ^ d 0 * Complex.exp (g z) *
        ∏' n, CanonicalFactors.factor_value n (z / (e n).1.1)

/-- Full existence, with finite and infinite divisors and the true center order. -/
def entire_factorization_type : Prop :=
  ∀ f : ℂ → ℂ, HolomorphicOn univ f → (∃ z, f z ≠ 0) →
    ∃ d : ℂ → ℕ, LocallyFiniteSupport d ∧
      (∀ z, analyticOrderAt f z = (d z : ℕ∞)) ∧
      ((∃ (s : Finset ℂ) (g : ℂ → ℂ),
          (∀ z, z ∈ s ↔ z ≠ 0 ∧ d z ≠ 0) ∧ HolomorphicOn univ g ∧
          ∀ z, f z = z ^ d 0 * Complex.exp (g z) *
            ∏ a ∈ s, CanonicalFactors.factor_value 0 (z / a) ^ d a) ∨
       (∃ (e : ℕ ≃ EntireZeros.Occurrences_value d) (g : ℂ → ℂ),
          Tendsto (fun n => ‖(e n).1.1‖) atTop atTop ∧ HolomorphicOn univ g ∧
          ∀ z, f z = z ^ d 0 * Complex.exp (g z) *
            ∏' n, CanonicalFactors.factor_value n (z / (e n).1.1)))

end Specs.D12Complex.Ch16.EntireFactorization
