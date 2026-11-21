import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.ExponentCountingRank
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-! Independent specification of paper.tex:2977–3016.
The index type is arbitrary: finite and empty divisors are included without
padding by artificial zeros. Local finiteness counts entries, so repetitions
are retained and every multiplicity is finite. No bound at s = ρ is assumed.
-/
noncomputable section
open Filter Set
open scoped Topology

namespace D12Complex.CanonicalLowerCircles
open ExponentCountingRank

/-- An eventual bound for every strictly larger exponent. -/
def CountingGrowth {ι : Type} (a : ι → ℂ) (ρ : ℝ) : Prop :=
  ∀ s : ℝ, ρ < s → ∃ C : ℝ,
    ∀ᶠ r : ℝ in atTop, (countingFunction a r : ℝ) ≤ C * r ^ s

/-- The actual canonical product, using the shared elementary factors. -/
def canonicalProduct {ι : Type} (p : ℕ) (a : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' i, Specs.D12Complex.Ch16.CanonicalFactors.factor_value p (z / a i)

end D12Complex.CanonicalLowerCircles

namespace Specs.D12Complex.Ch17.CanonicalLowerCircles
open _root_.D12Complex _root_.D12Complex.ExponentCountingRank
open _root_.D12Complex.CanonicalLowerCircles

def summable_above_type : Prop := ∀ {ι : Type} (a : ι → ℂ) (ρ : ℝ),
  LocallyFiniteDivisor a → CountingGrowth a ρ →
  ∀ s : ℝ, ρ < s → Summable (fun i => ‖a i‖ ^ (-s))

/-- Convergence is an actual locally uniform limit of the finite subproducts,
not just a totalized tprod. Entirety and the exact zero set are included. -/
def canonical_product_converges_type : Prop := ∀ {ι : Type} (a : ι → ℂ) (ρ : ℝ),
  0 ≤ ρ → LocallyFiniteDivisor a → (∀ i, a i ≠ 0) → CountingGrowth a ρ →
  HasProdLocallyUniformlyOn
    (fun i z => Specs.D12Complex.Ch16.CanonicalFactors.factor_value ⌊ρ⌋₊ (z / a i))
    (canonicalProduct ⌊ρ⌋₊ a) univ ∧
  HolomorphicOn univ (canonicalProduct ⌊ρ⌋₊ a) ∧
  ∀ z : ℂ, (canonicalProduct ⌊ρ⌋₊ a z = 0 ↔ ∃ i, z = a i)

/-- A proved quantitative component, stated independently for continuation. -/
def far_logarithms_le_power_type : Prop := ∀ {ι : Type} (a : ι → ℂ) (p : ℕ) (s : ℝ),
  s ≤ (p : ℝ) + 1 → Summable (fun i => ‖a i‖ ^ (-s)) →
  ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ ≤ 2 * R →
    ‖∑' i : {i // 4 * R < ‖a i‖},
      Specs.D12Complex.Ch16.CanonicalFactors.logFactor_value p (z / a i.val)‖ ≤ C * R ^ s

/-- Uniformly on each entire selected circle; every radius is positive,
tends to infinity, misses every divisor modulus, and the product is nonzero.
The nonzero assertions prevent Real.log 0's totalization from hiding a zero. -/
def lower_circles_type : Prop := ∀ {ι : Type} (a : ι → ℂ) (ρ : ℝ),
  0 ≤ ρ → LocallyFiniteDivisor a → (∀ i, a i ≠ 0) → CountingGrowth a ρ →
  ∀ t : ℝ, ρ < t → t < (⌊ρ⌋₊ : ℝ) + 1 →
  ∃ (r : ℕ → ℝ) (C : ℝ), 0 < C ∧ Tendsto r atTop atTop ∧
    ∀ k : ℕ, 0 < r k ∧ (∀ i, ‖a i‖ ≠ r k) ∧
      ∀ z : ℂ, ‖z‖ = r k → canonicalProduct ⌊ρ⌋₊ a z ≠ 0 ∧
        -C * (r k) ^ t ≤ Real.log ‖canonicalProduct ⌊ρ⌋₊ a z‖

/-- Complete original obligation, retaining the convergence part even if
there is no t in the stated open interval in a later generalization. -/
def canonical_lower_circles_type : Prop :=
  canonical_product_converges_type ∧ lower_circles_type

end Specs.D12Complex.Ch17.CanonicalLowerCircles
