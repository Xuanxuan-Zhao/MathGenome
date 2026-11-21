import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.HadamardFixedRank
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Order.Interval.Finset.Nat

/-! Complete Hadamard conclusion, paper.tex:3018–3057. The same intrinsic
repeated divisor is used at the floor rank and at its least admissible rank.
All sums/products are unconditional; finite and empty divisors are included. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Specs.D12Complex.Ch17.HadamardFactorization
open _root_.D12Complex _root_.D12Complex.OrderDivisorDefinitions
open _root_.D12Complex.ExponentCountingRank _root_.D12Complex.CanonicalLowerCircles

/-- The coefficient correction from rank q to rank p. Constants, including
zero, use natDegree zero, consistently with the shared genus definition. -/
def rankCorrection_type := {ι : Type} → (ι → ℂ) → ℕ → ℕ → Polynomial ℂ
def rankCorrection_value : rankCorrection_type := fun a q p =>
  ∑ l ∈ Finset.Ioc q p, Polynomial.monomial l ((∑' i, (a i)⁻¹ ^ l) / (l : ℂ))

def rank_change_coefficients_type : Prop := ∀ {ι : Type} (a : ι → ℂ),
  LocallyFiniteDivisor a → ∀ q : ℕ, RankSummable a q →
  ∀ l : ℕ, q < l → Summable (fun i => ‖(a i)⁻¹ ^ l‖)

def rankCorrection_eval_type : Prop := ∀ {ι : Type} (a : ι → ℂ) (q p : ℕ) (z : ℂ),
  (rankCorrection_value a q p).eval z =
    ∑ l ∈ Finset.Ioc q p, z ^ l / (l : ℂ) * ∑' i, (a i)⁻¹ ^ l

def rankCorrection_degree_type : Prop := ∀ {ι : Type} (a : ι → ℂ) (q p : ℕ),
  (rankCorrection_value a q p).natDegree ≤ p

/-- Rank-change identity with genuine product convergence at both ranks. -/
def canonical_product_rank_change_type : Prop := ∀ {ι : Type} (a : ι → ℂ),
  LocallyFiniteDivisor a → ∀ q p : ℕ, q ≤ p → RankSummable a q →
  HasProdLocallyUniformlyOn
    (fun i z => Specs.D12Complex.Ch16.CanonicalFactors.factor_value q (z / a i))
    (canonicalProduct q a) univ ∧
  HasProdLocallyUniformlyOn
    (fun i z => Specs.D12Complex.Ch16.CanonicalFactors.factor_value p (z / a i))
    (canonicalProduct p a) univ ∧
  ∀ z, canonicalProduct p a z = canonicalProduct q a z *
    Complex.exp ((rankCorrection_value a q p).eval z)

/-- The fixed-rank conclusion and the minimal-rank conclusion for every
nonzero finite-order entire function, including order zero. -/
def hadamard_factorization_type : Prop :=
  Specs.D12Complex.Ch17.HadamardFixedRank.hadamard_fixed_rank_type ∧
  ∀ f : NonzeroEntireFunction, order f ≠ ⊤ →
    let p := ⌊(order f).toReal⌋₊
    let m := (analyticOrderAt f.toFun 0).toNat
    ∃ (q : ℕ) (Q : Polynomial ℂ),
      canonicalRank (zeroLocation f) = (q : ℕ∞) ∧ q ≤ p ∧
      Q.natDegree ≤ p ∧
      HasProdLocallyUniformlyOn
        (fun i z => Specs.D12Complex.Ch16.CanonicalFactors.factor_value q (z / zeroLocation f i))
        (canonicalProduct q (zeroLocation f)) univ ∧
      IsCanonicalFactorization f m q Q ∧
      (genus q Q : ℝ) ≤ (order f).toReal
end Specs.D12Complex.Ch17.HadamardFactorization
