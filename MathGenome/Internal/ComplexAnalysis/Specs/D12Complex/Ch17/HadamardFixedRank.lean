import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.FiniteOrderDivisorGrowth
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.CanonicalLowerCircles
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.RealPartPolynomial

/-! Fixed-rank part of Hadamard's theorem, paper.tex:3018–3046.
The divisor is the intrinsic repeated nonzero zero divisor. No infinitude,
positive order, or nonvanishing at the center is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Specs.D12Complex.Ch17.HadamardFixedRank
open _root_.D12Complex _root_.D12Complex.OrderDivisorDefinitions
open _root_.D12Complex.CanonicalLowerCircles

/-- Actual locally uniform product convergence and equality of all local
multiplicities after restoring the center power. -/
def canonical_product_exact_type : Prop := ∀ f : NonzeroEntireFunction, order f ≠ ⊤ →
  let p := ⌊(order f).toReal⌋₊
  let m := (analyticOrderAt f.toFun 0).toNat
  HasProdLocallyUniformlyOn
    (fun i z => Specs.D12Complex.Ch16.CanonicalFactors.factor_value p (z / zeroLocation f i))
    (canonicalProduct p (zeroLocation f)) univ ∧
  HolomorphicOn univ (canonicalProduct p (zeroLocation f)) ∧
  ∀ z, analyticOrderAt (fun w => w ^ m * canonicalProduct p (zeroLocation f) w) z =
    analyticOrderAt f.toFun z

/-- An entire, everywhere nonzero extension of the quotient and an actual
entire logarithm. The factorization identifies the quotient off the divisor. -/
def entire_quotient_log_type : Prop := ∀ f : NonzeroEntireFunction, order f ≠ ⊤ →
  let p := ⌊(order f).toReal⌋₊
  let m := (analyticOrderAt f.toFun 0).toNat
  ∃ g h : ℂ → ℂ, HolomorphicOn univ g ∧ (∀ z, g z ≠ 0) ∧
    HolomorphicOn univ h ∧ (∀ z, Complex.exp (h z) = g z) ∧
    ∀ z, f.toFun z = z ^ m * g z * canonicalProduct p (zeroLocation f) z

/-- Full fixed-rank factorization, with sharp degree and exact divisor. -/
def hadamard_fixed_rank_type : Prop := ∀ f : NonzeroEntireFunction, order f ≠ ⊤ →
  let p := ⌊(order f).toReal⌋₊
  let m := (analyticOrderAt f.toFun 0).toNat
  ∃ Q : Polynomial ℂ, Q.natDegree ≤ p ∧
    HasProdLocallyUniformlyOn
      (fun i z => Specs.D12Complex.Ch16.CanonicalFactors.factor_value p (z / zeroLocation f i))
      (canonicalProduct p (zeroLocation f)) univ ∧
    HolomorphicOn univ (canonicalProduct p (zeroLocation f)) ∧
    (∀ z, analyticOrderAt (fun w => w ^ m * canonicalProduct p (zeroLocation f) w) z =
      analyticOrderAt f.toFun z) ∧
    ∀ z, f.toFun z = z ^ m * Complex.exp (Q.eval z) * canonicalProduct p (zeroLocation f) z
end Specs.D12Complex.Ch17.HadamardFixedRank
