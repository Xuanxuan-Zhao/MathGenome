import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.OrderDivisorDefinitions

/-! The infinite-preimage assertion of paper.tex:3092–3116 (d12:17-07).
Order is the shared extended nonnegative real log-log limsup. Nonintegral
means unequal to every natural number, since this order is nonnegative.
The zero set and each value fibre are sets of distinct complex points. -/
noncomputable section
open scoped ENNReal
namespace Specs.D12Complex.Ch17.NonintegralOrderValues
open _root_.D12Complex.OrderDivisorDefinitions
open Specs.D12Complex.Ch17.OrderDivisorDefinitions

/-- A finite set of zeros gives an actual polynomial times polynomial exponential. -/
def finite_zeros_polynomial_exp_type : Prop :=
  ∀ f : NonzeroEntireFunction, order_value f ≠ ⊤ →
    Set.Finite {z : ℂ | f.toFun z = 0} →
    ∃ A Q : Polynomial ℂ, A ≠ 0 ∧
      f.toFun = (fun z => A.eval z * Complex.exp (Q.eval z))

def finite_zeros_integral_order_type : Prop :=
  ∀ f : NonzeroEntireFunction, order_value f ≠ ⊤ →
    Set.Finite {z : ℂ | f.toFun z = 0} →
    ∃ n : ℕ, order_value f = (n : ℝ≥0∞)

/-- Infinitely many distinct preimages, for every finite target value. -/
def nonintegral_order_infinite_preimages_type : Prop :=
  ∀ f : NonzeroEntireFunction,
    (¬ ∃ c : ℂ, ∀ z, f.toFun z = c) →
    order_value f ≠ ⊤ →
    (∀ n : ℕ, order_value f ≠ (n : ℝ≥0∞)) →
    ∀ b : ℂ, Set.Infinite {z : ℂ | f.toFun z = b}

end Specs.D12Complex.Ch17.NonintegralOrderValues
