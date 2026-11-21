import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.OrderDivisorDefinitions

/-! The omitted-value assertion of paper.tex:3092–3106 (D12.17.07).
The function carries only weak entire holomorphy and is measured by the
canonical log-log order. The nonintegral-order assertion is a separate goal. -/
noncomputable section

namespace Specs.D12Complex.Ch17.FiniteOrderOmittedValue
open _root_.D12Complex.OrderDivisorDefinitions
open Specs.D12Complex.Ch17.OrderDivisorDefinitions

/-- A nonconstant finite-order entire function omitting a has a nonconstant
polynomial exponential representation and takes every other finite value. -/
def finite_order_omitted_value_type : Prop :=
  ∀ f : NonzeroEntireFunction,
    (¬ ∃ c : ℂ, ∀ z : ℂ, f.toFun z = c) →
    order_value f ≠ ⊤ →
    ∀ a : ℂ, (∀ z : ℂ, f.toFun z ≠ a) →
    ∃ Q : Polynomial ℂ, 0 < Q.natDegree ∧
      (∀ z : ℂ, f.toFun z = a + Complex.exp (Q.eval z)) ∧
      ∀ b : ℂ, b ≠ a → ∃ z : ℂ, f.toFun z = b

end Specs.D12Complex.Ch17.FiniteOrderOmittedValue
