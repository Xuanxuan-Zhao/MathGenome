import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.ExponentCountingRank
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.ZeroCounting
import Mathlib.Algebra.Order.Floor.Semiring

/-! Finite-order part of paper.tex:2954–2975. Order is the specified
extended nonnegative limsup; finite order includes order zero. -/
noncomputable section
namespace Specs.D12Complex.Ch17.FiniteOrderDivisorGrowth
open _root_.D12Complex.OrderDivisorDefinitions _root_.D12Complex.ExponentCountingRank

def counting_growth_type : Prop := ∀ f : NonzeroEntireFunction, order f ≠ ⊤ →
  ∀ s : ℝ, (order f).toReal < s → ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧
    ∀ r : ℝ, R ≤ r → (countingFunction (zeroLocation f) r : ℝ) ≤ C * r ^ s

def summable_above_order_type : Prop := ∀ f : NonzeroEntireFunction, order f ≠ ⊤ →
  ∀ s : ℝ, (order f).toReal < s → Summable (fun i => ‖zeroLocation f i‖ ^ (-s))

def divisorExponent_le_order_type : Prop := ∀ f : NonzeroEntireFunction,
  order f ≠ ⊤ → divisorExponent (zeroLocation f) ≤ order f

def floor_sum_type : Prop := ∀ f : NonzeroEntireFunction, order f ≠ ⊤ →
  Summable (fun i => ‖zeroLocation f i‖ ^ (-((⌊(order f).toReal⌋₊ : ℝ) + 1)))

def canonicalRank_le_floor_type : Prop := ∀ f : NonzeroEntireFunction, order f ≠ ⊤ →
  canonicalRank (zeroLocation f) ≤ (⌊(order f).toReal⌋₊ : ℕ∞)
end Specs.D12Complex.Ch17.FiniteOrderDivisorGrowth
