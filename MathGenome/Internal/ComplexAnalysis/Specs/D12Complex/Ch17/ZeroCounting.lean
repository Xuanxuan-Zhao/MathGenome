import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.OrderDivisorDefinitions

/-! The closed-disk zero count uses actual analytic multiplicities.  Both
circles in the estimate may contain zeros (paper.tex:2924–2935). -/
noncomputable section
open scoped Classical
namespace Specs.D12Complex.Ch17.ZeroCounting
open _root_.D12Complex _root_.D12Complex.OrderDivisorDefinitions

def zeroCount_type := (ℂ → ℂ) → ℝ → ℕ
def zeroCount_value : zeroCount_type := fun f r =>
  ∑ᶠ z : ℂ, if ‖z‖ ≤ r then (analyticOrderAt f z).toNat else 0

def count_support_finite_type : Prop := ∀ f : NonzeroEntireFunction, ∀ r : ℝ,
  (Function.support (fun z : ℂ =>
    if ‖z‖ ≤ r then (analyticOrderAt f.toFun z).toNat else 0)).Finite

def counting_zeros_type : Prop := ∀ (f : ℂ → ℂ), HolomorphicOn Set.univ f →
  f 0 = 1 → ∀ r : ℝ, 0 < r →
    (zeroCount_value f r : ℝ) * Real.log 2 ≤
      Real.log (Specs.D12Complex.Ch17.OrderDivisorDefinitions.maximumModulus_value f (2 * r))

/-- Remove the finite center zero and normalize its remaining nonzero value.
The nonzero multiplicities are unchanged, while the center contributes exactly
m to every closed-disk count. The normalized entire function obeys the estimate. -/
def center_reduction_type : Prop := ∀ f : NonzeroEntireFunction,
  ∃ (m : ℕ) (c : ℂ) (g : ℂ → ℂ),
    analyticOrderAt f.toFun 0 = (m : ℕ∞) ∧ c ≠ 0 ∧
    HolomorphicOn Set.univ g ∧ g 0 = 1 ∧
    (∀ z, f.toFun z = z ^ m * (c * g z)) ∧
    (∀ z, z ≠ 0 → analyticOrderAt f.toFun z = analyticOrderAt g z) ∧
    (∀ r : ℝ, 0 ≤ r → zeroCount_value f.toFun r = m + zeroCount_value g r) ∧
    (∀ r : ℝ, 0 < r → (zeroCount_value g r : ℝ) * Real.log 2 ≤
      Real.log (Specs.D12Complex.Ch17.OrderDivisorDefinitions.maximumModulus_value g (2 * r)))
end Specs.D12Complex.Ch17.ZeroCounting
