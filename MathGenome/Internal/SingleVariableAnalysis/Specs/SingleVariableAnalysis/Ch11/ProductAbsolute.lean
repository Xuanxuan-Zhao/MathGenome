import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Absolute

/-! Independent statements for K03.11.product_absolute, paper.tex:1150–1165.
Products are ordered inclusive partial products; absolute convergence is the
ordinary convergence of the real series of complex magnitudes. -/
namespace Specs.SingleVariableAnalysis.Ch11.ProductAbsolute
open scoped BigOperators
open Specs.SingleVariableAnalysis.Ch11.Absolute
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit

def finiteProductUpper : Prop :=
  ∀ (u : ℕ → ℂ) (s : Finset ℕ), (∑ j ∈ s, ‖u j‖) < 1 →
    ‖(∏ j ∈ s, (1 + u j)) - 1‖ ≤
      (∑ j ∈ s, ‖u j‖) / (1 - ∑ j ∈ s, ‖u j‖)

def finiteProductLower : Prop :=
  ∀ (u : ℕ → ℂ) (s : Finset ℕ), (∑ j ∈ s, ‖u j‖) < 1 →
    1 - (∑ j ∈ s, ‖u j‖) ≤ ‖∏ j ∈ s, (1 + u j)‖

def absoluteProductConverges : Prop :=
  ∀ u : ℕ → ℂ, complexAbsolutelyConvergesValue u →
    (∀ n, 1 + u n ≠ 0) →
    ∃ L : ℂ, L ≠ 0 ∧ complexSequenceConvergesValue
      (fun N => ∏ n ∈ Finset.range (N + 1), (1 + u n)) L
end Specs.SingleVariableAnalysis.Ch11.ProductAbsolute
