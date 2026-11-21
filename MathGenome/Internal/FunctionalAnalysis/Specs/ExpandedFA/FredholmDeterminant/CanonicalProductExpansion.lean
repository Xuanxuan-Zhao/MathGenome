import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Independent statement of the square-summable scalar canonical-product expansion.
All products and sums use the unconditional finite-subset summation filter. -/
namespace ExpandedFA.FredholmDeterminant.CanonicalProductExpansion.Spec

universe u

/-- The genus-one product has the indicated exponential expansion near zero.
The index type is arbitrary, including empty and finite types. -/
def CanonicalExpansion : Prop :=
  ∀ {I : Type u} (a : I → ℂ), Summable (fun i => ‖a i‖ ^ 2) →
    (∀ n : ℕ, Summable (fun i => ‖a i ^ (n + 2)‖)) ∧
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      Summable (fun n : ℕ =>
        ‖-(z ^ (n + 2) / ((n + 2 : ℕ) : ℂ)) * (∑' i, a i ^ (n + 2))‖) ∧
      HasProd (fun i => (1 - z * a i) * Complex.exp (z * a i))
        (Complex.exp (∑' n : ℕ,
          -(z ^ (n + 2) / ((n + 2 : ℕ) : ℂ)) * (∑' i, a i ^ (n + 2)))) ∧
      (∏' i, (1 - z * a i) * Complex.exp (z * a i)) =
        Complex.exp (∑' n : ℕ,
          -(z ^ (n + 2) / ((n + 2 : ℕ) : ℂ)) * (∑' i, a i ^ (n + 2)))

end ExpandedFA.FredholmDeterminant.CanonicalProductExpansion.Spec
