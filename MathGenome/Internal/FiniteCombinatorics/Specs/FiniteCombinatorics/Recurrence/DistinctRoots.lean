import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Recurrence.InitialValues

/-! Independent statements for paper.tex, Theorem p204:W15.
The roots are indexed by Fin r; injectivity expresses pairwise distinctness.
No root is assumed nonzero, and natural powers have the convention 0^0 = 1. -/

open scoped BigOperators
universe u
namespace Specs.FiniteCombinatorics.Recurrence

/-- Every root gives a geometric solution, including the zero root. -/
def geometric_isSolutionType : Prop :=
  ∀ {K : Type u} [Field K] {r : ℕ} (c : Fin r → K) (q : K),
    (characteristicPolynomialValue c).IsRoot q →
      IsSolutionValue c (fun n => q ^ n)

/-- The Vandermonde system determines the coefficients uniquely from any initial data. -/
def existsUnique_initial_coefficientsType : Prop :=
  ∀ {K : Type u} [Field K] {r : ℕ} (roots : Fin r → K),
    Function.Injective roots → ∀ init : Fin r → K,
      ∃! b : Fin r → K, ∀ j : Fin r, init j = ∑ i, b i * roots i ^ (j : ℕ)

/-- Full unique expansion of every solution in the r geometric sequences. -/
def existsUnique_geometric_expansionType : Prop :=
  ∀ {K : Type u} [Field K] {r : ℕ} (c : Fin r → K) (_hr : 1 ≤ r)
    (roots : Fin r → K), Function.Injective roots →
    (∀ i, (characteristicPolynomialValue c).IsRoot (roots i)) →
    ∀ a : ℕ → K, IsSolutionValue c a →
      ∃! b : Fin r → K, ∀ n : ℕ, a n = ∑ i, b i * roots i ^ n

end Specs.FiniteCombinatorics.Recurrence
