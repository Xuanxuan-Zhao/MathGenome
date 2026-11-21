import MathGenome.Internal.Specs.D05.M08.Minpoly
import MathGenome.Internal.Specs.D05.M09.Diagonalizable
import Mathlib.Algebra.Polynomial.BigOperators

/-!
Independent specifications for K05.09.minpoly_criterion, paper.tex:1288–1294.
All factors and eigenvalues belong to the original scalar field. A `Finset K`
records distinct scalars, and its product is `1` when the set is empty.
The minimal polynomial and diagonalizability are the accepted upstream objects.
-/

namespace Specs.D05.M09.MinpolyCriterion

/-- The full criterion, including both implications and the empty product. -/
def diagonalizable_iff_distinct_linear_factors : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Diagonalizable.diagonalizable_value K V T ↔
      ∃ s : Finset K, M08.Minpoly.minimalPolynomial_value K V T =
        ∏ a ∈ s, (Polynomial.X - Polynomial.C a)

/-- In an eigenbasis, a polynomial annihilates the operator exactly when it
vanishes at every eigenvalue occurring in that basis (repetitions allowed). -/
def annihilates_iff_vanishes_on_eigenbasis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (μ : Fin n → K), (∀ i, T (b i) = μ i • b i) →
    ∀ p : Polynomial K, Polynomial.aeval T p = 0 ↔ ∀ i, p.eval (μ i) = 0

/-- The empty factorization occurs exactly on the zero space. -/
def empty_product_iff_zero_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    M08.Minpoly.minimalPolynomial_value K V T =
      ∏ a ∈ (∅ : Finset K), (Polynomial.X - Polynomial.C a) ↔ ∀ v : V, v = 0

end Specs.D05.M09.MinpolyCriterion
