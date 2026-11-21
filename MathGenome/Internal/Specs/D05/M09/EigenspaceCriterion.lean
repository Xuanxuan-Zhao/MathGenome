import MathGenome.Internal.Specs.D05.M09.Diagonalizable
import Mathlib.Algebra.BigOperators.Finprod

/-!
Independent specifications for K05.09.eigenspace_criterion, paper.tex:1275–1281.

`T.Eigenvalues` is the subtype of scalars in the named field `K` whose
canonical eigenspaces are nonzero. Thus every distinct eigenvalue is counted
once, without counting repeated eigenvectors or passing to a splitting field.
`∑ᶠ` is the finite-support sum. The upstream finite-dimensional eigenvalue
bound ensures that its index type is finite; the implementation proves and
uses this finiteness rather than assuming it. Empty spectra and zero spaces
are included. Diagonalizability is the upstream finite eigenbasis predicate.
-/

namespace Specs.D05.M09.EigenspaceCriterion

open scoped BigOperators

/-- The dimension of the sum of all distinct nonzero eigenspaces is the sum
of their dimensions. No assumption of diagonalizability is made. -/
def eigenspace_sum_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Module.finrank K (⨆ μ : T.Eigenvalues, T.eigenspace (μ : K) : Submodule K V) =
      ∑ᶠ μ : T.Eigenvalues, Module.finrank K (T.eigenspace (μ : K))

/-- An eigenbasis exists exactly when the eigenspaces span the whole space. -/
def diagonalizable_iff_eigenspaces_span : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T ↔
      (⨆ μ : T.Eigenvalues, T.eigenspace (μ : K)) = ⊤

/-- The paper's full dimension criterion over the original field, including
empty sums in dimension zero. -/
def dimension_criterion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V T ↔
      (∑ᶠ μ : T.Eigenvalues, Module.finrank K (T.eigenspace (μ : K))) =
        Module.finrank K V

end Specs.D05.M09.EigenspaceCriterion
