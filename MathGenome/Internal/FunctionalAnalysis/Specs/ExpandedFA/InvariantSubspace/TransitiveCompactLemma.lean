import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! Independent specification of Lomonosov's transitive-algebra lemma,
`fa2:p2:lomonosov-lemma`, paper.tex:9671–9676.

The algebra is unital, but need not be norm closed. Invariance concerns
complex linear subspaces closed in the original norm topology. Compactness
uses the original target, through the shared unit-ball-image definition.
The nonzero eigenvector is part of the conclusion, including in finite
dimension; no infinite-dimensional or nontrivial-space assumption is added.
-/

namespace ExpandedFA.InvariantSubspace.TransitiveCompactLemma.Spec

universe u

/-- No nontrivial common closed invariant complex linear subspace. -/
def IsTransitive {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (𝒜 : Subalgebra ℂ (X →L[ℂ] X)) : Prop :=
  ∀ M : Submodule ℂ X, IsClosed (M : Set X) →
    (∀ A ∈ 𝒜, ∀ x ∈ M, A x ∈ M) → M = ⊥ ∨ M = ⊤

/-- A nonzero compact operator can be multiplied on the left by an algebra
member to obtain eigenvalue one. -/
def LomonosovLemma : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (𝒜 : Subalgebra ℂ (X →L[ℂ] X)), IsTransitive 𝒜 →
    ∀ K : X →L[ℂ] X,
      Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap → K ≠ 0 →
      ∃ A ∈ 𝒜, ∃ x : X, x ≠ 0 ∧ A (K x) = x

end ExpandedFA.InvariantSubspace.TransitiveCompactLemma.Spec
