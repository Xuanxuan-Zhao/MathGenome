import MathGenome.Internal.Specs.D05.M02.Independence
import MathGenome.Internal.Specs.D05.M09.Eigenspace
import Mathlib.Data.Set.Card

/-!
Independent specifications for K05.09.distinct_independence, paper.tex:1264–1270.

All eigenspaces and eigenvalues use the given field. `iSupIndep` says that each
subspace intersects the sum of the others trivially; thus the sum is direct,
without asserting that it is the whole ambient space. The next two statements
spell out the finite zero-sum and uniqueness conditions. These independence
results hold in arbitrary dimension, and in particular in the paper's setting.
Only the counting conclusions require finite dimension. Empty index types and
zero spaces are allowed throughout, and no splitting hypothesis is imposed.
-/

namespace Specs.D05.M09.DistinctIndependence

open scoped BigOperators

/-- Distinct indexed scalars give an independent family of eigenspaces. -/
def eigenspaces_independent : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : I → K), Function.Injective μ →
      iSupIndep (fun i => T.eigenspace (μ i))

/-- The only finite zero sum of vectors in distinct eigenspaces is trivial. -/
def zero_sum_components : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : I → K), Function.Injective μ →
      ∀ (s : Finset I) (v : I → V),
        (∀ i ∈ s, T (v i) = μ i • v i) →
        (∑ i ∈ s, v i) = 0 → ∀ i ∈ s, v i = 0

/-- Two decompositions over the same finite set agree component by component. -/
def unique_components : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : I → K), Function.Injective μ →
      ∀ (s : Finset I) (v w : I → V),
        (∀ i ∈ s, v i ∈ T.eigenspace (μ i) ∧ w i ∈ T.eigenspace (μ i)) →
        (∑ i ∈ s, v i) = (∑ i ∈ s, w i) → ∀ i ∈ s, v i = w i

/-- Nonzero eigenvectors at distinct eigenvalues form an independent family. -/
def eigenvectors_independent : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : I → K), Function.Injective μ →
      ∀ v : I → V, (∀ i, T.HasEigenvector (μ i) (v i)) →
        LinearIndependent K v

/-- Every finite indexed family of distinct eigenvalues has length at most dim V. -/
def eigenvalue_family_card_le : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype I]
    (T : Module.End K V) (μ : I → K), Function.Injective μ →
      (∀ i, T.HasEigenvalue (μ i)) → Fintype.card I ≤ Module.finrank K V

/-- The full set of eigenvalues over K is finite and has size at most dim V. -/
def eigenvalues_finite_and_card_le : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Set.Finite {μ : K | T.HasEigenvalue μ} ∧
      Set.ncard {μ : K | T.HasEigenvalue μ} ≤ Module.finrank K V

end Specs.D05.M09.DistinctIndependence
