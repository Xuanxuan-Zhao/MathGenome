import MathGenome.Internal.Specs.D05.M10.Triangularization
import MathGenome.Internal.Specs.D05.M08.RestrictionMinpoly
import MathGenome.Internal.Specs.D05.M09.CommutantInvariance

/-! Independent statements for the common-eigenvector stage of
K05.10.simultaneous_triangular, paper.tex:1407–1413.
All eigenvalues and splitting statements use the original field. The family is
indexed by an arbitrary finite type, so repeated operators and the empty family
are allowed. Nontriviality is required only of the space in which a nonzero
vector is requested. -/

noncomputable section
namespace Specs.D05.M10.SimultaneousTriangular.CommonEigenvector

open Specs.D05.M06.Invariant (invariant_value)
open Specs.D05.M10.Triangularization (HasUpperTriangularBasis)

/-- Splitting passes to every invariant restriction, including the zero subspace. -/
def restriction_splits : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V) (T : Module.End K V)
    (hU : invariant_value K V U T),
    (minpoly K T).Splits → (minpoly K (T.restrict hU)).Splits

/-- One successive eigenspace step retains invariance under the entire family,
commutation of the restrictions, and splitting of every restricted minimal
polynomial. This applies again after any preceding restriction. -/
def eigenspace_step : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] (T : ι → Module.End K V),
    (Pairwise fun i j => Commute (T i) (T j)) →
    (∀ i, (minpoly K (T i)).Splits) → ∀ i : ι,
    ∃ (μ : K) (hE : ∀ j, invariant_value K V ((T i).eigenspace μ) (T j)),
      (T i).eigenspace μ ≠ ⊥ ∧
      (Pairwise fun j k => Commute ((T j).restrict (hE j))
        ((T k).restrict (hE k))) ∧
      (∀ j, (minpoly K ((T j).restrict (hE j))).Splits)

/-- Common nonzero eigenvector under the equivalent split-minimal-polynomial
hypothesis. No hypothesis on the number of distinct eigenvalues is made. -/
def common_eigenvector_of_splits : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] [Finite ι]
    (T : ι → Module.End K V),
    (Pairwise fun i j => Commute (T i) (T j)) →
    (∀ i, (minpoly K (T i)).Splits) →
    ∃ (v : V) (μ : ι → K), v ≠ 0 ∧ ∀ i, T i v = μ i • v

/-- The assigned conclusion with the original individual triangularizability
hypotheses. For an empty index type the eigenvalue function is empty. -/
def common_eigenvector : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] [Finite ι]
    (T : ι → Module.End K V),
    (Pairwise fun i j => Commute (T i) (T j)) →
    (∀ i, HasUpperTriangularBasis (T i)) →
    ∃ (v : V) (μ : ι → K), v ≠ 0 ∧ ∀ i, T i v = μ i • v

/-- The same conclusion inside any nonzero common invariant subspace, as used
at intermediate stages of the successive-restriction argument. -/
def common_eigenvector_in_subspace : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Finite ι] (T : ι → Module.End K V),
    (Pairwise fun i j => Commute (T i) (T j)) →
    (∀ i, HasUpperTriangularBasis (T i)) →
    ∀ (U : Submodule K V), U ≠ ⊥ →
    (∀ i, invariant_value K V U (T i)) →
    ∃ (v : V) (μ : ι → K), v ∈ U ∧ v ≠ 0 ∧ ∀ i, T i v = μ i • v

end Specs.D05.M10.SimultaneousTriangular.CommonEigenvector
