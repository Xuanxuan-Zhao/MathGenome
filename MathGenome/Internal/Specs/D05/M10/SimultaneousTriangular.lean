import MathGenome.Internal.Specs.D05.M10.Triangularization

/-! Independent statements for K05.10.simultaneous_triangular,
paper.tex:1407–1417. The field is arbitrary and fixed throughout. Individual
triangularizing bases may differ; the conclusion supplies a single ordered basis.
The family may be empty or infinite, and the ambient space may have dimension zero.
-/

noncomputable section
namespace Specs.D05.M10.SimultaneousTriangular

open Specs.D05.M10.Triangularization (HasUpperTriangularBasis)

/-- The dimension-induction stage for an arbitrary finite indexed family. -/
def finite_simultaneous_triangular : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Finite ι] (T : ι → Module.End K V),
    (Pairwise fun i j => Commute (T i) (T j)) →
    (∀ i, HasUpperTriangularBasis (T i)) →
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K V),
      ∀ i, (LinearMap.toMatrix b b (T i)).IsUpperTriangular

/-- The paper's full conclusion for a possibly infinite set of operators. -/
def simultaneous_triangular : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (F : Set (Module.End K V)),
    F.Pairwise Commute →
    (∀ T ∈ F, HasUpperTriangularBasis T) →
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K V),
      ∀ T ∈ F, (LinearMap.toMatrix b b T).IsUpperTriangular

/-- The equivalent indexed formulation retains repeated occurrences and has
no finiteness assumption on its index type. -/
def simultaneous_triangular_indexed : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : ι → Module.End K V),
    (Pairwise fun i j => Commute (T i) (T j)) →
    (∀ i, HasUpperTriangularBasis (T i)) →
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K V),
      ∀ i, (LinearMap.toMatrix b b (T i)).IsUpperTriangular

end Specs.D05.M10.SimultaneousTriangular
