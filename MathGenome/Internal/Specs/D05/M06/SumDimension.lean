import MathGenome.Internal.Specs.D05.M02.Basis
import MathGenome.Internal.Specs.D05.M02.Dimension
import MathGenome.Internal.Specs.D05.M06.ExternalSum

/-!
Independent statements for K05.06.sum_dimension, paper.tex:989–990.
The concatenation is indexed by a dependent disjoint union, retaining each
occurrence of each summand's chosen basis. The basis assertions are valid even
without finite dimension. Dimension formulas concern finite families of
finite-dimensional summands; finite dimension of the ambient space is a
conclusion. Internal sums use the upstream unique-decomposition predicate and
the external sum is the canonical finitely supported space.
-/

namespace Specs.D05.M06.SumDimension

open scoped Classical in
/-- Inject each chosen component basis into the external sum. This is a basis,
with exactly the indicated vectors, rather than an abstract basis existence. -/
def external_basis : Prop :=
  ∀ {K ι : Type*} {M : ι → Type*} {κ : ι → Type*}
    [Field K] [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (b : ∀ i, Module.Basis (κ i) K (M i)),
    ∃ B : Module.Basis (Σ i, κ i) K (_root_.DirectSum ι M),
      ∀ (i : ι) (j : κ i), B ⟨i, j⟩ = _root_.DirectSum.lof K ι M i (b i j)

/-- Concatenate the chosen bases by their actual inclusions in the ambient
space. No ambient finite-dimensionality is assumed. -/
def internal_basis : Prop :=
  ∀ {K V ι : Type*} {κ : ι → Type*}
    [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V), Specs.D05.M06.DirectSum.UniqueDecomposition U →
    ∀ b : ∀ i, Module.Basis (κ i) K (U i),
      ∃ B : Module.Basis (Σ i, κ i) K V,
        ∀ (i : ι) (j : κ i), B ⟨i, j⟩ = (b i j : V)

/-- Finite-dimensional components and a finite family imply finite dimension
of the external sum. -/
def external_finiteDimensional : Prop :=
  ∀ {K ι : Type*} {M : ι → Type*}
    [Field K] [Fintype ι] [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, FiniteDimensional K (M i)],
    FiniteDimensional K (_root_.DirectSum ι M)

/-- The corresponding internal finiteness is derived from the decomposition. -/
def internal_finiteDimensional : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V) [∀ i, FiniteDimensional K (U i)],
    Specs.D05.M06.DirectSum.UniqueDecomposition U → FiniteDimensional K V

/-- Natural-number dimension of the external sum, including empty families. -/
def external_dimension : Prop :=
  ∀ {K ι : Type*} {M : ι → Type*}
    [Field K] [Fintype ι] [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, FiniteDimensional K (M i)],
    Module.finrank K (_root_.DirectSum ι M) = ∑ i, Module.finrank K (M i)

/-- Dimension of the ambient internal sum. Its finiteness is proved separately,
so it is not silently added to the hypotheses of the paper. -/
def internal_dimension : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V) [∀ i, FiniteDimensional K (U i)],
    Specs.D05.M06.DirectSum.UniqueDecomposition U →
      Module.finrank K V = ∑ i, Module.finrank K (U i)

/-- The empty external sum has dimension zero and the sum of dimensions is zero;
there is no component finiteness assumption to supply in this case. -/
def empty_external_dimension : Prop :=
  ∀ {K ι : Type*} {M : ι → Type*}
    [Field K] [Fintype ι] [IsEmpty ι]
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)],
    Module.finrank K (_root_.DirectSum ι M) = 0 ∧
      (∑ i, Module.finrank K (M i)) = 0

/-- For an empty internal decomposition the ambient dimension and the empty sum
of dimensions both vanish, without an ambient finiteness assumption. -/
def empty_internal_dimension : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [IsEmpty ι] (U : ι → Submodule K V),
    Specs.D05.M06.DirectSum.UniqueDecomposition U →
      Module.finrank K V = 0 ∧ (∑ i, Module.finrank K (U i)) = 0

end Specs.D05.M06.SumDimension
