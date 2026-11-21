import MathGenome.Internal.Specs.D05.M03.BasisExtension
import MathGenome.Internal.Specs.D05.M07.Dual
import MathGenome.Internal.Specs.D05.M02.Dimension

/-!
Independent specifications for K05.07.dual_basis (paper.tex:1015–1021).

A finite basis is indexed by any `Fintype I`, including the empty type.
The functionals are algebraic linear maps over the same field, with ordinary
scalar multiplication and no topology or conjugation. `b.coord` is the existing
coordinate functional of the canonical basis. The diagonal/off-diagonal clauses
below express the Kronecker delta without requiring a chosen decidable equality.
-/

namespace Specs.D05.M07.DualBasis

/-- The Kronecker equations determine exactly one entire family of functionals. -/
def exists_unique_dual_family : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (b : Module.Basis I K V),
    ∃! φ : I → Module.Dual K V,
      (∀ i, φ i (b i) = 1) ∧ (∀ i j, i ≠ j → φ i (b j) = 0)

/-- The coordinate functionals form an actual basis of the algebraic dual. -/
def coordinate_family_basis : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (b : Module.Basis I K V),
    ∃ d : Module.Basis I K (Module.Dual K V), ∀ i, d i = b.coord i

/-- Coordinate functionals recover the unique coefficients of any vector. -/
def coordinate_apply : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (b : Module.Basis I K V) (i : I) (x : V), b.coord i x = b.repr x i

/-- In particular, applying the i-th functional to a prescribed expansion gives a_i. -/
def coordinate_of_expansion : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (b : Module.Basis I K V) (a : I → K) (x : V),
    x = ∑ j, a j • b j → ∀ i, b.coord i x = a i

/-- Every functional has the paper's explicit expansion in the dual basis. -/
def functional_expansion : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (b : Module.Basis I K V) (f : Module.Dual K V),
    f = ∑ i, f (b i) • b.coord i

/-- A zero linear combination of the coordinate functionals has zero coefficients. -/
def dual_relation_coefficients : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (b : Module.Basis I K V) (c : I → K),
    (∑ i, c i • b.coord i) = 0 → ∀ j, c j = 0

/-- The scalar evaluation formula, with no conjugation of either factor. -/
def evaluation_expansion : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (b : Module.Basis I K V) (f : Module.Dual K V) (x : V),
    f x = ∑ i, f (b i) * b.coord i x

/-- Finite-dimensional algebraic duals have the same dimension as the original space. -/
def dual_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    FiniteDimensional K (Module.Dual K V) ∧
      Module.finrank K (Module.Dual K V) = Module.finrank K V

/-- The zero space has zero dual, empty dual basis, and dual dimension zero. -/
def zero_space_dual : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    (∀ x : V, x = 0) →
      (∀ f : Module.Dual K V, f = 0) ∧
      Nonempty (Module.Basis (Fin 0) K (Module.Dual K V)) ∧
      Module.finrank K (Module.Dual K V) = 0

end Specs.D05.M07.DualBasis
