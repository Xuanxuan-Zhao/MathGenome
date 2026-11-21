import MathGenome.Internal.Specs.D05.M04.MatrixOfMap
import MathGenome.Internal.Specs.D05.M07.DualBasis
import MathGenome.Internal.Specs.D05.M07.DualMap
import Mathlib.LinearAlgebra.Dual.Basis

/-!
Independent specifications for K05.07.dual_matrix (paper.tex:1083–1087).

The algebraic dual is `Module.Dual K V`, and the dual map is ordinary
precomposition `T.dualMap`. The matrix construction is the already specified
`MatrixOfMap.matrixOfMap_value`. Ordered bases have indices `Fin n` and `Fin m`;
neither dimension is required to be positive. Their coordinate functionals are
the dual bases, as proved in K05.07.dual_basis. All coefficients are in the
original field, including over ℂ, with no conjugation or inner-product structure.
-/

namespace Specs.D05.M07.DualMatrix

open Matrix

/-- The paper's evaluation calculation for any prescribed column expansions. -/
def dual_evaluation_of_expansion : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (T : V →ₗ[K] W) (A : Matrix (Fin m) (Fin n) K),
    (∀ j, T (b j) = ∑ i, A i j • c i) →
      ∀ i j, T.dualMap (c.coord i) (b j) = c.coord i (T (b j)) ∧
        c.coord i (T (b j)) = A i j

/-- Each pulled-back codomain coordinate functional has the stated dual expansion. -/
def dual_basis_expansion : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (T : V →ₗ[K] W) (A : Matrix (Fin m) (Fin n) K),
    (∀ j, T (b j) = ∑ i, A i j • c i) →
      ∀ i, T.dualMap (c.coord i) = ∑ j, A i j • b.coord j

/-- Row j, column i of the dual matrix is row i, column j of the original matrix. -/
def dual_matrix_entry : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (T : V →ₗ[K] W) (i : Fin m) (j : Fin n),
    Specs.D05.M04.MatrixOfMap.matrixOfMap_value c.dualBasis b.dualBasis
        T.dualMap j i =
      Specs.D05.M04.MatrixOfMap.matrixOfMap_value b c T i j

/-- The actual coordinate matrix of the algebraic dual is the ordinary transpose. -/
def matrix_transpose : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (T : V →ₗ[K] W),
    Specs.D05.M04.MatrixOfMap.matrixOfMap_value c.dualBasis b.dualBasis
        T.dualMap =
      (Specs.D05.M04.MatrixOfMap.matrixOfMap_value b c T)ᵀ

/-- In particular, the given coefficients A in the paper give dual matrix Aᵀ. -/
def matrix_transpose_of_expansion : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (T : V →ₗ[K] W) (A : Matrix (Fin m) (Fin n) K),
    (∀ j, T (b j) = ∑ i, A i j • c i) →
      Specs.D05.M04.MatrixOfMap.matrixOfMap_value c.dualBasis b.dualBasis
        T.dualMap = Aᵀ

end Specs.D05.M07.DualMatrix
