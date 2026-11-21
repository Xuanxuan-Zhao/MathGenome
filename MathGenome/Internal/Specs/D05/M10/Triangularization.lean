import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M08.Minpoly
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Matrix.Block

/-! Independent specification of K05.10.triangularization, paper.tex:1397–1405.
The basis is ordered by `Fin n`, and entries strictly below its diagonal vanish.
The existence of such a basis forces its length to be the dimension; no
positive-dimension, algebraic-closure or characteristic hypothesis is imposed.
Splitting is over the original scalar field. -/

noncomputable section
namespace Specs.D05.M10.Triangularization

/-- The paper's upper triangular matrix condition in an ordered basis. -/
def HasUpperTriangularBasis {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (T : Module.End K V) : Prop :=
  ∃ (n : ℕ) (b : Module.Basis (Fin n) K V),
    (LinearMap.toMatrix b b T).IsUpperTriangular

def triangular_implies_charpoly_splits : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    HasUpperTriangularBasis T → (Specs.D05.M08.Charpoly.charpoly_value T).Splits

def charpoly_splits_implies_minpoly_splits : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    (Specs.D05.M08.Charpoly.charpoly_value T).Splits →
      (Specs.D05.M08.Minpoly.minimalPolynomial_value K V T).Splits

def minpoly_splits_implies_triangular : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    (Specs.D05.M08.Minpoly.minimalPolynomial_value K V T).Splits →
      HasUpperTriangularBasis T

/-- The complete three-way equivalence, including the empty basis. -/
def triangularization : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    (HasUpperTriangularBasis T ↔ (Specs.D05.M08.Charpoly.charpoly_value T).Splits) ∧
    (HasUpperTriangularBasis T ↔
      (Specs.D05.M08.Minpoly.minimalPolynomial_value K V T).Splits)

end Specs.D05.M10.Triangularization
