import MathGenome.Internal.Specs.D05.M04.ChangeBasis
import MathGenome.Internal.Specs.D05.M03.RankNullity
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Independent statements for K05.04.equivalence, paper.tex:662–668.
Rows are codomain coordinates and columns are domain coordinates. All dimensions
may be zero. Rank normal form and classification require a field. -/

namespace Specs.D05.M04.Equivalence

universe u

/-- The rectangular matrix with an initial identity block of size `r`. -/
def rankNormalMatrix {R : Type*} [Zero R] [One R] (m n r : ℕ) :
    Matrix (Fin m) (Fin n) R :=
  fun i j => if i.val = j.val ∧ i.val < r then 1 else 0

/-- Independent invertible row and column changes. Over a commutative ring this
is the usual matrix equivalence; no division operation is built into it. -/
def Equivalent {R : Type*} [CommRing R] {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ (L : (Matrix (Fin m) (Fin m) R)ˣ)
    (P : (Matrix (Fin n) (Fin n) R)ˣ), B = (L : Matrix _ _ R) * A * (P : Matrix _ _ R)

/-- Every finite-dimensional linear map has the asserted matrix in finite
ordered bases, with the identity size equal to its actual image dimension. -/
def map_rank_normal_form : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V →ₗ[K] W),
    ∃ (b : Module.Basis (Fin (Module.finrank K V)) K V)
      (c : Module.Basis (Fin (Module.finrank K W)) K W),
      MatrixOfMap.matrixOfMap_value b c T =
        rankNormalMatrix (Module.finrank K W) (Module.finrank K V)
          (Module.finrank K (LinearMap.range T))

/-- The same form is obtainable by actual invertible matrix multipliers. -/
def matrix_rank_normal_form : Prop :=
  ∀ {K : Type*} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    Equivalent A (rankNormalMatrix m n A.rank)

/-- For a fixed rectangular shape rank is a complete invariant. -/
def equivalent_iff_rank : Prop :=
  ∀ {K : Type*} [Field K] {m n : ℕ} (A B : Matrix (Fin m) (Fin n) K),
    Equivalent A B ↔ A.rank = B.rank

end Specs.D05.M04.Equivalence
