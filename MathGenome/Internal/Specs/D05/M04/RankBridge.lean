import Mathlib.LinearAlgebra.Matrix.Rank
import MathGenome.Internal.Specs.D05.M03.Image
import MathGenome.Internal.Specs.D05.M03.CompositionRank
import MathGenome.Internal.Specs.D05.M04.MatrixOfMap

/-!
Independent statements for K05.04.rank_bridge, paper.tex:673–679.
Columns and rows are the actual entry functions `A.col` and `A.row`.
Their ranks are dimensions of their spans, not assumed certificates.
`Fin n` and `Fin m` retain the ordered coordinate convention and permit zero
and rectangular sizes. The image and finite-sum assertions hold over any
commutative ring. Rank comparisons are over a field, as in the manuscript.
-/

namespace Specs.D05.M04.RankBridge

open Matrix

/-- Matrix action is the linear combination of the columns with input coefficients. -/
def mulVec_eq_column_sum : Prop :=
  ∀ {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (x : Fin n → R),
    A *ᵥ x = ∑ j, x j • A.col j

/-- Equality of subspaces, proving both inclusions of the image assertion. -/
def image_eq_column_span : Prop :=
  ∀ {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R),
    LinearMap.range (MatrixOfMap.coordinateLinearMap_value A) =
      Submodule.span R (Set.range A.col)

/-- A column-span vector has an actual preimage under matrix multiplication. -/
def mem_column_span_iff : Prop :=
  ∀ {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (y : Fin m → R),
    y ∈ Submodule.span R (Set.range A.col) ↔ ∃ x : Fin n → R, A *ᵥ x = y

/-- Column rank agrees with the accepted finite-image rank of the coordinate map. -/
def column_rank_eq_map_rank : Prop :=
  ∀ {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K),
    Module.finrank K (Submodule.span K (Set.range A.col)) =
      Specs.D05.M03.Image.rank_value K (Fin n → K) (Fin m → K)
        (MatrixOfMap.coordinateLinearMap_value A)

/-- The library's matrix rank is precisely column-space dimension. -/
def rank_eq_column_rank : Prop :=
  ∀ {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K),
    A.rank = Module.finrank K (Submodule.span K (Set.range A.col))

/-- Equality of the dimensions of the row and column spaces over any field. -/
def row_rank_eq_column_rank : Prop :=
  ∀ {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K),
    Module.finrank K (Submodule.span K (Set.range A.row)) =
      Module.finrank K (Submodule.span K (Set.range A.col))

/-- Transposition preserves rank without a square or positive-size hypothesis. -/
def rank_transpose : Prop :=
  ∀ {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K), A.transpose.rank = A.rank

/-- Rank of a matrix in the chosen ordered bases equals rank of the original map. -/
def matrixOfMap_rank : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (T : V →ₗ[K] W),
    (MatrixOfMap.matrixOfMap_value b c T).rank = Module.finrank K (LinearMap.range T)

/-- The inverse matrix-to-map correspondence has the same rank. -/
def mapOfMatrix_rank : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (A : Matrix (Fin m) (Fin n) K),
    A.rank = Module.finrank K (LinearMap.range (MatrixOfMap.mapOfMatrix_value b c A))

end Specs.D05.M04.RankBridge
