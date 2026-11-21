import MathGenome.Internal.Specs.D05.M05.DetDefinition
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fintype.EquivFin

/-!
Independent statement types for paper.tex:891–894, K05.05.triangular_block.
Every determinant is the shared column Leibniz determinant. Scalars range over
all commutative rings with identity; neither a field nor nontriviality is needed.

In the finite-block statements `b` assigns each coordinate to its block. The
same partition is used for rows and columns, so diagonal blocks are square;
their sizes may differ. Empty fibers are allowed, including unused block labels.
`equivFin` enumerates each fiber only to use the shared Fin-indexed determinant.
The two-block statements use the ordered concatenation `finSumFinEquiv`.
-/

noncomputable section

open scoped BigOperators

namespace D05.Specs.TriangularBlock

open D05.M05

/-- Upper triangular means that every entry strictly below the diagonal is zero. -/
def upper_triangular : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    (∀ i j, j < i → A i j = 0) → determinant A = ∏ j, A j j

/-- Lower triangular means that every entry strictly above the diagonal is zero. -/
def lower_triangular : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    (∀ i j, i < j → A i j = 0) → determinant A = ∏ j, A j j

/-- The off-diagonal block has the full rectangular shape r by s. -/
def upper_block : Prop :=
  ∀ {R : Type*} [CommRing R] {r s : ℕ}
    (B : Matrix (Fin r) (Fin r) R) (C : Matrix (Fin r) (Fin s) R)
    (D : Matrix (Fin s) (Fin s) R),
    determinant ((Matrix.fromBlocks B C 0 D).reindex finSumFinEquiv finSumFinEquiv) =
      determinant B * determinant D

/-- The transposed block-triangular formula, allowing arbitrary rectangular C. -/
def lower_block : Prop :=
  ∀ {R : Type*} [CommRing R] {r s : ℕ}
    (B : Matrix (Fin r) (Fin r) R) (C : Matrix (Fin s) (Fin r) R)
    (D : Matrix (Fin s) (Fin s) R),
    determinant ((Matrix.fromBlocks B 0 C D).reindex finSumFinEquiv finSumFinEquiv) =
      determinant B * determinant D

/-- Any finite number of square diagonal blocks, with all blocks below them zero.
There is no surjectivity or nonempty-block assumption on b. -/
def finite_upper_blocks : Prop :=
  ∀ {R : Type*} [CommRing R] {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → Fin k),
    (∀ i j, b j < b i → A i j = 0) →
    determinant A = ∏ a : Fin k,
      determinant ((A.toSquareBlock b a).reindex
        (Fintype.equivFin {i // b i = a}) (Fintype.equivFin {i // b i = a}))

/-- The analogous finite lower-block formula. -/
def finite_lower_blocks : Prop :=
  ∀ {R : Type*} [CommRing R] {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → Fin k),
    (∀ i j, b i < b j → A i j = 0) →
    determinant A = ∏ a : Fin k,
      determinant ((A.toSquareBlock b a).reindex
        (Fintype.equivFin {i // b i = a}) (Fintype.equivFin {i // b i = a}))

/-- A zero-sized diagonal block contributes one to the block product. -/
def empty_block : Prop :=
  ∀ {R : Type*} [CommRing R] {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → Fin k) (a : Fin k),
    (∀ i, b i ≠ a) →
    determinant ((A.toSquareBlock b a).reindex
      (Fintype.equivFin {i // b i = a}) (Fintype.equivFin {i // b i = a})) = 1

/-- With no coordinates both the determinant and the diagonal product are one. -/
def empty_triangular : Prop :=
  ∀ {R : Type*} [CommRing R] (A : Matrix (Fin 0) (Fin 0) R),
    determinant A = 1 ∧ (∏ j : Fin 0, A j j) = 1

end D05.Specs.TriangularBlock
