import MathGenome.Internal.Specs.D05.M05.DetDefinition

/-!
Independent statements for paper.tex:813–823, K05.05.det_product.
The determinant is the shared column-indexed Leibniz determinant. Both
identities hold over every commutative ring with identity, for all natural
matrix sizes, including zero. No field or invertibility hypothesis is used.
-/

namespace D05.Specs.DetProduct

/-- Determinant multiplicativity for square matrices of the same size. -/
def det_mul : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R),
    D05.M05.determinant (A * B) = D05.M05.determinant A * D05.M05.determinant B

/-- Transposition preserves the determinant. -/
def det_transpose : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R),
    D05.M05.determinant A.transpose = D05.M05.determinant A

end D05.Specs.DetProduct
