import MathGenome.Internal.Specs.D05.M05.DetProduct

/-!
Independent statements for paper.tex:825–826, K05.05.det_row_rules.
All operations refer to the shared column Leibniz determinant. The six
operation rules hold over every commutative ring with identity. Only the
two linear-dependence assertions require a field. Sizes include zero;
an interchange or addition from another column/row requires distinct indices.
-/

namespace D05.Specs.DetRowRules

/-- Interchanging the two distinct columns `j` and `k` negates determinant.
The first submatrix map acts on rows and the second acts on columns. -/
def column_swap : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (j k : Fin n), j ≠ k →
    D05.M05.determinant (A.submatrix id (Equiv.swap j k)) =
      -D05.M05.determinant A

/-- Scaling the selected column allows every scalar, including zero. -/
def column_scale : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (j : Fin n) (a : R),
    D05.M05.determinant (A.updateCol j (fun i => a * A i j)) =
      a * D05.M05.determinant A

/-- Add `a` times column `k` to the distinct column `j`. -/
def column_add_multiple : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (j k : Fin n), j ≠ k → ∀ a : R,
    D05.M05.determinant (A.updateCol j (fun i => A i j + a * A i k)) =
      D05.M05.determinant A

/-- Interchanging two distinct rows negates determinant. -/
def row_swap : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (i k : Fin n), i ≠ k →
    D05.M05.determinant (A.submatrix (Equiv.swap i k) id) =
      -D05.M05.determinant A

/-- Scaling one row scales determinant by the same arbitrary scalar. -/
def row_scale : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (i : Fin n) (a : R),
    D05.M05.determinant (A.updateRow i (fun j => a * A i j)) =
      a * D05.M05.determinant A

/-- Add `a` times row `k` to the distinct row `i`. -/
def row_add_multiple : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (i k : Fin n), i ≠ k → ∀ a : R,
    D05.M05.determinant (A.updateRow i (fun j => A i j + a * A k j)) =
      D05.M05.determinant A

/-- A dependent indexed family of columns over a field has determinant zero. -/
def dependent_columns_zero : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    ¬ LinearIndependent K (fun j i => A i j) → D05.M05.determinant A = 0

/-- A dependent indexed family of rows over a field has determinant zero. -/
def dependent_rows_zero : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    ¬ LinearIndependent K (fun i j => A i j) → D05.M05.determinant A = 0

end D05.Specs.DetRowRules
