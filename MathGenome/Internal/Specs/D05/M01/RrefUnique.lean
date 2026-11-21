import MathGenome.Internal.Specs.D05.M01.Elimination
import MathGenome.Internal.Specs.D05.M01.RrefUnique.RowSpace

/-!
Independent statements for paper.tex:744–752, K05.01.rref_unique.
Row equivalence means reachability by a finite list of precisely the permitted
operations. Rows and columns are ordered finite indices; either size may be zero.
The choice below selects a matrix by a predicate, without assuming that predicate
has a witness. Existence, uniqueness, and the choice's specification are separate
proof obligations. This module imports no candidate implementation.
-/
namespace D05.M01.RrefUniqueSpec

universe u

def RowEquivalent_type := ∀ {K : Type u} [Field K] {m n : ℕ},
  Matrix (Fin m) (Fin n) K → Matrix (Fin m) (Fin n) K → Prop

/-- A chronological finite sequence of elementary row operations. -/
def RowEquivalent_value : RowEquivalent_type := fun A B =>
  ∃ ops : List (RowOps.RowOperation _ _), Elimination.applyOps ops A = B

def reducedForm_type := ∀ {K : Type u} [Field K] {m n : ℕ},
  Matrix (Fin m) (Fin n) K → Matrix (Fin m) (Fin n) K

noncomputable def reducedForm_value : reducedForm_type := fun A =>
  Classical.epsilon (fun R => R.IsReducedRowEchelon ∧ RowEquivalent_value A R)

def rowEquivalent_refl : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    RowEquivalent_value A A

def rowEquivalent_symm : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A B : Matrix (Fin m) (Fin n) K),
    RowEquivalent_value A B → RowEquivalent_value B A

def rowEquivalent_trans : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) K),
    RowEquivalent_value A B → RowEquivalent_value B C → RowEquivalent_value A C

def rowEquivalent_rowSpace : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A B : Matrix (Fin m) (Fin n) K),
    RowEquivalent_value A B →
      Specs.D05.M01.RrefUnique.RowSpace.rowSpace_value A =
        Specs.D05.M01.RrefUnique.RowSpace.rowSpace_value B

def reduced_eq_of_rowEquivalent : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R S : Matrix (Fin m) (Fin n) K),
    R.IsReducedRowEchelon → S.IsReducedRowEchelon → RowEquivalent_value R S → R = S

/-- Exactly one reduced matrix in the entire elementary row-equivalence class. -/
def exists_unique_reduced : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    ∃! R, R.IsReducedRowEchelon ∧ RowEquivalent_value A R

def reducedForm_spec : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    (reducedForm_value A).IsReducedRowEchelon ∧ RowEquivalent_value A (reducedForm_value A)

/-- Any two reduced forms of the indicated matrices satisfy the classification. -/
def rowEquivalent_iff_reduced_eq : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A B R S : Matrix (Fin m) (Fin n) K),
    R.IsReducedRowEchelon → S.IsReducedRowEchelon →
    RowEquivalent_value A R → RowEquivalent_value B S →
    (RowEquivalent_value A B ↔ R = S)

def rowEquivalent_iff_reducedForm_eq : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A B : Matrix (Fin m) (Fin n) K),
    RowEquivalent_value A B ↔ reducedForm_value A = reducedForm_value B

end D05.M01.RrefUniqueSpec
