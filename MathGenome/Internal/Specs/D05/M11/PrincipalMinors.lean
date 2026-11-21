import MathGenome.Internal.Specs.D05.M11.PrincipalMinors.Semidefinite

/-!
Independent interface for K05.11.principal_minors, paper.tex:1780–1800.
The quadratic expression is x*Ax. Complex inequalities mean inequalities on
its real part; Hermitian symmetry ensures that this expression is real.
The canonical leading blocks, principal subsets and sign predicates are reused
from the prerequisite Specs. All natural sizes, including zero, are allowed.
-/
noncomputable section
open Matrix

namespace Specs.D05.M11.PrincipalMinors

/-- Both tests for a complex Hermitian matrix, with no invertibility assumption. -/
def complex_criteria : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian →
    (Definiteness.positiveDefinite_value (fun x y => star y ⬝ᵥ A *ᵥ x) ↔
      Leading.LeadingPositive A) ∧
    (Definiteness.positiveSemidefinite_value (fun x y => star y ⬝ᵥ A *ᵥ x) ↔
      Semidefinite.AllPrincipalNonnegative A)

/-- The real symmetric version uses ordinary real inequalities throughout. -/
def real_criteria : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm →
    ((∀ x, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) ↔
      ∀ (k : ℕ) (h : k ≤ n), 0 < k → 0 < (Leading.leadingBlock A k h).det) ∧
    ((∀ x, 0 ≤ x ⬝ᵥ A *ᵥ x) ↔
      ∀ s : Finset (Fin n),
        0 ≤ (A.submatrix (Subtype.val : s → Fin n) Subtype.val).det)

/-- Strict positivity in the paper's first-slot-linear form coordinates. -/
def form_strict_criterion : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Module.Basis (Fin n) K V) (B : Hermitian.sesquilinearForm_value K V),
    Hermitian.isHermitian_value B →
    (Definiteness.positiveDefinite_value (fun x y => B x y) ↔
      Leading.LeadingPositive (Hermitian.formMatrix_value e B))

def form_complex_semidefinite_criterion : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (B : Hermitian.sesquilinearForm_value ℂ V),
    Hermitian.isHermitian_value B →
    (Definiteness.positiveSemidefinite_value (fun x y => B x y) ↔
      Semidefinite.AllPrincipalNonnegative (Hermitian.formMatrix_value e B))

/-- Conjugation is trivial over the real field, giving the real form version. -/
def form_real_semidefinite_criterion : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : Module.Basis (Fin n) ℝ V) (B : Hermitian.sesquilinearForm_value ℝ V),
    Hermitian.isHermitian_value B →
    (Definiteness.positiveSemidefinite_value (fun x y => B x y) ↔
      Semidefinite.AllPrincipalNonnegative (Hermitian.formMatrix_value e B))

/-- H = Aᵗ has identical principal determinants and identical minor conditions. -/
def transpose_criteria : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K),
    (∀ {k : ℕ} (s : Fin k → Fin n),
      (Hᵀ.submatrix s s).det = (H.submatrix s s).det) ∧
    (Leading.LeadingPositive Hᵀ ↔ Leading.LeadingPositive H) ∧
    (Semidefinite.AllPrincipalNonnegative Hᵀ ↔
      Semidefinite.AllPrincipalNonnegative H)

/-- The literal symmetric counterexample and its negative coordinate vector. -/
def leading_minors_insufficient : Prop :=
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, -1]
  A.IsSymm ∧
    (∀ (k : ℕ) (h : k ≤ 2), 0 ≤ (Leading.leadingBlock A k h).det) ∧
    (![0, 1] : Fin 2 → ℝ) ⬝ᵥ A *ᵥ ![0, 1] = -1 ∧
    ¬ Definiteness.positiveSemidefinite_value (fun x y => y ⬝ᵥ A *ᵥ x)

/-- The empty size is retained on both sides of both tests. -/
def empty_case : Prop :=
  ∀ {K : Type*} [RCLike K] (A : Matrix (Fin 0) (Fin 0) K),
    Definiteness.positiveDefinite_value (fun x y => star y ⬝ᵥ A *ᵥ x) ∧
    Leading.LeadingPositive A ∧
    Definiteness.positiveSemidefinite_value (fun x y => star y ⬝ᵥ A *ᵥ x) ∧
    Semidefinite.AllPrincipalNonnegative A

/-- The empty principal subset contributes determinant one. -/
def empty_minor : Prop :=
  ∀ {R n : Type*} [CommRing R] (A : Matrix n n R),
    (A.submatrix (Subtype.val : (∅ : Finset n) → n) Subtype.val).det = 1

end Specs.D05.M11.PrincipalMinors
