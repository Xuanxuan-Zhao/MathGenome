import MathGenome.Internal.Specs.D05.M11.PrincipalMinors.Leading

/-! All-principal-minor criterion, paper.tex:1790–1800.
Principal subsets have their actual subtype indices; the empty subset is included.
The real part orders the real-valued Hermitian quadratic expression. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace Specs.D05.M11.PrincipalMinors.Semidefinite

/-- Every principal minor, including the empty minor, is nonnegative. -/
def AllPrincipalNonnegative {K : Type*} [RCLike K] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : Prop :=
  ∀ s : Finset n, 0 ≤ RCLike.re (A.submatrix (Subtype.val : s → n) Subtype.val).det

/-- Real positive diagonal perturbation. -/
def shift {K : Type*} [RCLike K] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (ε : ℝ) : Matrix n n K := A + (ε : K) • 1

def determinant_expansion : Prop :=
  ∀ {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (t : R),
    (A + t • 1).det = ∑ s : Finset n,
      t ^ (Fintype.card n - s.card) *
        (A.submatrix (Subtype.val : s → n) Subtype.val).det

/-- The real ordering used in the criterion is applied to real scalars. -/
def principal_determinants_real : Prop :=
  ∀ {K n : Type*} [RCLike K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K), A.IsHermitian → ∀ s : Finset n,
    RCLike.im (A.submatrix (Subtype.val : s → n) Subtype.val).det = 0

/-- First-slot-linear congruence, including strict positivity of the scaling
factor for an invertible change of coordinates. -/
def congruence_determinant_scaling : Prop :=
  ∀ {K n : Type*} [RCLike K] [Fintype n] [DecidableEq n]
    (H P : Matrix n n K),
    RCLike.re (Pᵀ * H * P.map star).det = ‖P.det‖ ^ 2 * RCLike.re H.det ∧
    (IsUnit P → 0 < ‖P.det‖ ^ 2)

def shifted_determinant_positive : Prop :=
  ∀ {K n : Type*} [RCLike K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K), AllPrincipalNonnegative A →
    ∀ ε : ℝ, 0 < ε → 0 < RCLike.re (shift A ε).det

def shifted_positive_definite : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    A.IsHermitian → AllPrincipalNonnegative A → ∀ ε : ℝ, 0 < ε →
    Definiteness.positiveDefinite_value (fun x y => star y ⬝ᵥ shift A ε *ᵥ x)

def limit_nonnegative : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    (∀ ε : ℝ, 0 < ε →
      Definiteness.positiveDefinite_value (fun x y => star y ⬝ᵥ shift A ε *ᵥ x)) →
    Definiteness.positiveSemidefinite_value (fun x y => star y ⬝ᵥ A *ᵥ x)

/-- Necessity for every restriction; the final theorem assumes no normal form. -/
def principal_restrictions_nonnegative : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian →
    Definiteness.positiveSemidefinite_value (fun x y => star y ⬝ᵥ A *ᵥ x) →
    AllPrincipalNonnegative A

def criterion : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian →
    (Definiteness.positiveSemidefinite_value (fun x y => star y ⬝ᵥ A *ᵥ x) ↔
      AllPrincipalNonnegative A)

def real_criterion : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm →
    ((∀ x, 0 ≤ x ⬝ᵥ A *ᵥ x) ↔
      ∀ s : Finset (Fin n), 0 ≤ (A.submatrix (Subtype.val : s → Fin n) Subtype.val).det)

def empty_minor : Prop :=
  ∀ {R n : Type*} [CommRing R] (A : Matrix n n R),
    (A.submatrix (Subtype.val : (∅ : Finset n) → n) Subtype.val).det = 1

/-- The source's literal matrix and negative vector. -/
def leading_minors_insufficient : Prop :=
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, -1]
  (∀ (k : ℕ) (h : k ≤ 2), 0 ≤ (Leading.leadingBlock A k h).det) ∧
    (![0, 1] : Fin 2 → ℝ) ⬝ᵥ A *ᵥ ![0, 1] = -1 ∧
    ¬ Definiteness.positiveSemidefinite_value (fun x y => y ⬝ᵥ A *ᵥ x)

/-- Determinants agree under the paper's transpose convention H = Aᵗ. -/
def transpose_criterion : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K),
    AllPrincipalNonnegative Hᵀ ↔ AllPrincipalNonnegative H

/-- Transfer the matrix criterion back to an actual first-slot-linear form. -/
def form_criterion : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (B : Hermitian.sesquilinearForm_value ℂ V),
    Hermitian.isHermitian_value B →
    (Definiteness.positiveSemidefinite_value (fun x y => B x y) ↔
      AllPrincipalNonnegative (Hermitian.formMatrix_value e B))
end Specs.D05.M11.PrincipalMinors.Semidefinite
