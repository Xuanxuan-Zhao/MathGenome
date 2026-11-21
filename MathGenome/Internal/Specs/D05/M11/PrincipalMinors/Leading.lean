import MathGenome.Internal.Specs.D05.M11.Definiteness
import MathGenome.Internal.Specs.D05.M11.FormMatrix
import Mathlib.Analysis.RCLike.Basic

/-! Strict principal-minor criterion, paper.tex:1780–1800.
`RCLike` covers both real symmetric and complex Hermitian matrices. All orders
in the statements below are orders on real parts; Hermitian symmetry ensures
that the scalars being compared are real. No nonempty dimension is assumed. -/
noncomputable section
namespace Specs.D05.M11.PrincipalMinors.Leading
open Matrix

/-- The first k rows and columns, in their original order. -/
def leadingBlock {K : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (k : ℕ) (h : k ≤ n) : Matrix (Fin k) (Fin k) K :=
  A.submatrix (Fin.castLE h) (Fin.castLE h)

def LeadingPositive {K : Type*} [RCLike K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ (k : ℕ) (h : k ≤ n), 0 < k → 0 < RCLike.re (leadingBlock A k h).det

/-- The paper's matrix [a r*; r B], with a real pivot. -/
def bordered {K : Type*} [RCLike K] {n : ℕ} (a : ℝ) (r : Fin n → K)
    (B : Matrix (Fin n) (Fin n) K) : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) K :=
  fromBlocks (fun _ _ => (a : K)) (fun _ j => star (r j)) (fun i _ => r i) B

def schur {K : Type*} [RCLike K] {n : ℕ} (a : ℝ) (r : Fin n → K)
    (B : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  B - (a : K)⁻¹ • vecMulVec r (star r)

def strict_criterion : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    A.IsHermitian →
    (Definiteness.positiveDefinite_value (fun x y => star y ⬝ᵥ A *ᵥ x) ↔ LeadingPositive A)

/-- The completed-square identity is an equality in K, before taking real parts. -/
def completed_square : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (a : ℝ) (r : Fin n → K)
    (B : Matrix (Fin n) (Fin n) K), 0 < a → ∀ (z : K) (y : Fin n → K),
    star (Sum.elim (fun _ : Unit => z) y) ⬝ᵥ
      bordered a r B *ᵥ Sum.elim (fun _ : Unit => z) y =
    (a : K) * (star (z + (a : K)⁻¹ * (star r ⬝ᵥ y)) *
      (z + (a : K)⁻¹ * (star r ⬝ᵥ y))) + star y ⬝ᵥ schur a r B *ᵥ y

/-- The identical square written as the squared absolute value (the norm). -/
def completed_square_norm : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (a : ℝ) (r : Fin n → K)
    (B : Matrix (Fin n) (Fin n) K), 0 < a → ∀ (z : K) (y : Fin n → K),
    star (Sum.elim (fun _ : Unit => z) y) ⬝ᵥ
      bordered a r B *ᵥ Sum.elim (fun _ : Unit => z) y =
    (a : K) * (‖z + (a : K)⁻¹ * (star r ⬝ᵥ y)‖ : K)^2 +
      star y ⬝ᵥ schur a r B *ᵥ y

/-- The ordinary real symmetric specialization, with ordinary real inequalities. -/
def real_strict_criterion : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm →
    ((∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) ↔
      ∀ (k : ℕ) (h : k ≤ n), 0 < k → 0 < (leadingBlock A k h).det)

/-- The completed-square positivity reduction used in the source induction. -/
def schur_positive_definite : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (a : ℝ) (r : Fin n → K)
    (B : Matrix (Fin n) (Fin n) K), 0 < a → B.IsHermitian →
    (Definiteness.positiveDefinite_value (fun x y => star y ⬝ᵥ bordered a r B *ᵥ x) ↔
      Definiteness.positiveDefinite_value (fun x y => star y ⬝ᵥ schur a r B *ᵥ x))

/-- Every leading block containing the pivot has the stated Schur determinant.
The case k = 0 includes the one by one pivot block. -/
def leading_schur_determinant : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (a : ℝ) (r : Fin n → K)
    (B : Matrix (Fin n) (Fin n) K), 0 < a → ∀ (k : ℕ) (h : k ≤ n),
    ((bordered a r B).submatrix
      (Sum.map id (Fin.castLE h)) (Sum.map id (Fin.castLE h))).det =
      (a : K) * (leadingBlock (schur a r B) k h).det

def empty_positive_definite : Prop :=
  ∀ {K : Type*} [RCLike K] (A : Matrix (Fin 0) (Fin 0) K),
    Definiteness.positiveDefinite_value (fun x y => star y ⬝ᵥ A *ᵥ x) ∧ LeadingPositive A

/-- Transposition preserves every principal determinant, for an arbitrary finite
selection of indices, not only the leading selections. -/
def principal_transpose : Prop :=
  ∀ {K : Type*} [CommRing K] {n k : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (s : Fin k → Fin n), (Hᵀ.submatrix s s).det = (H.submatrix s s).det

/-- The coordinate criterion for an actual first-slot-linear Hermitian form. -/
def form_criterion : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Module.Basis (Fin n) K V) (B : Hermitian.sesquilinearForm_value K V),
    Hermitian.isHermitian_value B →
    (Definiteness.positiveDefinite_value (fun x y => B x y) ↔
      LeadingPositive (Hermitian.formMatrix_value e B))
end Specs.D05.M11.PrincipalMinors.Leading
