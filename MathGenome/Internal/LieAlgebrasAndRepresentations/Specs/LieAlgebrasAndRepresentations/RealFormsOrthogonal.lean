import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.OrthogonalCompactGeometry
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts
import Mathlib.Tactic.NoncommRing

/-! Matrix models for the orthogonal row of LA-J07, source lines 4970–4972
and 5030–5055. The signed form uses Mathlib's indefinite orthogonal algebra. -/

noncomputable section

open scoped TensorProduct
open Matrix LieAlgebra LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature

namespace LieAlgebrasAndRepresentations.RealFormsOrthogonal

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev so (ι : Type*) [Fintype ι] [DecidableEq ι] := Orthogonal.so ι ℂ

abbrev soSignature (p q : ℕ) :=
  Orthogonal.so' (Fin p) (Fin q) ℝ

abbrev complexMatrix := @Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts.complexMatrix
abbrev conjMatrix := @Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts.conjMatrix
abbrev IsOrthogonal {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :=
  Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts.IsOrthogonal A
abbrev coefficientConjugation := @OrthogonalCompactGeometry.coefficientConjugation

open Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts
  (complexMatrix_transpose)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem conjMatrix_complexMatrix (A : Matrix ι ι ℝ) :
    conjMatrix (complexMatrix A) = complexMatrix A := by
  ext i j
  simp

theorem orthogonal_right {A : Matrix ι ι ℝ} (h : IsOrthogonal A) : A * Aᵀ = 1 :=
  mul_eq_one_comm.mp h

theorem complex_orthogonal_left {A : Matrix ι ι ℝ} (h : IsOrthogonal A) :
    (complexMatrix A)ᵀ * complexMatrix A = 1 :=
  Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts.complex_orthogonal h

theorem complex_orthogonal_right {A : Matrix ι ι ℝ} (h : IsOrthogonal A) :
    complexMatrix A * (complexMatrix A)ᵀ = 1 :=
  mul_eq_one_comm.mp (complex_orthogonal_left h)

/-- Conjugation by a real orthogonal matrix on the complex skew-symmetric algebra. -/
abbrev orthogonalAction (A : Matrix ι ι ℝ) (h : IsOrthogonal A) : so ι ≃ₗ⁅ℂ⁆ so ι :=
  Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts.orthogonalLieEquiv
    (complexMatrix A) (complex_orthogonal_left h)

@[simp] theorem orthogonalAction_val {A : Matrix ι ι ℝ} (h : IsOrthogonal A) (X : so ι) :
    (orthogonalAction A h X).val = complexMatrix A * X.val * (complexMatrix A)ᵀ := rfl

theorem orthogonalAction_commutes {A : Matrix ι ι ℝ} (h : IsOrthogonal A) :
    Intertwines (coefficientConjugation ι) (coefficientConjugation ι) (orthogonalAction A h) := by
  intro X
  apply Subtype.ext
  change conjMatrix (complexMatrix A * X.val * (complexMatrix A)ᵀ) =
    complexMatrix A * conjMatrix X.val * (complexMatrix A)ᵀ
  have hm : ∀ B C : Matrix ι ι ℂ, conjMatrix (B * C) = conjMatrix B * conjMatrix C :=
    map_mul (Complex.conjAe.toRingEquiv.mapMatrix)
  rw [hm, hm, ← complexMatrix_transpose, conjMatrix_complexMatrix,
    conjMatrix_complexMatrix]

theorem orthogonalAction_involutive {A : Matrix ι ι ℝ} (h : IsOrthogonal A)
    (hs : A * A = 1 ∨ A * A = -1) : Function.Involutive (orthogonalAction A h) := by
  intro X
  apply Subtype.ext
  let B := complexMatrix A
  have hh : B * B = 1 ∨ B * B = -1 := by
    rcases hs with hs | hs
    · left
      exact ((map_mul Complex.ofRealHom.mapMatrix A A).symm.trans
        (congrArg complexMatrix hs)).trans (map_one Complex.ofRealHom.mapMatrix)
    · right
      exact ((map_mul Complex.ofRealHom.mapMatrix A A).symm.trans
        (congrArg complexMatrix hs)).trans (by
          exact (map_neg Complex.ofRealHom.mapMatrix 1).trans
            (congrArg Neg.neg (map_one Complex.ofRealHom.mapMatrix)))
  change B * (B * X.val * Bᵀ) * Bᵀ = X.val
  calc
    _ = (B * B) * X.val * (B * B)ᵀ := by rw [transpose_mul]; noncomm_ring
    _ = _ := by rcases hh with he | he <;> simp [he]

/-- Entrywise conjugation followed by the orthogonal matrix action. -/
def matrixConjugation (A : Matrix ι ι ℝ) (h : IsOrthogonal A)
    (hs : A * A = 1 ∨ A * A = -1) : Conjugation (so ι) :=
  involutionConjugation (coefficientConjugation ι) (orthogonalAction A h)
    (orthogonalAction_commutes h) (orthogonalAction_involutive h hs)

/-- The signature matrix with p positive and q negative entries. -/
abbrev signatureMatrix (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  Orthogonal.indefiniteDiagonal (Fin p) (Fin q) ℝ

theorem signature_square (p q : ℕ) : signatureMatrix p q * signatureMatrix p q = 1 := by
  unfold signatureMatrix Orthogonal.indefiniteDiagonal
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    cases i <;> simp
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem signature_orthogonal (p q : ℕ) : IsOrthogonal (signatureMatrix p q) := by
  change (Matrix.diagonal _)ᵀ * signatureMatrix p q = 1
  rw [Matrix.diagonal_transpose]
  exact signature_square p q

def signatureConjugation (p q : ℕ) : Conjugation (so (Fin p ⊕ Fin q)) :=
  matrixConjugation (signatureMatrix p q) (signature_orthogonal p q) (Or.inl (signature_square p q))

/-- The standard orthogonal complex structure on two copies of real n-space. -/
abbrev quaternionicMatrix (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  OrthogonalCompactGeometry.sourceJ n ℝ

theorem quaternionic_square (n : ℕ) :
    quaternionicMatrix n * quaternionicMatrix n = -1 := by
  unfold quaternionicMatrix
  rw [neg_mul_neg, Matrix.J_squared]

theorem quaternionic_orthogonal (n : ℕ) : IsOrthogonal (quaternionicMatrix n) := by
  change (-Matrix.J (Fin n) ℝ)ᵀ * (-Matrix.J (Fin n) ℝ) = 1
  rw [Matrix.transpose_neg, Matrix.J_transpose, neg_neg, mul_neg, Matrix.J_squared, neg_neg]

def quaternionicConjugation (n : ℕ) : Conjugation (so (Fin n ⊕ Fin n)) :=
  matrixConjugation (quaternionicMatrix n) (quaternionic_orthogonal n)
    (Or.inr (quaternionic_square n))

/-- The real algebra so*(2n) in the skew-symmetric complex model. -/
abbrev soStar (n : ℕ) := (quaternionicConjugation n).fixed

@[simp] theorem matrixConjugation_val (A : Matrix ι ι ℝ) (h : IsOrthogonal A)
    (hs : A * A = 1 ∨ A * A = -1) (X : so ι) :
    ((matrixConjugation A h hs).map X).val =
      complexMatrix A * conjMatrix X.val * (complexMatrix A)ᵀ := rfl

/-- Matrix sizes for which the complex orthogonal Lie algebra is simple. -/
def IsSimpleSize (N : ℕ) : Prop := N = 3 ∨ 5 ≤ N

def matrix_real_form_type : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (h : IsOrthogonal A)
    (hs : A * A = 1 ∨ A * A = -1), IsRealForm (matrixConjugation A h hs).fixed

def matrix_fixed_iff_type : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (h : IsOrthogonal A)
    (hs : A * A = 1 ∨ A * A = -1) (X : so ι),
    X ∈ (matrixConjugation A h hs).fixed ↔
      complexMatrix A * conjMatrix X.val = X.val * complexMatrix A

def orthogonal_involution_iff_type : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι], 2 < Fintype.card ι →
    ∀ (A : Matrix ι ι ℝ) (h : IsOrthogonal A),
      Function.Involutive (orthogonalAction A h) ↔ (A * A = 1 ∨ A * A = -1)

def signature_model_type : Prop :=
  ∀ p q : ℕ, Nonempty (soSignature p q ≃ₗ⁅ℝ⁆ (signatureConjugation p q).fixed)

def quaternionic_model_type : Prop :=
  ∀ (n : ℕ) (X : so (Fin n ⊕ Fin n)), X ∈ soStar n ↔
    OrthogonalCompactGeometry.sourceJ n ℂ * conjMatrix X.val =
      X.val * OrthogonalCompactGeometry.sourceJ n ℂ

def signature_compact_type : Prop :=
  ∀ p q : ℕ,
    Nonempty (complexFixed (orthogonalAction (signatureMatrix p q) (signature_orthogonal p q)) ≃ₗ⁅ℂ⁆
      so (Fin p) × so (Fin q))

def quaternionic_compact_type : Prop :=
  ∀ n : ℕ,
    Nonempty (complexFixed (orthogonalAction (quaternionicMatrix n) (quaternionic_orthogonal n))
      ≃ₗ⁅ℂ⁆ Matrix (Fin n) (Fin n) ℂ)

def coefficient_compact_type : Prop :=
  ∀ N : ℕ, IsSimpleSize N → IsCompact (coefficientConjugation (Fin N))

def compact_matrix_reduction_type : Prop :=
  ∀ N : ℕ, IsSimpleSize N → ∀ θ : so (Fin N) ≃ₗ⁅ℂ⁆ so (Fin N),
    Intertwines (coefficientConjugation (Fin N)) (coefficientConjugation (Fin N)) θ →
    Function.Involutive θ →
    ∃ (A : Matrix (Fin N) (Fin N) ℝ) (h : IsOrthogonal A),
      (A * A = 1 ∨ A * A = -1) ∧
      ∃ v : so (Fin N) ≃ₗ⁅ℂ⁆ so (Fin N),
        Intertwines (coefficientConjugation (Fin N)) (coefficientConjugation (Fin N)) v ∧
        ∀ X, v (θ X) = orthogonalAction A h (v X)

def matrix_normal_forms_type : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), IsOrthogonal A →
    (A * A = 1 →
      ∃ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ ι) (Q : Matrix ι ι ℝ),
        IsOrthogonal Q ∧ Qᵀ * A * Q = Matrix.reindex e e (signatureMatrix p q)) ∧
    (A * A = -1 →
      A.det = 1 ∧
      ∃ (n : ℕ) (e : Fin n ⊕ Fin n ≃ ι) (Q : Matrix ι ι ℝ),
        IsOrthogonal Q ∧ Qᵀ * A * Q = Matrix.reindex e e (quaternionicMatrix n))

def model_existence_type : Prop :=
  (∀ p q : ℕ, ∃ S : LieSubalgebra ℝ (so (Fin (p + q))),
      IsRealForm S ∧ Nonempty (soSignature p q ≃ₗ⁅ℝ⁆ S)) ∧
  (∀ n : ℕ, ∃ S : LieSubalgebra ℝ (so (Fin (n + n))),
      IsRealForm S ∧ Nonempty (soStar n ≃ₗ⁅ℝ⁆ S))

def exhaustion_type : Prop :=
  ∀ N : ℕ, IsSimpleSize N → ∀ S : LieSubalgebra ℝ (so (Fin N)), IsRealForm S →
    (∃ p q : ℕ, p + q = N ∧ Nonempty (S ≃ₗ⁅ℝ⁆ soSignature p q)) ∨
    (∃ n : ℕ, n + n = N ∧ Nonempty (S ≃ₗ⁅ℝ⁆ soStar n))

def signature_isomorphism_type : Prop :=
  ∀ p q r s : ℕ, p + q = r + s → IsSimpleSize (p + q) →
    (Nonempty (soSignature p q ≃ₗ⁅ℝ⁆ soSignature r s) ↔
      (p = r ∧ q = s) ∨ (p = s ∧ q = r))

/-- The converse at n = 4 is part of the low-rank comparisons. -/
def possible_quaternionic_repetition_type : Prop :=
  ∀ p q n : ℕ, p + q = n + n → IsSimpleSize (p + q) →
    Nonempty (soSignature p q ≃ₗ⁅ℝ⁆ soStar n) →
    n = 4 ∧ ((p = 6 ∧ q = 2) ∨ (p = 2 ∧ q = 6))

def signature_swap_type : Prop :=
  ∀ p q : ℕ, Nonempty (soSignature p q ≃ₗ⁅ℝ⁆ soSignature q p)

def compact_signature_type : Prop :=
  ∀ p : ℕ, Nonempty (soSignature p 0 ≃ₗ⁅ℝ⁆ Orthogonal.so (Fin p) ℝ)

def compact_signature_killing_type : Prop :=
  ∀ p : ℕ, IsSimpleSize p → ∀ X : soSignature p 0, X ≠ 0 →
    _root_.killingForm ℝ (soSignature p 0) X X < 0

/-- Relative compactness of the adjoint action, expressed by an invariant positive
definite scalar product on the ambient real Lie algebra. -/
def IsCompactlyEmbedded {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (K : LieSubalgebra ℝ L) : Prop :=
  ∃ B : LinearMap.BilinForm ℝ L, B.IsSymm ∧ (∀ x : L, x ≠ 0 → 0 < B x x) ∧
    ∀ x ∈ K, ∀ y z : L, B ⁅x, y⁆ z = -B y ⁅x, z⁆

/-- Maximality is with respect to compact embedding in the given real Lie algebra. -/
def IsMaximalCompact {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (K : LieSubalgebra ℝ L) : Prop :=
  IsCompactlyEmbedded K ∧ ∀ U : LieSubalgebra ℝ L, K ≤ U → IsCompactlyEmbedded U → U = K

/-- The joint fixed algebra of the compact conjugation and the real structure,
viewed as a real subalgebra of the given real form. -/
def compactSubalgebra {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (ω σ : Conjugation L) : LieSubalgebra ℝ σ.fixed :=
  ω.fixed.comap σ.fixed.incl

/-- The complexified maximal compact algebra of the signature matrix model. -/
def signature_maximal_compact_type : Prop :=
  ∀ p q : ℕ, IsSimpleSize (p + q) →
    ∃ K : LieSubalgebra ℝ (soSignature p q), IsMaximalCompact K ∧
      Nonempty ((ℂ ⊗[ℝ] K) ≃ₗ⁅ℂ⁆ so (Fin p) × so (Fin q))

/-- The complex and real identifications of the maximal compact algebra of `soStar n`. -/
def quaternionic_maximal_compact_type : Prop :=
  ∀ n : ℕ, IsSimpleSize (n + n) →
    let K := compactSubalgebra (coefficientConjugation (Fin n ⊕ Fin n)) (quaternionicConjugation n)
    IsMaximalCompact K ∧ Nonempty ((ℂ ⊗[ℝ] K) ≃ₗ⁅ℂ⁆ Matrix (Fin n) (Fin n) ℂ) ∧
      Nonempty (K ≃ₗ⁅ℝ⁆ OrthogonalCompactGeometry.unitaryAlgebra n)

/-- The real form classification also applies to algebras presented by an
isomorphism from their complexification. -/
def abstract_exhaustion_type : Prop :=
  ∀ (N : ℕ), IsSimpleSize N → ∀ (S : Type*) [LieRing S] [LieAlgebra ℝ S],
    Nonempty ((ℂ ⊗[ℝ] S) ≃ₗ⁅ℂ⁆ so (Fin N)) →
    (∃ p q : ℕ, p + q = N ∧ Nonempty (S ≃ₗ⁅ℝ⁆ soSignature p q)) ∨
    (∃ n : ℕ, n + n = N ∧ Nonempty (S ≃ₗ⁅ℝ⁆ soStar n))

end LieAlgebrasAndRepresentations.RealFormsOrthogonal
