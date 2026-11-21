import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition
import Mathlib.Algebra.Lie.Classical
import Mathlib.Tactic.NoncommRing

/-! Matrix lift interfaces for the orthogonal row of LA-J07, with the inner
subgroup of LA-J01. The standard form on the defining space has matrix 1. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts

open Matrix LieAlgebra
open Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition (Aut inner)

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

abbrev so (ι : Type u) [Fintype ι] [DecidableEq ι] := Orthogonal.so ι ℂ

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Orthogonality for the standard symmetric form. -/
def IsOrthogonal {R : Type*} [CommRing R] (A : Matrix ι ι R) : Prop := Aᵀ * A = 1

/-- The real matrices viewed in the complex matrix algebra. -/
def complexMatrix (A : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  Complex.ofRealHom.mapMatrix A

/-- Entrywise complex conjugation in the standard matrix coordinates. -/
def conjMatrix (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Complex.conjAe.toRingEquiv.mapMatrix A

@[simp] theorem complexMatrix_apply (A : Matrix ι ι ℝ) (i j : ι) :
    complexMatrix A i j = (A i j : ℂ) := rfl

@[simp] theorem conjMatrix_apply (A : Matrix ι ι ℂ) (i j : ι) :
    conjMatrix A i j = star (A i j) := rfl

theorem complexMatrix_transpose (A : Matrix ι ι ℝ) :
    complexMatrix Aᵀ = (complexMatrix A)ᵀ := rfl

theorem conjMatrix_transpose (A : Matrix ι ι ℂ) :
    conjMatrix Aᵀ = (conjMatrix A)ᵀ := rfl

theorem complex_orthogonal {A : Matrix ι ι ℝ} (hA : IsOrthogonal A) :
    IsOrthogonal (complexMatrix A) := by
  change (complexMatrix A)ᵀ * complexMatrix A = 1
  rw [← complexMatrix_transpose]
  exact (map_mul Complex.ofRealHom.mapMatrix _ _).symm.trans
    ((congrArg complexMatrix hA).trans (map_one Complex.ofRealHom.mapMatrix))

/-- Coefficient conjugation of the complex skew-symmetric algebra. -/
def coefficientConjugation (X : so ι) : so ι :=
  ⟨conjMatrix X.val, (Orthogonal.mem_so _ _ _).2 <| by
    rw [← conjMatrix_transpose, (Orthogonal.mem_so _ _ _).1 X.property]
    exact map_neg (Complex.conjAe.toRingEquiv.mapMatrix) X.val⟩

private theorem skew_congruence (A : Matrix ι ι ℂ) (X : so ι) :
    A * X.val * Aᵀ ∈ so ι := by
  rw [Orthogonal.mem_so, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    (Orthogonal.mem_so _ _ _).1 X.property, neg_mul, mul_neg, mul_assoc]

/-- Matrix conjugation on the skew-symmetric algebra as a complex Lie equivalence. -/
def orthogonalLieEquiv (A : Matrix ι ι ℂ) (hA : IsOrthogonal A) : so ι ≃ₗ⁅ℂ⁆ so ι where
  toFun X := ⟨A * X.val * Aᵀ, skew_congruence A X⟩
  invFun X := ⟨Aᵀ * X.val * Aᵀᵀ, skew_congruence Aᵀ X⟩
  left_inv X := Subtype.ext <| by
    change Aᵀ * (A * X.val * Aᵀ) * Aᵀᵀ = X.val
    rw [Matrix.transpose_transpose]
    calc
      _ = (Aᵀ * A) * X.val * (Aᵀ * A) := by noncomm_ring
      _ = _ := by rw [show Aᵀ * A = 1 from hA, one_mul, mul_one]
  right_inv X := Subtype.ext <| by
    change A * (Aᵀ * X.val * Aᵀᵀ) * Aᵀ = X.val
    rw [Matrix.transpose_transpose]
    calc
      _ = (A * Aᵀ) * X.val * (A * Aᵀ) := by noncomm_ring
      _ = _ := by rw [mul_eq_one_comm.mp hA, one_mul, mul_one]
  map_add' X Y := Subtype.ext <| by
    change A * (X.val + Y.val) * Aᵀ = A * X.val * Aᵀ + A * Y.val * Aᵀ
    rw [mul_add, add_mul]
  map_smul' a X := Subtype.ext <| by
    change A * (a • X.val) * Aᵀ = a • (A * X.val * Aᵀ)
    rw [mul_smul_comm, smul_mul_assoc]
  map_lie' {X Y} := Subtype.ext <| by
    change A * (X.val * Y.val - Y.val * X.val) * Aᵀ =
      (A * X.val * Aᵀ) * (A * Y.val * Aᵀ) - (A * Y.val * Aᵀ) * (A * X.val * Aᵀ)
    calc
      _ = A * (X.val * (1 : Matrix ι ι ℂ) * Y.val -
          Y.val * (1 : Matrix ι ι ℂ) * X.val) * Aᵀ := by simp
      _ = _ := by rw [← show Aᵀ * A = 1 from hA]; noncomm_ring

/-- The same conjugation in the automorphism group used for LA-J01. -/
def orthogonalAction (A : Matrix ι ι ℂ) (hA : IsOrthogonal A) : Aut (so ι) :=
  ⟨(orthogonalLieEquiv A hA).toLinearEquiv, (orthogonalLieEquiv A hA).map_lie⟩

@[simp] theorem orthogonalAction_apply (A : Matrix ι ι ℂ) (hA : IsOrthogonal A) (X : so ι) :
    ((orthogonalAction A hA).val X).val = A * X.val * Aᵀ := rfl

/-- Commuting with the compact coefficient conjugation. -/
def CommutesWithConjugation (g : Aut (so ι)) : Prop :=
  ∀ X : so ι, coefficientConjugation (g.val X) = g.val (coefficientConjugation X)

/-- A complex orthogonal representative for an actual Lie automorphism. -/
def HasComplexRepresentative (g : Aut (so ι)) : Prop :=
  ∃ (A : Matrix ι ι ℂ) (hA : IsOrthogonal A), g = orthogonalAction A hA

/-- A real orthogonal representative for an actual complex Lie automorphism. -/
def HasRealRepresentative (g : Aut (so ι)) : Prop :=
  ∃ (A : Matrix ι ι ℝ) (hA : IsOrthogonal A),
    g = orthogonalAction (complexMatrix A) (complex_orthogonal hA)

def commuting_with_skew_is_scalar_type : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], 2 < Fintype.card ι →
    ∀ B : Matrix ι ι ℂ, (∀ X : so ι, B * X.val = X.val * B) → ∃ c : ℂ, B = c • 1

def inner_has_complex_representative_type : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], 2 < Fintype.card ι →
    ∀ g : Aut (so ι), g ∈ inner (so ι) → HasComplexRepresentative g

def complex_has_real_representative_type : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], 2 < Fintype.card ι →
    ∀ g : Aut (so ι), HasComplexRepresentative g → CommutesWithConjugation g →
      HasRealRepresentative g

def complex_representative_mul_type : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {g h : Aut (so ι)},
    HasComplexRepresentative g → HasComplexRepresentative h → HasComplexRepresentative (g * h)

def real_representative_mul_type : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {g h : Aut (so ι)},
    HasRealRepresentative g → HasRealRepresentative h → HasRealRepresentative (g * h)

/-- A complex orthogonal representative of the same outer class suffices
to construct a real orthogonal lift of a compact-preserving automorphism. -/
def real_representative_of_inner_difference_type : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], 2 < Fintype.card ι →
    ∀ {g h : Aut (so ι)}, g * h⁻¹ ∈ inner (so ι) →
      HasComplexRepresentative h → CommutesWithConjugation g → HasRealRepresentative g

end Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts
