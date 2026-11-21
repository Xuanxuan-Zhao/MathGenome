import MathGenome.Internal.Specs.D05.M04.ChangeBasis
import MathGenome.Internal.Specs.D05.M05.DetProduct
import Mathlib.LinearAlgebra.Determinant

/-!
Independent specification for K05.05.operator_det, paper.tex:896–899.

The determinant in a given finite ordered basis uses the accepted column
matrix and the accepted Leibniz determinant. Its algebraic properties are
stated over every commutative unital ring. The intrinsic operator determinant
is Mathlib's determinant, restricted here to the finite-dimensional vector
spaces of the source; its agreement with the based definition is an obligation,
not an assumed certificate. All sizes include zero. The later exterior-power
comparison (paper.tex:901–907) is outside this assigned excerpt.
-/

namespace Specs.D05.M05.OperatorDet

open Specs.D05.M04.MatrixOfMap Specs.D05.M04.ChangeBasis

universe u v

/-- Determinant computed in a finite ordered basis. -/
def detInBasis_type : Type (max (u + 1) (v + 1)) :=
  {R : Type u} → {V : Type v} → [CommRing R] →
  [AddCommGroup V] → [Module R V] → {n : ℕ} →
  Module.Basis (Fin n) R V → Module.End R V → R

noncomputable def detInBasis_value : detInBasis_type.{u, v} :=
  fun b T => D05.M05.determinant (matrixOfMap_value b b T)

/-- The intrinsic determinant, on exactly the finite-dimensional source domain. -/
def operatorDet_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [Field K] →
  [AddCommGroup V] → [Module K V] → [FiniteDimensional K V] →
  Module.End K V → K

noncomputable def operatorDet_value : operatorDet_type.{u, v} :=
  fun T => LinearMap.det T

/-- The paper's determinant of the basis matrix is the standard operator scalar. -/
def detInBasis_eq_linearMap_det : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {n : ℕ} (b : Module.Basis (Fin n) R V) (T : Module.End R V),
    detInBasis_value b T = LinearMap.det T

/-- Explicit similarity formula, with `P` converting new to old coordinates. -/
def matrix_change_basis : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {n : ℕ} (b b' : Module.Basis (Fin n) R V) (T : Module.End R V),
    matrixOfMap_value b' b' T =
      (changeMatrix_value b b')⁻¹ * matrixOfMap_value b b T * changeMatrix_value b b'

/-- Determinants agree for any two finite bases, even with different index sizes. -/
def basis_independent : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {n m : ℕ} (b : Module.Basis (Fin n) R V)
    (b' : Module.Basis (Fin m) R V) (T : Module.End R V),
    detInBasis_value b' T = detInBasis_value b T

/-- Multiplicativity in any specified basis, without invertibility assumptions. -/
def detInBasis_comp : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {n : ℕ} (b : Module.Basis (Fin n) R V) (S T : Module.End R V),
    detInBasis_value b (S.comp T) = detInBasis_value b S * detInBasis_value b T

/-- The intrinsic definition gives the paper's scalar in every basis. -/
def operatorDet_eq_detInBasis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    (T : Module.End K V), operatorDet_value T = detInBasis_value b T

/-- The conclusion `det(ST) = det(S) det(T)` for all operators. -/
def operatorDet_comp : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S T : Module.End K V),
    operatorDet_value (S.comp T) = operatorDet_value S * operatorDet_value T

/-- Identity, including the identity of the zero vector space. -/
def operatorDet_id : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], operatorDet_value (LinearMap.id : Module.End K V) = 1

/-- Empty basis matrices have determinant one over every commutative ring. -/
def detInBasis_empty : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 0) R V) (T : Module.End R V), detInBasis_value b T = 1

/-- The finite-dimensional operator determinant retains the empty convention. -/
def operatorDet_zero_dim : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], Module.finrank K V = 0 →
    ∀ T : Module.End K V, operatorDet_value T = 1

end Specs.D05.M05.OperatorDet
