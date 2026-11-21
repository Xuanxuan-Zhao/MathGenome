import MathGenome.Internal.Specs.D05.M04.InverseMatrix
import MathGenome.Internal.Specs.D05.M05.Adjugate
import MathGenome.Internal.Specs.D05.M05.DetProduct

/-!
Independent statements for K05.05.det_invertible, paper.tex:878–884.
Invertibility means existence of a two-sided matrix inverse. The determinant
and adjugate are the shared paper constructions. Ring statements allow every
commutative unital ring, including the zero ring, and all sizes including zero.
`Ring.inverse` is the inverse of a unit, extended by zero to nonunits; its uses
below are guarded by a unit hypothesis. Over a field it is ordinary inversion.
-/

namespace D05.Specs.DetInvertible

open D05.M05

/-- The determinant criterion over a commutative ring. -/
def inverse_iff_isUnit_det : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    (∃ B : Matrix (Fin n) (Fin n) R, B * A = 1 ∧ A * B = 1) ↔
      IsUnit (determinant A)

/-- The same criterion for the actual action on coordinate columns. -/
def bijective_iff_isUnit_det : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    Function.Bijective (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A) ↔
      IsUnit (determinant A)

/-- A chosen determinant unit gives the stated two-sided adjugate inverse. -/
def adjugate_inverse : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (u : Rˣ), determinant A = (u : R) →
    ((↑(u⁻¹) : R) • adjugate A) * A = 1 ∧
      A * ((↑(u⁻¹) : R) • adjugate A) = 1

/-- The conventional matrix inverse agrees with the paper's inverse formula. -/
def inverse_eq_adjugate : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    IsUnit (determinant A) → A⁻¹ = Ring.inverse (determinant A) • adjugate A

/-- The determinant of the inverse over a commutative ring. -/
def det_inverse : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    IsUnit (determinant A) → determinant A⁻¹ = Ring.inverse (determinant A)

/-- Over a field the unit condition is exactly nonvanishing. -/
def field_inverse_iff_det_ne_zero : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    (∃ B : Matrix (Fin n) (Fin n) K, B * A = 1 ∧ A * B = 1) ↔
      determinant A ≠ 0

/-- The inverse-determinant identity with ordinary field inversion. -/
def field_det_inverse : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    determinant A ≠ 0 → determinant A⁻¹ = (determinant A)⁻¹

end D05.Specs.DetInvertible
