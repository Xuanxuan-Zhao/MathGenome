import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorRing
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

namespace GaloisFormalization.PV

open scoped Matrix

universe u v

/-- Coefficient data for a linear system of rank `n` over an operator field `K`. -/
def LinearSystem (kind : OperatorKind) (K : Type u) [Field K] (n : ℕ) : Type u :=
  match kind with
  | .differential => Matrix (Fin n) (Fin n) K
  | .difference => Matrix.GeneralLinearGroup (Fin n) K

namespace LinearSystem

variable {kind : OperatorKind} {K : Type u} [Field K] {n : ℕ}

/-- The differential system with coefficient matrix `A`. -/
def differential (A : Matrix (Fin n) (Fin n) K) : LinearSystem .differential K n := A

/-- The difference system with invertible coefficient matrix `A`. -/
def difference (A : Matrix.GeneralLinearGroup (Fin n) K) : LinearSystem .difference K n := A

/-- The underlying square coefficient matrix. -/
def coefficientMatrix (A : LinearSystem kind K n) : Matrix (Fin n) (Fin n) K :=
  match kind, A with
  | .differential, M => M
  | .difference, M => (show Matrix.GeneralLinearGroup (Fin n) K from M).val

/-- View the coefficient matrix in the algebra where solutions are taken. -/
def mapCoefficients (A : LinearSystem kind K n) (S : Type v) [CommRing S] [Algebra K S] :
    Matrix (Fin n) (Fin n) S :=
  A.coefficientMatrix.map (algebraMap K S)

section Solutions

variable {S : Type v} [CommRing S] [Algebra K S]

/-- The column equation, with the operator on `S` applied entrywise.
For a base operator `D`, the compatible extension hypothesis is `D.IsExtension E`. -/
def IsSolution (A : LinearSystem kind K n) (E : Operator kind S) (x : Fin n → S) : Prop :=
  (fun i => E (x i)) = A.mapCoefficients S *ᵥ x

/-- The matrix equation for a fundamental matrix, given as a matrix unit. -/
def IsFundamental (A : LinearSystem kind K n) (E : Operator kind S)
    (Y : Matrix.GeneralLinearGroup (Fin n) S) : Prop :=
  Y.val.map E = A.mapCoefficients S * Y.val

/-- The solution columns of the system in `S`. -/
def Solution (A : LinearSystem kind K n) (E : Operator kind S) : Type v :=
  {x // A.IsSolution E x}

/-- The fundamental matrices of the system in `S`. -/
def FundamentalMatrix (A : LinearSystem kind K n) (E : Operator kind S) : Type v :=
  {Y // A.IsFundamental E Y}

end Solutions

/-- The inverse of the determinant unit, viewed as a scalar in the coefficient ring. -/
def determinantInverse {S : Type v} [CommRing S]
    (Y : Matrix.GeneralLinearGroup (Fin n) S) : S :=
  ↑((Matrix.GeneralLinearGroup.det Y)⁻¹)

end LinearSystem
end GaloisFormalization.PV
