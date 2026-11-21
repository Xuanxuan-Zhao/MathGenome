import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
Independent specification of the quaternion-matrix part of
`K07.01.dihedral_quaternion_models` (paper.tex:370–375).
The matrices are the source matrices, not an abstract replacement. The
identification uses Mathlib's `QuaternionGroup 2`, whose constructors are
`a t = i^t` and `xa t = j i^t`. In particular `xa 1` corresponds to `-K`.
-/

namespace Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev MatrixGroup := Matrix.GeneralLinearGroup (Fin 2) ℂ

def E : Mat := 1
def I : Mat := !![Complex.I, 0; 0, -Complex.I]
def J : Mat := !![0, 1; -1, 0]
def K : Mat := I * J

/-- The eight displayed matrices, in the order used for distinctness. -/
def matrixList : Fin 8 → Mat := ![E, -E, I, -I, J, -J, K, -K]

def eightMatrices : Set Mat := {E, -E, I, -I, J, -J, K, -K}

/-- The explicit quaternion notation, with the library's `j i^t` convention. -/
def modelMatrix : QuaternionGroup 2 → Mat
  | .a t => match t.val with
    | 0 => E
    | 1 => I
    | 2 => -E
    | _ => -I
  | .xa t => match t.val with
    | 0 => J
    | 1 => -K
    | 2 => -J
    | _ => K

def MatrixIdentities : Prop :=
  I ^ 2 = -E ∧ J ^ 2 = -E ∧ K ^ 2 = -E ∧
    J * I = -(I * J) ∧ I * J * K = -E ∧ I * J ≠ J * I

def EightDistinct : Prop := Function.Injective matrixList

/-- Closure and invertibility refer to the actual matrices and identity. -/
def MatrixClosure : Prop :=
  E ∈ eightMatrices ∧
    (∀ A ∈ eightMatrices, ∀ B ∈ eightMatrices, A * B ∈ eightMatrices) ∧
    (∀ A ∈ eightMatrices, ∃ B ∈ eightMatrices, A * B = E ∧ B * A = E)

/-- A subgroup of GL with exactly the displayed matrices, cardinality eight,
and a noncommuting pair. The multiplicative equivalence is required to have
the explicit matrix values given above, so it identifies the source model. -/
def QuaternionMatrixModel : Prop :=
  ∃ H : Subgroup MatrixGroup,
    (∀ g : MatrixGroup, g ∈ H ↔ (g : Mat) ∈ eightMatrices) ∧
    Nat.card H = 8 ∧
    (∃ g h : H, g * h ≠ h * g) ∧
    ∃ e : QuaternionGroup 2 ≃* H,
      ∀ q : QuaternionGroup 2, (((e q : H) : MatrixGroup) : Mat) = modelMatrix q

end Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices
