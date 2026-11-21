import MathGenome.Internal.Specs.D05.M01.System
import Mathlib.Data.Matrix.Basis
import Mathlib.Logic.Equiv.Basic

/-!
Independent interface for paper.tex:722–723, K05.01.row_ops.
Rows and columns are ordered `Fin` indices, with no positivity assumption on their
sizes. The shared data type lists exactly the three permitted operations, including
the distinct-row and nonzero-scalar conditions. These are data, not certificates
of the conclusions. All expected theorem declarations below are definitions of
full proposition types. No implementation module is imported.
-/
namespace D05.M01.RowOps

universe u

/-- A permitted elementary row operation on `m` rows over `K`. -/
inductive RowOperation (K : Type u) [Field K] (m : ℕ) where
  | swap (i j : Fin m) (distinct : i ≠ j)
  | scale (i : Fin m) (a : K) (nonzero : a ≠ 0)
  | add (i j : Fin m) (a : K) (distinct : i ≠ j)

end D05.M01.RowOps

namespace D05.M01.RowOpsSpec

open D05.M01.RowOps
universe u

def applyOpType := ∀ {K : Type u} [Field K] {m n : ℕ},
  RowOperation K m → Matrix (Fin m) (Fin n) K → Matrix (Fin m) (Fin n) K

/-- Swap rows; scale just one row; or add a multiple of row `j` to row `i`. -/
def applyOpValue : applyOpType := fun op A =>
  match op with
  | .swap i j _ => fun r c => A (Equiv.swap i j r) c
  | .scale i a _ => fun r c => if r = i then a * A i c else A r c
  | .add i j a _ => fun r c => if r = i then A i c + a * A j c else A r c

def inverseType := ∀ {K : Type u} [Field K] {m : ℕ},
  RowOperation K m → RowOperation K m

/-- The actual inverse operations, without an assumed inverse-action certificate. -/
def inverseValue : inverseType := fun op =>
  match op with
  | .swap i j h => .swap i j h
  | .scale i a h => .scale i a⁻¹ (inv_ne_zero h)
  | .add i j a h => .add i j (-a) h

def elementaryMatrixType := ∀ {K : Type u} [Field K] {m : ℕ},
  RowOperation K m → Matrix (Fin m) (Fin m) K

/-- Apply the operation to the identity matrix. -/
def elementaryMatrixValue : elementaryMatrixType := fun op => applyOpValue op 1

def swap_entry : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (i j : Fin m) (h : i ≠ j)
    (A : Matrix (Fin m) (Fin n) K) (r : Fin m) (c : Fin n),
    applyOpValue (.swap i j h) A r c =
      if r = i then A j c else if r = j then A i c else A r c

def scale_entry : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (i : Fin m) (a : K) (h : a ≠ 0)
    (A : Matrix (Fin m) (Fin n) K) (r : Fin m) (c : Fin n),
    applyOpValue (.scale i a h) A r c = if r = i then a * A i c else A r c

def add_entry : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (i j : Fin m) (a : K) (h : i ≠ j)
    (A : Matrix (Fin m) (Fin n) K) (r : Fin m) (c : Fin n),
    applyOpValue (.add i j a h) A r c =
      if r = i then A i c + a * A j c else A r c

def inverse_inverse : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ} (op : RowOperation K m),
    inverseValue (inverseValue op) = op

/-- Applying the given operation and then its displayed inverse restores every matrix. -/
def inverse_apply : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (op : RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K),
    applyOpValue (inverseValue op) (applyOpValue op A) = A

/-- The inverse also works in the other order. -/
def apply_inverse : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (op : RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K),
    applyOpValue op (applyOpValue (inverseValue op) A) = A

/-- Left multiplication implements the operation on every rectangular matrix. -/
def elementary_mul : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (op : RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K),
    elementaryMatrixValue op * A = applyOpValue op A

def elementary_inverse_mul : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ} (op : RowOperation K m),
    elementaryMatrixValue (inverseValue op) * elementaryMatrixValue op = 1

def elementary_mul_inverse : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ} (op : RowOperation K m),
    elementaryMatrixValue op * elementaryMatrixValue (inverseValue op) = 1

/-- Invertibility in the square-matrix ring, for every permitted operation. -/
def elementary_isUnit : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ} (op : RowOperation K m),
    IsUnit (elementaryMatrixValue op)

/-- The source's matrix unit `E_ij` is `Matrix.single i j 1`. -/
def elementary_add_eq : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ} (i j : Fin m) (a : K) (h : i ≠ j),
    elementaryMatrixValue (.add i j a h) =
      1 + a • (Matrix.single i j 1 : Matrix (Fin m) (Fin m) K)

def matrixUnit_sq_zero : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ} (i j : Fin m) (_h : i ≠ j),
    (Matrix.single i j 1 : Matrix (Fin m) (Fin m) K) * Matrix.single i j 1 = 0

def shear_mul_shear_inverse : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ} (i j : Fin m) (a : K) (_h : i ≠ j),
    (1 + a • (Matrix.single i j 1 : Matrix (Fin m) (Fin m) K)) *
      (1 - a • Matrix.single i j 1) = 1

end D05.M01.RowOpsSpec
