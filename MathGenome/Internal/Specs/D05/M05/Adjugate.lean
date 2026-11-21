import MathGenome.Internal.Specs.D05.M05.Cofactor
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
Independent interface for paper.tex:834–839, K05.05.adjugate.
The adjugate is defined from the already shared signed deleted minors, not
from an inverse. In size zero it is the unique empty matrix. All sizes and
all commutative unital rings (including the zero ring) are allowed.
-/

noncomputable section

namespace D05.M05

/-- Transpose of the cofactor matrix in positive size, with the empty-matrix
convention in size zero. -/
def adjugate {R : Type*} [CommRing R] {n : ℕ} :
    Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R :=
  match n with
  | 0 => fun _ => 0
  | _m + 1 => fun A i j => cofactor A j i

end D05.M05

namespace D05.Specs.Adjugate

open D05.M05

def adjugate_type := ∀ {R : Type*} [CommRing R] {n : ℕ},
  Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R

def adjugate_value : adjugate_type := @D05.M05.adjugate

/-- The paper's entry convention uses the transposed indices. -/
def cofactor_entry : Prop := ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)),
  adjugate A i j = cofactor A j i

/-- Bridge to the library's independently defined adjugate. -/
def matrix_adjugate_bridge : Prop := ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R), adjugate A = Matrix.adjugate A

def mul_adjugate : Prop := ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R),
  A * adjugate A = determinant A • (1 : Matrix (Fin n) (Fin n) R)

def adjugate_mul : Prop := ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R),
  adjugate A * A = determinant A • (1 : Matrix (Fin n) (Fin n) R)

/-- Both equations together, without an invertibility hypothesis. -/
def adjugate_identities : Prop := ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R),
  A * adjugate A = determinant A • (1 : Matrix (Fin n) (Fin n) R) ∧
    adjugate A * A = determinant A • (1 : Matrix (Fin n) (Fin n) R)

def singleton_adjugate : Prop := ∀ {R : Type*} [CommRing R]
    (A : Matrix (Fin 1) (Fin 1) R), adjugate A = 1

/-- Every empty matrix is the chosen empty adjugate. -/
def empty_adjugate : Prop := ∀ {R : Type*} [CommRing R]
    (A B : Matrix (Fin 0) (Fin 0) R), adjugate A = B

/-- In size zero both identities really are equalities of empty matrices. -/
def empty_identities : Prop := ∀ {R : Type*} [CommRing R]
    (A : Matrix (Fin 0) (Fin 0) R),
  A * adjugate A = (1 : Matrix (Fin 0) (Fin 0) R) ∧
    adjugate A * A = (1 : Matrix (Fin 0) (Fin 0) R)

end D05.Specs.Adjugate
