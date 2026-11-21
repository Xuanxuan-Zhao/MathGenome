import Mathlib.RingTheory.PowerSeries.Derivative
import MathGenome.Internal.Specs.D05.M05.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Formal series for paper.tex:1238–1252. The index set `Fin n` allows every
finite size, including zero. No characteristic or splitting assumption is used.
Matrix series are represented entrywise in the commutative coefficient ring K⟦X⟧;
matrix multiplication itself remains noncommutative. -/
noncomputable section
namespace D05.M08.NewtonIdentities
open PowerSeries
variable {K : Type*} [Field K] {n : ℕ}

def constantMatrix (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K⟦X⟧ :=
  A.map C

def pencil (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K⟦X⟧ :=
  1 - (X : K⟦X⟧) • constantMatrix A

/-- Entrywise coefficients are exactly the powers A^j. -/
def geometricMatrix (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K⟦X⟧ :=
  fun i k => mk (fun j => (A ^ j) i k)

def determinantSeries (A : Matrix (Fin n) (Fin n) K) : K⟦X⟧ := D05.M05.determinant (pencil A)

/-- The coefficient of degree j is tr(A^(j+1)), i.e. the reindexed sum in the paper. -/
def tracePowerSeries (A : Matrix (Fin n) (Fin n) K) : K⟦X⟧ :=
  mk (fun j => Matrix.trace (A ^ (j + 1)))
end D05.M08.NewtonIdentities

namespace Specs.D05.M08.NewtonIdentities.Series
open PowerSeries _root_.D05.M08.NewtonIdentities

def geometricMatrix_type := ∀ {K : Type*} [Field K] {n : ℕ},
  Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K⟦X⟧
def geometricMatrix_value : geometricMatrix_type := @geometricMatrix

def coefficients : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (j : ℕ) (i k : Fin n),
  coeff j (geometricMatrix A i k) = (A ^ j) i k

def inverse_left : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K), pencil A * geometricMatrix A = 1

def inverse_right : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K), geometricMatrix A * pencil A = 1

def determinant_derivative : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K),
  derivative (determinantSeries A) =
    -Matrix.trace (_root_.D05.M05.adjugate (pencil A) * constantMatrix A)

def adjugate_series : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K),
  _root_.D05.M05.adjugate (pencil A) = determinantSeries A • geometricMatrix A

def logarithmic_derivative : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K),
  derivative (determinantSeries A) = -determinantSeries A * tracePowerSeries A

/-- Cauchy products have finite coefficients, without an analytic sum. -/
def finite_coefficients : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (j : ℕ),
  coeff (j + 1) (determinantSeries A) * (j + 1 : K) =
    -∑ p ∈ Finset.antidiagonal j,
      coeff p.1 (determinantSeries A) * Matrix.trace (A ^ (p.2 + 1))

def empty_case : Prop := ∀ {K : Type*} [Field K]
    (A : Matrix (Fin 0) (Fin 0) K),
  geometricMatrix A = 1 ∧ pencil A = 1 ∧ determinantSeries A = 1 ∧
    tracePowerSeries A = 0 ∧ derivative (determinantSeries A) = 0
end Specs.D05.M08.NewtonIdentities.Series
