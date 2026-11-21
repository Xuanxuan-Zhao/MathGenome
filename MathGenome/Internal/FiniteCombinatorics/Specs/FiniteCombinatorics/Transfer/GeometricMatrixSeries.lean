import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.Data.Matrix.Basic

/-! Independent statements for the first assertion of p204:W17.
Matrices have entries in `PowerSeries R`. The variable times a constant matrix
has entry `X * C (M i j)`; the geometric series has entry the OGF of `(M^n) i j`.
No nonemptiness, field, or convergence assumption is made. -/

noncomputable section

universe u v

namespace Specs.FiniteCombinatorics.Transfer

def zMatrixType : Type (max (u + 1) (v + 1)) :=
  ∀ {R : Type u} [CommRing R] {ι : Type v},
    Matrix ι ι R → Matrix ι ι (PowerSeries R)

def zMatrixValue : zMatrixType :=
  fun {_} [_] {_} M i j => PowerSeries.X * PowerSeries.C (M i j)

def geometricSeriesType : Type (max (u + 1) (v + 1)) :=
  ∀ {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι],
    Matrix ι ι R → Matrix ι ι (PowerSeries R)

def geometricSeriesValue : geometricSeriesType :=
  fun {_} [_] {_} [_] [_] M i j =>
    Specs.FiniteCombinatorics.Series.ogfValue (fun n => (M ^ n) i j)

def geometric_coefficients : Prop :=
  ∀ {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (n : ℕ) (i j : ι),
    PowerSeries.coeff n (geometricSeriesValue M i j) = (M ^ n) i j

def resolvent_mul_geometric : Prop :=
  ∀ {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R),
    (1 - zMatrixValue M) * geometricSeriesValue M = 1

def geometric_mul_resolvent : Prop :=
  ∀ {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R),
    geometricSeriesValue M * (1 - zMatrixValue M) = 1

/-- The inverse is expressed as the inverse of a unit, so it is meaningful over
any commutative coefficient ring, including the zero ring and empty matrices. -/
def geometric_inverse : Prop :=
  ∀ {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R),
    ∃ U : (Matrix ι ι (PowerSeries R))ˣ,
      (U : Matrix ι ι (PowerSeries R)) = 1 - zMatrixValue M ∧
      (↑(U⁻¹) : Matrix ι ι (PowerSeries R)) = geometricSeriesValue M

end Specs.FiniteCombinatorics.Transfer
