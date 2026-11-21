import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Transfer.GeometricMatrixSeries
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.MultiplicativeInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Independent statements for the rationality assertion of p204:W17.
The polynomial matrix is I-zM. Polynomial-to-series coercion is the canonical
coefficient-preserving inclusion. The numerator is the (i,j) entry of its
adjugate, and the common denominator is its determinant. -/

noncomputable section
universe u v

namespace Specs.FiniteCombinatorics.Transfer

def polynomialResolventType : Type (max (u + 1) (v + 1)) :=
  ∀ {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι],
    Matrix ι ι R → Matrix ι ι (Polynomial R)

def polynomialResolventValue : polynomialResolventType :=
  fun {R} [_] {ι} [_] [_] M =>
    (1 : Matrix ι ι (Polynomial R)) -
      Matrix.of (fun i j => Polynomial.X * Polynomial.C (M i j))

def resolvent_denominator_constant : Prop :=
  ∀ {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R), (polynomialResolventValue M).det.coeff 0 = 1

def geometric_entry_adjugate : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (i j : ι),
    geometricSeriesValue M i j =
      (((polynomialResolventValue M).adjugate i j : Polynomial K) : PowerSeries K) *
        (((polynomialResolventValue M).det : Polynomial K) : PowerSeries K)⁻¹

/-- Rationality is expressed by a quotient of polynomials with normalized
nonzero constant denominator, interpreted in formal series. -/
def entries_are_rational : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (i j : ι),
    ∃ P Q : Polynomial K, Q.coeff 0 = 1 ∧
      geometricSeriesValue M i j = (P : PowerSeries K) * (Q : PowerSeries K)⁻¹

/-- The same adjugate formula describes the actual inverse unit and the
geometric matrix series. No nonemptiness assumption is imposed on the index. -/
def inverse_adjugate_formula : Prop :=
  ∀ {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K),
    ∃ U : (Matrix ι ι (PowerSeries K))ˣ,
      (U : Matrix ι ι (PowerSeries K)) = 1 - zMatrixValue M ∧
      (↑(U⁻¹) : Matrix ι ι (PowerSeries K)) = geometricSeriesValue M ∧
      ∀ i j : ι, (↑(U⁻¹) : Matrix ι ι (PowerSeries K)) i j =
        (((polynomialResolventValue M).adjugate i j : Polynomial K) : PowerSeries K) *
          (((polynomialResolventValue M).det : Polynomial K) : PowerSeries K)⁻¹

end Specs.FiniteCombinatorics.Transfer
