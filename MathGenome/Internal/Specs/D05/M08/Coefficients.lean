import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M04.Trace

/-!
Independent specifications for K05.08.coefficients, paper.tex:1208–1209 (core paragraph).
These are the trace and determinant coefficients of the characteristic
polynomial over an arbitrary field. The matrix statements use the shared
column Leibniz determinant, and the operator statements use the accepted
basis-independent characteristic polynomial. Only the trace coefficient
requires positive dimension; the constant coefficient includes dimension zero.
The separately headed adjugate supplement has its own allocated goals and Specs.
-/

noncomputable section

namespace Specs.D05.M08.Coefficients

open scoped BigOperators

/-- The coefficient of degree `n - 1` is the negative diagonal sum, hence the
negative trace. Positivity prevents truncated subtraction from asserting this
at degree zero for the empty matrix. -/
def matrix_trace_coefficient : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    0 < n →
    (D05.M05.determinant
      (Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) - A.map Polynomial.C)).coeff
        (n - 1) = -(∑ i, A i i) ∧
    (D05.M05.determinant
      (Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) - A.map Polynomial.C)).coeff
        (n - 1) = -Matrix.trace A

/-- Setting the variable to zero gives the determinant of `-A`, whose sign is
`(-1)^n`. No positivity, splitting, or characteristic hypothesis is added. -/
def matrix_constant_coefficient : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    (D05.M05.determinant
      (Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) - A.map Polynomial.C)).coeff 0 =
        D05.M05.determinant (-A) ∧
    D05.M05.determinant (-A) = (-1 : K) ^ n * D05.M05.determinant A

/-- Intrinsic endomorphism form of the trace coefficient. -/
def operator_trace_coefficient : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V),
    0 < Module.finrank K V →
    (Charpoly.charpoly_value T).coeff (Module.finrank K V - 1) =
      -LinearMap.trace K V T

/-- Intrinsic constant coefficient, including the empty determinant `1` on
the zero space. -/
def operator_constant_coefficient : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V),
    (Charpoly.charpoly_value T).coeff 0 =
      (-1 : K) ^ Module.finrank K V * LinearMap.det T

end Specs.D05.M08.Coefficients
