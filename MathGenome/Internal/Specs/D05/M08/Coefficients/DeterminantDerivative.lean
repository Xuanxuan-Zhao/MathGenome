import MathGenome.Internal.Specs.D05.M05.Adjugate
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Independent statement of the differentiation step in paper.tex:1220–1222.
The matrix entries and the equality are formal polynomials over any field.
The determinant and adjugate are the shared Leibniz and cofactor constructions.
-/

namespace Specs.D05.M08.Coefficients.DeterminantDerivative

noncomputable def determinant_derivative : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ}, 1 ≤ n →
    ∀ A : Matrix (Fin n) (Fin n) K,
      Polynomial.derivative
          (D05.M05.determinant
            (Matrix.scalar (Fin n) Polynomial.X + A.map Polynomial.C)) =
        Matrix.trace (D05.M05.adjugate
          (Matrix.scalar (Fin n) Polynomial.X + A.map Polynomial.C))

end Specs.D05.M08.Coefficients.DeterminantDerivative
