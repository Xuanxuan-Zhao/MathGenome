import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials

/-!
Independent statement of the division algorithm, paper.tex:361–367.
`Polynomial K` is the formal coefficient polynomial used by the upstream
univariate coefficient bridge. A pair records joint uniqueness of quotient and
remainder. Natural degree is compared only in the explicit zero-remainder
alternative, so zero dividends and nonzero constant divisors are included.
-/

namespace D05.Specs.Division

/-- Every polynomial over a field has a unique quotient and remainder upon
division by any nonzero polynomial. No monicity or positive degree is required. -/
def divisionAlgorithm : Prop :=
  ∀ (K : Type*) [Field K] (a b : Polynomial K), b ≠ 0 →
    ∃! qr : Polynomial K × Polynomial K,
      a = qr.1 * b + qr.2 ∧
      (qr.2 = 0 ∨ qr.2.natDegree < b.natDegree)

end D05.Specs.Division
