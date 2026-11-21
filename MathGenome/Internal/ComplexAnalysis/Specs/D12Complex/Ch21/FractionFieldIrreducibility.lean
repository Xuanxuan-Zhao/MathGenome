import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Content

/-!
The algebraic bridge in `paper.tex`, Chapter 21, proof of the finite exceptional
set theorem (and reused in the transitivity corollary).

`Polynomial (Polynomial ℂ)` is ℂ[z][w]: the inner variable is z and the
outer variable is w. Thus `coeff j` is a polynomial in z, `natDegree`
is the w-degree, and `derivative` is the partial derivative with respect to w.
The coefficient map into `RatFunc ℂ` is the canonical inclusion ℂ[z] → ℂ(z).
No primitivity or rational-coefficient irreducibility is a hypothesis.
-/

namespace Specs.D12Complex.Ch21.FractionFieldIrreducibility

/-- The full Gauss bridge, with the exact derivative degrees, including d = 1.
A common divisor of the w-coefficients is a unit of ℂ[z], hence constant.
Coprimality is stated for the image of the actual partial derivative. -/
def gaussBridge : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    (∀ q : Polynomial ℂ, (∀ j : ℕ, q ∣ P.coeff j) →
      IsUnit q ∧ q.natDegree = 0) ∧
    P.IsPrimitive ∧
    let Q := P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
    Irreducible Q ∧
    Q.natDegree = d ∧
    P.derivative ≠ 0 ∧
    P.derivative.natDegree = d - 1 ∧
    P.derivative.degree = ((d - 1 : ℕ) : WithBot ℕ) ∧
    Q.derivative = P.derivative.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) ∧
    Q.derivative ≠ 0 ∧
    Q.derivative.natDegree = d - 1 ∧
    Q.derivative.degree = ((d - 1 : ℕ) : WithBot ℕ) ∧
    IsCoprime Q (P.derivative.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)))

end Specs.D12Complex.Ch21.FractionFieldIrreducibility
