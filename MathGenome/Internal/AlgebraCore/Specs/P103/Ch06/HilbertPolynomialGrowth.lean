import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertSerreLength

/-!
Numerical comparison in the last paragraph of Theorem 6.10, paper.tex:1164.
The coefficients, rational presentation, and arbitrary integer shifts are the
actual ones used by the accepted length version of Hilbert–Serre.
-/
namespace Specs.P103.HilbertPolynomialGrowth
open _root_.P103.HilbertSerreLength

/-- Two shifted degreewise bounds determine the reduced denominator exponent.
The choose expressions are natural binomial coefficients, then cast to ℚ.
No eventual degree or sign of a leading coefficient is assumed. -/
def comparisonType : Prop :=
  ∀ (h : ℤ → ℤ) (b : ℤ) (p : Polynomial ℤ) (e : ℕ),
    (∀ j, 0 ≤ h j) →
    RationalPresentation h b p e →
    (e = 0 ∨ p.eval 1 ≠ 0) →
    ∀ (d r : ℕ), 0 < d → 0 < r →
      ∀ (a : Fin r → ℤ) (J : ℤ), 0 ≤ J → (∀ i, a i ≤ J) →
        (∀ j ≥ J, (h j : ℚ) ≤
          ∑ i, (((j - a i).toNat + d - 1).choose (d - 1) : ℚ)) →
        (∀ j ≥ J, ((j.toNat + d - 1).choose (d - 1) : ℚ) ≤
          ∑ i, (h (j + a i) : ℚ)) →
        e = d

end Specs.P103.HilbertPolynomialGrowth
