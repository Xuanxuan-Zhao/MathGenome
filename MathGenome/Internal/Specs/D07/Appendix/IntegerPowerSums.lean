import Mathlib.Basic.Complex.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
Independent specifications for `lem:integer-power-sums`, paper.tex:7646.
A function on `Fin m` records a finite list, including repeated entries and
`m = 0`. The factorization equality expresses that its complete monic root
product is the coefficient image of the integer polynomial `Q`.
-/

namespace Specs.D07.Appendix.IntegerPowerSums

open Polynomial

/-- Every nonnegative power sum of the listed roots is an integer. -/
def PowerSumsIntegral : Prop :=
  ∀ (m : ℕ) (γ : Fin m → ℂ) (Q : Polynomial ℤ),
    Q.map (Int.castRingHom ℂ) = ∏ j, (X - C (γ j)) →
    ∀ r : ℕ, ∃ z : ℤ, ∑ j, γ j ^ r = (z : ℂ)

/-- The same holds for the sum of values of every integer polynomial. -/
def PolynomialSumsIntegral : Prop :=
  ∀ (m : ℕ) (γ : Fin m → ℂ) (Q : Polynomial ℤ),
    Q.map (Int.castRingHom ℂ) = ∏ j, (X - C (γ j)) →
    ∀ A : Polynomial ℤ,
      ∃ z : ℤ, ∑ j, A.eval₂ (Int.castRingHom ℂ) (γ j) = (z : ℂ)

end Specs.D07.Appendix.IntegerPowerSums
