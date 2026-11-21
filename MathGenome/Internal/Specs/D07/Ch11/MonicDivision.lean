import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
Independent specification of K07.11.monic_division
(paper.tex:2315–2347; chapters/M07.11.tex:170–202).

The objects are formal polynomials with their canonical ring operations.
Degree is `WithBot ℕ`, with bottom at the zero polynomial. Uniqueness is
joint uniqueness of the quotient and remainder. The coefficient ring is
commutative and nontrivial, but need not be a domain. The final statement
records the source's obstruction even over the domain ℤ.
-/

universe u

namespace Specs.D07.Ch11.MonicDivision

open Polynomial

def UniqueMonicDivision : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] (f g : Polynomial R),
    g.Monic → ∃! qr : Polynomial R × Polynomial R,
      f = qr.1 * g + qr.2 ∧ qr.2.degree < g.degree

def UnitLeadingCoefficientDivision : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] (f g : Polynomial R),
    IsUnit g.leadingCoeff → ∃! qr : Polynomial R × Polynomial R,
      f = qr.1 * g + qr.2 ∧ qr.2.degree < g.degree

/-- Any quotient and remainder on division by one are exactly `f` and zero. -/
def DivisionByOne : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] (f q r : Polynomial R),
    f = q * 1 + r → r.degree < (1 : Polynomial R).degree → q = f ∧ r = 0

/-- The nonzero constant divisor two does not permit this division of X.
The bound is literally below degree zero, as in the source. -/
def ConstantDivisorObstruction : Prop :=
  (C (2 : ℤ) : Polynomial ℤ) ≠ 0 ∧
  (C (2 : ℤ) : Polynomial ℤ).leadingCoeff ≠ 0 ∧
  ¬ ∃ q r : Polynomial ℤ,
    X = q * C (2 : ℤ) + r ∧ r.degree < (0 : WithBot ℕ)

end Specs.D07.Ch11.MonicDivision
