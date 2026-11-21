import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Basic.Complex.Basic

/-!
Independent propositions for the common-factor conclusion and counterexample
in K07.19.primitive_fermat, paper.tex:5784–5795.

The coefficient field is arbitrary of characteristic zero. All three original
polynomials are nonzero; they are not assumed coprime or nonconstant. We use
the normalized (hence monic, when nonzero) gcd of the first two polynomials.
The equation makes this a gcd of the triple as well. Quotients are polynomial
Euclidean quotients, with exact divisibility explicitly part of the conclusion.
The complex example includes the nonzero and nonconstant assertions and the
failure of coprimality, rather than just its scalar power identity.
-/

universe u

namespace Specs.D07.Ch19.PrimitiveFermatCommonFactorClassification

open Polynomial
open scoped Classical

/-- Removing a common monic gcd leaves a nonzero pairwise-coprime solution. -/
def CommonGcdReduction : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (n : ℕ), 3 ≤ n →
    ∀ f g h : Polynomial F, f ≠ 0 → g ≠ 0 → h ≠ 0 →
      f ^ n + g ^ n = h ^ n →
      let d := gcd f g
      d ≠ 0 ∧ d.Monic ∧ d ∣ h ∧
      (∀ e : Polynomial F, e ∣ f → e ∣ g → e ∣ h → e ∣ d) ∧
      f / d ≠ 0 ∧ g / d ≠ 0 ∧ h / d ≠ 0 ∧
      f = d * (f / d) ∧ g = d * (g / d) ∧ h = d * (h / d) ∧
      IsCoprime (f / d) (g / d) ∧
      IsCoprime (f / d) (h / d) ∧
      IsCoprime (g / d) (h / d) ∧
      (f / d) ^ n + (g / d) ^ n = (h / d) ^ n

/-- Every nonzero solution is a common polynomial multiple of a nonzero
constant solution, with the equation retained over the original field. -/
def CommonFactorClassification : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (n : ℕ), 3 ≤ n →
    ∀ f g h : Polynomial F, f ≠ 0 → g ≠ 0 → h ≠ 0 →
      f ^ n + g ^ n = h ^ n →
      ∃ (d : Polynomial F) (a b c : F),
        d ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
        f = d * C a ∧ g = d * C b ∧ h = d * C c ∧
        a ^ n + b ^ n = c ^ n

/-- For every exponent in scope, the explicit nonprimitive complex triple
`X, X, C c * X` disproves unqualified nonconstant impossibility. -/
def ComplexCounterexample : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ c : ℂ,
    c ≠ 0 ∧ c ^ n = 2 ∧
    (X : Polynomial ℂ) ≠ 0 ∧ C c * X ≠ 0 ∧
    (X : Polynomial ℂ) ^ n + X ^ n = (C c * X) ^ n ∧
    (∀ a : ℂ, (X : Polynomial ℂ) ≠ C a) ∧
    (∀ a : ℂ, C c * X ≠ C a) ∧
    ¬ IsCoprime (X : Polynomial ℂ) X

end Specs.D07.Ch19.PrimitiveFermatCommonFactorClassification
