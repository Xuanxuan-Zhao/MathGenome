import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Card

/-!
Independent statements for K07.13.polynomial_functions
(paper.tex:4054–4063; chapters/M07.13.tex:189–198).

The field is arbitrary, with its finite cardinality identified with q, as
in the preceding power-identity entry. Thus the statements apply to any
chosen q-element base field, without identifying unrelated field copies.
Polynomials are formal `Polynomial F` objects, and their bottom-valued
degree includes the zero polynomial among the representatives of degree
less than q. Uniqueness is only among polynomials satisfying this bound.
-/

universe u

namespace Specs.D07.Ch13.PolynomialFunctions

open Polynomial

/-- The formal polynomial is nonzero, although its evaluation is zero
at every element of the finite field. -/
def NonzeroVanishingPolynomial : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (q : ℕ),
    Fintype.card F = q →
      (X ^ q - X : Polynomial F) ≠ 0 ∧
        ∀ a : F, (X ^ q - X : Polynomial F).eval a = 0

/-- Every function is represented by exactly one formal polynomial of
degree less than the cardinality of the field. -/
def UniqueRepresentative : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (q : ℕ),
    Fintype.card F = q → ∀ h : F → F,
      ∃! f : Polynomial F,
        f.degree < (q : WithBot ℕ) ∧ ∀ a : F, f.eval a = h a

end Specs.D07.Ch13.PolynomialFunctions
