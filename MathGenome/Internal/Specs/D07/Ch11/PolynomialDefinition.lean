import Mathlib.Algebra.Polynomial.Basic

/-!
Independent specification of K07.11.polynomial_definition
(paper.tex:2149–2162; chapters/M07.11.tex:4–17).

The canonical object `Polynomial R` is used throughout. A coefficient sequence
has finite support exactly when it specifies a unique polynomial. This refers
to formal coefficients, not to values of a polynomial function. All assertions
allow noncommutative unital rings and the zero ring. Arithmetic, degree and
evaluation are specified by their separately allocated entries.
-/

universe u

namespace Specs.D07.Ch11.PolynomialDefinition

open Polynomial

/-- Every polynomial has only finitely many nonzero coefficients. -/
def FiniteCoefficientSupport : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R),
    (Function.support (fun i => f.coeff i)).Finite

/-- Precisely the finitely supported sequences specify unique polynomials. -/
def CoefficientSequenceCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (a : ℕ → R),
    (∃! f : Polynomial R, ∀ i, f.coeff i = a i) ↔ (Function.support a).Finite

/-- Equality means equality of every formal coefficient. -/
def CoefficientExtensionality : Prop :=
  ∀ (R : Type u) [Ring R] (f g : Polynomial R),
    f = g ↔ ∀ i, f.coeff i = g.coeff i

/-- The coefficients of a constant polynomial, including index zero. -/
def ConstantCoefficients : Prop :=
  ∀ (R : Type u) [Ring R] (a : R) (i : ℕ),
    (C a).coeff i = if i = 0 then a else 0

/-- The formal indeterminate has coefficient one only at index one. -/
def IndeterminateCoefficients : Prop :=
  ∀ (R : Type u) [Ring R] (i : ℕ),
    (X : Polynomial R).coeff i = if i = 1 then 1 else 0

/-- The constant map is injective without any nontriviality assumption. -/
def ConstantInjectivity : Prop :=
  ∀ (R : Type u) [Ring R], Function.Injective (C : R → Polynomial R)

/-- Any upper bound on the nonzero indices yields the displayed expansion. -/
def BoundedExpansion : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R) (n : ℕ),
    (∀ i, n < i → f.coeff i = 0) →
      f = ∑ i ∈ Finset.range (n + 1), C (f.coeff i) * X ^ i

/-- Every polynomial admits a finite coefficient expansion, including zero. -/
def FiniteExpansion : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R),
    ∃ n : ℕ, f = ∑ i ∈ Finset.range (n + 1), C (f.coeff i) * X ^ i

/-- Extending a finite expression by trailing zero coefficients has no effect. -/
def TrailingZeroIndependence : Prop :=
  ∀ (R : Type u) [Ring R] (a : ℕ → R) (n m : ℕ), n ≤ m →
    (∀ i, n < i → i ≤ m → a i = 0) →
      (∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i) =
        ∑ i ∈ Finset.range (m + 1), C (a i) * X ^ i

end Specs.D07.Ch11.PolynomialDefinition
