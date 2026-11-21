import MathGenome.Internal.Specs.D07.Ch12.SeparableDefinition
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Content

/-!
Independent statements for K07.12.derivative_criterion, paper.tex:3744–3750.

`polynomialSeparableValue` is the canonical predicate whose equivalence with
simple roots in every splitting field is proved in the upstream goal.
The gcd here is the normalized (monic) polynomial gcd, not the unnormalized
Euclidean algorithm output. All coefficient fields are arbitrary.
The characteristic-p substitution uses polynomial composition, and does
not require the coefficients to have p-th roots in the field.
-/

universe u

namespace Specs.D07.Ch12.DerivativeCriterion

open Polynomial
open scoped Classical

/-- Includes all nonzero constants. -/
def SeparableIffGcdOne : Prop :=
  ∀ (K : Type u) [Field K] (f : Polynomial K), f ≠ 0 →
    (SeparableDefinition.polynomialSeparableValue K f ↔ gcd f f.derivative = 1)

def IrreducibleSeparableIffDerivativeNeZero : Prop :=
  ∀ (K : Type u) [Field K] (f : Polynomial K), Irreducible f →
    (SeparableDefinition.polynomialSeparableValue K f ↔ f.derivative ≠ 0)

/-- The two derivative criteria agree for every irreducible polynomial. -/
def IrreducibleGcdOneIffDerivativeNeZero : Prop :=
  ∀ (K : Type u) [Field K] (f : Polynomial K), Irreducible f →
    (gcd f f.derivative = 1 ↔ f.derivative ≠ 0)

/-- Positive characteristic only; no perfectness hypothesis. Zero and
constant polynomials are allowed in this coefficientwise statement. -/
def DerivativeZeroIffSubstitution : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [CharP K p], 0 < p →
    ∀ f : Polynomial K,
      (f.derivative = 0 ↔ ∃ g : Polynomial K, f = g.comp (X ^ p))

/-- The source's warning that irreducibility cannot be dropped. -/
def NonzeroDerivativeCounterexample : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K],
    ((X - 1 : Polynomial K) ^ 2).derivative ≠ 0 ∧
      ¬ SeparableDefinition.polynomialSeparableValue K ((X - 1) ^ 2)

end Specs.D07.Ch12.DerivativeCriterion
