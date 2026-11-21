import MathGenome.Internal.Specs.D07.Ch11.PolynomialArithmetic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
Independent specification of K07.11.evaluation_universal,
paper.tex:2229–2254 (chapters/M07.11.tex:84–109).

The source rings are associative and unital, with no nontriviality or
commutativity assumptions unless explicitly stated. `Polynomial R` is the
same formal finite coefficient sequence as in the upstream specifications.
All maps below are unital ring homomorphisms. The condition `Commute s (φ a)`
means precisely `s * φ a = φ a * s`; it is not an assumed centrality of S.
The coefficient formula and the formula for arbitrary finite expressions
record the displayed evaluation formula, including zero and trailing zeros.
The final statements identify ordinary evaluation and substitution with the
canonical Mathlib operations, retaining commutation for noncommutative rings.
-/

universe u v

namespace Specs.D07.Ch11.EvaluationUniversal

open Polynomial

/-- The unique extension with the prescribed values on constants and X. -/
def UniversalEvaluation : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (φ : R →+* S) (s : S),
    (∀ a, Commute s (φ a)) →
      ∃! Φ : Polynomial R →+* S, (∀ a, Φ (C a) = φ a) ∧ Φ X = s

/-- Every extension is given by the finite sum over the formal support. -/
def CoefficientFormula : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (φ : R →+* S) (s : S) (Φ : Polynomial R →+* S),
    (∀ a, Φ (C a) = φ a) → Φ X = s →
      ∀ f, Φ f = ∑ i ∈ f.support, φ (f.coeff i) * s ^ i

/-- The displayed formula holds for every finite coefficient expression. -/
def FiniteSumFormula : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (φ : R →+* S) (s : S) (Φ : Polynomial R →+* S),
    (∀ a, Φ (C a) = φ a) → Φ X = s →
      ∀ (t : Finset ℕ) (a : ℕ → R),
        Φ (∑ i ∈ t, C (a i) * X ^ i) = ∑ i ∈ t, φ (a i) * s ^ i

/-- In a commutative target the commutation condition is automatic. -/
def CommutativeUniversalEvaluation : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [CommRing S]
    (φ : R →+* S) (s : S),
    ∃! Φ : Polynomial R →+* S, (∀ a, Φ (C a) = φ a) ∧ Φ X = s

/-- The polynomial identity XC(a)=C(a)X forces the stated commutation. -/
def NecessaryCommutation : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (φ : R →+* S) (s : S) (Φ : Polynomial R →+* S),
    (∀ a, Φ (C a) = φ a) → Φ X = s → ∀ a, Commute s (φ a)

/-- In particular the commutation condition cannot simply be omitted. -/
def ExistenceIffCommutation : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (φ : R →+* S) (s : S),
    (∃ Φ : Polynomial R →+* S, (∀ a, Φ (C a) = φ a) ∧ Φ X = s) ↔
      ∀ a, Commute s (φ a)

/-- Evaluation at x uses the identity coefficient homomorphism. -/
def OrdinaryEvaluation : Prop :=
  ∀ (R : Type u) [CommRing R] (x : R),
    (∀ f : Polynomial R, (evalRingHom x) f = f.eval x) ∧
    (∀ a, (evalRingHom x) (C a) = a) ∧ (evalRingHom x) X = x ∧
    ∀ Φ : Polynomial R →+* R,
      (∀ a, Φ (C a) = a) → Φ X = x → Φ = evalRingHom x

/-- Substitution into a noncommutative polynomial ring retains commutation
with the constant coefficients. -/
def ConditionalSubstitution : Prop :=
  ∀ (R : Type u) [Ring R] (g : Polynomial R),
    (∀ a, Commute g (C a)) →
      ∃! Φ : Polynomial R →+* Polynomial R,
        (∀ a, Φ (C a) = C a) ∧ Φ X = g ∧ ∀ f, Φ f = f.comp g

/-- Over a commutative ring ordinary substitution is the unique extension
with coefficient homomorphism C and target R[X]. -/
def CommutativeSubstitution : Prop :=
  ∀ (R : Type u) [CommRing R] (g : Polynomial R),
    (∀ f : Polynomial R, (compRingHom g) f = f.comp g) ∧
    (∀ a, (compRingHom g) (C a) = C a) ∧ (compRingHom g) X = g ∧
    ∀ Φ : Polynomial R →+* Polynomial R,
      (∀ a, Φ (C a) = C a) → Φ X = g → Φ = compRingHom g

end Specs.D07.Ch11.EvaluationUniversal
