import MathGenome.Internal.Specs.D07.Ch11.EvaluationUniversal
import MathGenome.Internal.Specs.D07.Ch11.RootBound
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
Independent specification of K07.11.polynomial_function, paper.tex:2806–2826.
The objects are formal `Polynomial R`, and their evaluation functions have
pointwise ring operations. Finite fields are arbitrary, with no chosen
classification or characteristic. The infinite case is every commutative
domain, without assuming it is a field. The nonzero elements are represented
by the literal subtype `{x : F // x ≠ 0}`.
-/

universe u

namespace Specs.D07.Ch11.PolynomialFunction

open Polynomial

/-- Multiplication by a nonzero element permutes precisely the nonzero elements. -/
def NonzeroMultiplicationPermutation : Prop :=
  ∀ (F : Type u) [Field F] (a : F) (ha : a ≠ 0),
    Function.Bijective (fun b : {x : F // x ≠ 0} =>
      (⟨a * b.val, mul_ne_zero ha b.property⟩ : {x : F // x ≠ 0}))

/-- The nonzero elements have cardinality q-1; their product is nonzero and
is unchanged by multiplying every factor by a nonzero a. -/
def NonzeroProductComparison : Prop := by
  classical
  exact ∀ (F : Type u) [Field F] [Fintype F],
    Fintype.card {x : F // x ≠ 0} = Fintype.card F - 1 ∧
    let P : F := ∏ b : {x : F // x ≠ 0}, b.val
    P ≠ 0 ∧ ∀ a : F, a ≠ 0 → P = a ^ (Fintype.card F - 1) * P

/-- Cancellation of the nonzero product gives the power identity. -/
def NonzeroPowerIdentity : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (a : F), a ≠ 0 →
    a ^ (Fintype.card F - 1) = 1

/-- This identity includes a=0. -/
def FinitePowerIdentity : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (a : F),
    a ^ Fintype.card F - a = 0

/-- A field has distinct elements zero and one, even in the finite case q=2. -/
def FiniteCardinality : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F], 2 ≤ Fintype.card F

/-- Formal coefficients distinguish the witness from the zero polynomial. -/
def WitnessCoefficients : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F],
    (X ^ Fintype.card F - X : Polynomial F).coeff (Fintype.card F) = 1 ∧
    (X ^ Fintype.card F - X : Polynomial F).coeff 1 = -1

/-- The witness is a nonzero formal polynomial, including in characteristic two. -/
def WitnessNonzero : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F],
    (X ^ Fintype.card F - X : Polynomial F) ≠ 0

/-- Nevertheless its evaluation function is identically zero. -/
def WitnessVanishes : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (a : F),
    (X ^ Fintype.card F - X : Polynomial F).eval a = 0

/-- Evaluation into the pointwise ring of functions is not injective. -/
def FiniteEvaluationNoninjective : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F],
    ¬ Function.Injective (RingHom.pi (fun a : F => evalRingHom a))

/-- Over an infinite domain, evaluation into that same function ring is injective. -/
def InfiniteEvaluationInjective : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [Infinite R],
    Function.Injective (RingHom.pi (fun a : R => evalRingHom a))

/-- Equivalently, coefficient equality and equality of evaluation functions
coincide under these hypotheses, although they are separate definitions. -/
def InfiniteEvaluationEquality : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [Infinite R] (f g : Polynomial R),
    (∀ a : R, f.eval a = g.eval a) ↔ f = g

end Specs.D07.Ch11.PolynomialFunction
