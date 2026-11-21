import MathGenome.Internal.Specs.D07.Ch09.MaximalQuotient
import MathGenome.Internal.Specs.D07.Ch09.PrimeQuotient
import MathGenome.Internal.Specs.D07.Ch11.EvaluationUniversal
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps

/-!
Independent specifications for K07.09.maximal_prime_nonconverse,
paper.tex:1672–1684. Rings in this part of the chapter are commutative
and unital; the ambient zero ring is allowed. Prime and maximal ideals
are the canonical proper-ideal predicates. The concrete examples use
ordinary integers and formal polynomials, with the canonical quotient
ring operations. Divisibility by 2 expresses evenness of an integer.

The coefficient-shift statement records the polynomial used in the kernel
argument, including its coefficients. The quotient equivalence is required
to send the class of f to f(0), rather than merely identify two types.
-/

universe u

namespace Specs.D07.Ch09.MaximalPrimeNonconverse

open Polynomial

def FieldImpliesDomain : Prop :=
  ∀ (R : Type u) [CommRing R], IsField R → IsDomain R

def MaximalImpliesPrime : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Ideal R), M.IsMaximal → M.IsPrime

def IntegerDomainNotField : Prop := IsDomain ℤ ∧ ¬ IsField ℤ

def IntegerZeroPrimeNotMaximal : Prop :=
  (⊥ : Ideal ℤ).IsPrime ∧ ¬ (⊥ : Ideal ℤ).IsMaximal

/-- Shift every positive-index coefficient down by one. -/
def ShiftedDecomposition : Prop :=
  ∀ f : Polynomial ℤ, ∃ g : Polynomial ℤ,
    (∀ n : ℕ, g.coeff n = f.coeff (n + 1)) ∧
      f = C (f.eval 0) + X * g

def EvaluationZeroIffMultiple : Prop :=
  ∀ f : Polynomial ℤ, f.eval 0 = 0 ↔ (X : Polynomial ℤ) ∣ f

def EvaluationSurjective : Prop :=
  Function.Surjective (evalRingHom (0 : ℤ))

def EvaluationKernel : Prop :=
  RingHom.ker (evalRingHom (0 : ℤ)) =
    Ideal.span ({X} : Set (Polynomial ℤ))

def QuotientEquivalence : Prop :=
  ∃ e : (Polynomial ℤ ⧸ Ideal.span ({X} : Set (Polynomial ℤ))) ≃+* ℤ,
    ∀ f : Polynomial ℤ, e (Ideal.Quotient.mk _ f) = f.eval 0

def QuotientDomainNotField : Prop :=
  IsDomain (Polynomial ℤ ⧸ Ideal.span ({X} : Set (Polynomial ℤ))) ∧
    ¬ IsField (Polynomial ℤ ⧸ Ideal.span ({X} : Set (Polynomial ℤ)))

def XIdealNonzeroPrimeNotMaximal : Prop :=
  (Ideal.span ({X} : Set (Polynomial ℤ)) : Ideal (Polynomial ℤ)) ≠ ⊥ ∧
    (Ideal.span ({X} : Set (Polynomial ℤ))).IsPrime ∧
    ¬ (Ideal.span ({X} : Set (Polynomial ℤ))).IsMaximal

/-- The ideal (2,X) consists of the displayed linear combinations. -/
def TwoXRepresentation : Prop :=
  ∀ f : Polynomial ℤ,
    f ∈ Ideal.span ({C 2, X} : Set (Polynomial ℤ)) ↔
      ∃ a b : Polynomial ℤ, f = C 2 * a + X * b

def TwoXEvenConstant : Prop :=
  ∀ f : Polynomial ℤ,
    f ∈ Ideal.span ({C 2, X} : Set (Polynomial ℤ)) → (2 : ℤ) ∣ f.coeff 0

def StrictIdealChain : Prop :=
  (Ideal.span ({X} : Set (Polynomial ℤ)) : Ideal (Polynomial ℤ)) <
      Ideal.span ({C 2, X} : Set (Polynomial ℤ)) ∧
    (Ideal.span ({C 2, X} : Set (Polynomial ℤ)) : Ideal (Polynomial ℤ)) < ⊤

def StrictnessWitnesses : Prop :=
  (C 2 : Polynomial ℤ) ∉ Ideal.span ({X} : Set (Polynomial ℤ)) ∧
    (C 2 : Polynomial ℤ) ∈ Ideal.span ({C 2, X} : Set (Polynomial ℤ)) ∧
    (1 : Polynomial ℤ) ∉ Ideal.span ({C 2, X} : Set (Polynomial ℤ))

end Specs.D07.Ch09.MaximalPrimeNonconverse
