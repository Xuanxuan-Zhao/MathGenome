import MathGenome.Internal.Specs.D07.Ch11.PolynomialDefinition
import Mathlib.Algebra.Polynomial.Coeff

/-!
Independent specification of K07.11.polynomial_arithmetic
(paper.tex:2164–2185; chapters/M07.11.tex:19–40).

The operations below are the canonical operations on the formal finite
coefficient sequences `Polynomial R` used in the upstream specification.
The ring-structure assertion retains those operations, including the whole
additive group. No commutativity or nontriviality of `R` is implicit.
-/

universe u

namespace Specs.D07.Ch11.PolynomialArithmetic

open Polynomial

def CoefficientAddition : Prop :=
  ∀ (R : Type u) [Ring R] (f g : Polynomial R) (n : ℕ),
    (f + g).coeff n = f.coeff n + g.coeff n

def CoefficientNegation : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R) (n : ℕ),
    (-f).coeff n = -f.coeff n

/-- `antidiagonal n` consists of the ordered pairs `(i,j)` with `i+j=n`.
The order of the two coefficient factors is retained. -/
def CoefficientMultiplication : Prop :=
  ∀ (R : Type u) [Ring R] (f g : Polynomial R) (n : ℕ),
    (f * g).coeff n =
      ∑ ij ∈ Finset.antidiagonal n, f.coeff ij.1 * g.coeff ij.2

def SupportAddition : Prop :=
  ∀ (R : Type u) [Ring R] (f g : Polynomial R),
    (f + g).support ⊆ f.support ∪ g.support

def SupportNegation : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R),
    (-f).support = f.support

/-- The support of a product is contained in the finite set of pairwise
sums of support indices; equality is not asserted in rings with cancellation
or zero divisors. -/
def SupportMultiplication : Prop :=
  ∀ (R : Type u) [Ring R] (f g : Polynomial R),
    (f * g).support ⊆
      (f.support ×ˢ g.support).image (fun ij : ℕ × ℕ => ij.1 + ij.2)

def FiniteSupportClosure : Prop :=
  ∀ (R : Type u) [Ring R] (f g : Polynomial R),
    (Function.support (fun n => (f + g).coeff n)).Finite ∧
    (Function.support (fun n => (-f).coeff n)).Finite ∧
    (Function.support (fun n => (f * g).coeff n)).Finite

/-- These very operations, rather than unspecified operations on the same
underlying set, form a ring. The retained additive group includes zero and
additive inverse, and the retained `One` is `C(1)`. -/
def PolynomialRingStructure : Prop :=
  ∀ (R : Type u) [Ring R],
    ∃ s : Ring (Polynomial R),
      s.toAddCommGroup = (inferInstance : AddCommGroup (Polynomial R)) ∧
      s.toMul = (inferInstance : Mul (Polynomial R)) ∧
      s.toOne = (inferInstance : One (Polynomial R))

/-- Explicit associativity, two-sided constant identity and distributivity
for the coefficientwise/convolution operations. -/
def MultiplicativeLaws : Prop :=
  ∀ (R : Type u) [Ring R] (f g h : Polynomial R),
    (f * g) * h = f * (g * h) ∧
    C (1 : R) * f = f ∧ f * C (1 : R) = f ∧
    f * (g + h) = f * g + f * h ∧
    (f + g) * h = f * h + g * h

/-- The constant-polynomial function is a unital ring homomorphism. -/
def ConstantRingHomomorphism : Prop :=
  ∀ (R : Type u) [Ring R],
    ∃ c : R →+* Polynomial R, ∀ a, c a = C a

/-- With commutative coefficients the same ring is commutative. -/
def PolynomialCommutativeRingStructure : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ s : CommRing (Polynomial R), s.toRing = (inferInstance : Ring (Polynomial R))

/-- Both products with a constant have their sole possible nonzero
coefficient at index one, even over a noncommutative ring. -/
def IndeterminateConstantCoefficients : Prop :=
  ∀ (R : Type u) [Ring R] (a : R) (n : ℕ),
    (X * C a).coeff n = (if n = 1 then a else 0) ∧
    (C a * X).coeff n = (if n = 1 then a else 0)

def IndeterminateCommutesConstants : Prop :=
  ∀ (R : Type u) [Ring R] (a : R), X * C a = C a * X

def IndeterminateCentral : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R), X * f = f * X

end Specs.D07.Ch11.PolynomialArithmetic
