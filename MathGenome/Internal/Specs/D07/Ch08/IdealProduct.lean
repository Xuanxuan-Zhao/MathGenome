import MathGenome.Internal.Specs.D07.Ch08.IdealSumIntersection
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
Independent specification of K07.08.ideal_product, paper.tex:1368–1379.
All general statements concern two-sided ideals in arbitrary associative
unital rings, including the zero ring. Lists express finite sums, permitting
the empty sum and repetitions. The factors are kept in their original order.
The membership theorem identifies Mathlib's product with the source's product,
rather than assuming this identification from the notation.
-/

universe u

namespace Specs.D07.Ch08.IdealProduct

/-- Exactly a finite sum of products of elements of the two ideals. -/
def FiniteProductSum {R : Type u} [Ring R] (I J : Ideal R) (x : R) : Prop :=
  ∃ terms : List (I × J), (terms.map fun p => (p.1 : R) * (p.2 : R)).sum = x

/-- The corresponding finite sums of three factors. -/
def FiniteTripleSum {R : Type u} [Ring R] (I J K : Ideal R) (x : R) : Prop :=
  ∃ terms : List (I × J × K),
    (terms.map fun p => ((p.1 : R) * (p.2.1 : R)) * (p.2.2 : R)).sum = x

def ProductDescription : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R),
    I.IsTwoSided → J.IsTwoSided →
      (I * J).IsTwoSided ∧ (∀ x, x ∈ I * J ↔ FiniteProductSum I J x)

/-- Addition, additive inverses, and absorption on both sides for the
explicit set of finite sums. -/
def ProductClosure : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R),
    I.IsTwoSided → J.IsTwoSided →
      FiniteProductSum I J 0 ∧
      (∀ x y, FiniteProductSum I J x → FiniteProductSum I J y →
        FiniteProductSum I J (x + y)) ∧
      (∀ x, FiniteProductSum I J x → FiniteProductSum I J (-x)) ∧
      (∀ r x, FiniteProductSum I J x → FiniteProductSum I J (r * x)) ∧
      (∀ x r, FiniteProductSum I J x → FiniteProductSum I J (x * r))

def ProductLeIntersection : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R),
    I.IsTwoSided → J.IsTwoSided → I * J ≤ I ⊓ J

def LeftDistributivity : Prop :=
  ∀ (R : Type u) [Ring R] (I J K : Ideal R),
    I.IsTwoSided → J.IsTwoSided → K.IsTwoSided →
      I * (J ⊔ K) = (I * J) ⊔ (I * K)

def RightDistributivity : Prop :=
  ∀ (R : Type u) [Ring R] (I J K : Ideal R),
    I.IsTwoSided → J.IsTwoSided → K.IsTwoSided →
      (I ⊔ J) * K = (I * K) ⊔ (J * K)

def Associativity : Prop :=
  ∀ (R : Type u) [Ring R] (I J K : Ideal R),
    I.IsTwoSided → J.IsTwoSided → K.IsTwoSided →
      (I * J) * K = I * (J * K)

def TripleProductDescription : Prop :=
  ∀ (R : Type u) [Ring R] (I J K : Ideal R),
    I.IsTwoSided → J.IsTwoSided → K.IsTwoSided →
      ∀ x, (x ∈ (I * J) * K ↔ FiniteTripleSum I J K x) ∧
        (x ∈ I * (J * K) ↔ FiniteTripleSum I J K x)

def IntegerCounterexample : Prop :=
  let I : Ideal ℤ := Ideal.span {2}
  let F : Ideal ℤ := Ideal.span {4}
  I * I = F ∧ I ⊓ I = I ∧ F ≠ I ⊓ I

/-- Two-sided ideals can have unequal products in the two orders. -/
def NoncommutativeCounterexample : Prop :=
  ∃ (R : Type) (_ : Ring R) (I J : Ideal R),
    I.IsTwoSided ∧ J.IsTwoSided ∧ I * J ≠ J * I

end Specs.D07.Ch08.IdealProduct
