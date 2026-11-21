import Mathlib.Algebra.Ring.Pi
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.ZMod.Defs

/-!
Independent specification of K07.08.basic_examples, paper.tex:1192–1209.
Products may have arbitrary index types and noncommutative or trivial factors.
The operation predicates below require the ring structure to retain the given
addition, multiplication, additive inverse, zero and one. Thus an unrelated
ring structure on the same underlying type does not meet the specification.

`ZMod n` is the canonical residue-class model. Surjectivity of the integer
representative map and its exact equality criterion identify this model with
integers modulo divisibility by n. The operation formulas specify descent
from the integers, in addition to the ring axioms and well-definedness.
-/

universe u v

namespace Specs.D07.Ch08.BasicExamples

/-- A unital associative ring with all five given primitive operations. -/
def RingOnGivenOperations (R : Type u) [Add R] [Mul R] [Neg R] [Zero R] [One R] : Prop :=
  ∃ s : Ring R, s.toAdd = (inferInstance : Add R) ∧ s.toMul = (inferInstance : Mul R) ∧
    s.toNeg = (inferInstance : Neg R) ∧ s.toZero = (inferInstance : Zero R) ∧ s.toOne = (inferInstance : One R)

/-- The commutative version, again retaining the given operations. -/
def CommRingOnGivenOperations (R : Type u) [Add R] [Mul R] [Neg R] [Zero R] [One R] : Prop :=
  ∃ s : CommRing R, s.toAdd = (inferInstance : Add R) ∧ s.toMul = (inferInstance : Mul R) ∧
    s.toNeg = (inferInstance : Neg R) ∧ s.toZero = (inferInstance : Zero R) ∧ s.toOne = (inferInstance : One R)

/-- The arithmetic structures are the usual integer, rational, real and
complex operations; these structures are declared prior foundations. -/
def ArithmeticRings : Prop :=
  CommRingOnGivenOperations ℤ ∧ CommRingOnGivenOperations ℚ ∧
    CommRingOnGivenOperations ℝ ∧ CommRingOnGivenOperations ℂ

/-- Arbitrary dependent products of rings are rings with their given
coordinatewise operations, with no commutativity/nontriviality assumption. -/
def ProductRing : Prop :=
  ∀ (I : Type u) (R : I → Type v) [∀ i, Ring (R i)],
    RingOnGivenOperations (∀ i, R i)

/-- All primitive product operations are computed coordinatewise. -/
def ProductOperations : Prop :=
  ∀ (I : Type u) (R : I → Type v) [∀ i, Ring (R i)]
    (a b : ∀ i, R i) (i : I),
    (a + b) i = a i + b i ∧ (a * b) i = a i * b i ∧
      (-a) i = -(a i) ∧ (0 : ∀ i, R i) i = 0 ∧ (1 : ∀ i, R i) i = 1

/-- The function ring is the constant-family specialization of the product. -/
def FunctionRing : Prop :=
  ∀ (X : Type u) (R : Type v) [Ring R], RingOnGivenOperations (X → R)

/-- In particular, function multiplication is pointwise. -/
def FunctionMultiplication : Prop :=
  ∀ (X : Type u) (R : Type v) [Ring R] (f g : X → R) (x : X),
    (f * g) x = f x * g x

/-- On any empty domain there is exactly one function, including when the
coefficient ring is nontrivial. -/
def EmptyFunctions : Prop :=
  ∀ (X : Type u) (R : Type v) [Ring R] [IsEmpty X], ∃! _f : X → R, True

/-- A nonempty domain and nontrivial coefficient ring give distinct constant
zero/one functions and a nontrivial function ring. -/
def NontrivialFunctions : Prop :=
  ∀ (X : Type u) (R : Type v) [Ring R] [Nonempty X] [Nontrivial R],
    (0 : X → R) ≠ 1 ∧ Nontrivial (X → R)

/-- The two divisibility computations proving representative independence. -/
def RepresentativesCompatible : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ a a' b b' : ℤ,
    (n : ℤ) ∣ a - a' → (n : ℤ) ∣ b - b' →
    (n : ℤ) ∣ (a + b) - (a' + b') ∧ (n : ℤ) ∣ a * b - a' * b'

/-- Every residue has an integer representative. -/
def ResidueRepresentatives : Prop :=
  ∀ n : ℕ, 1 ≤ n → Function.Surjective ((↑) : ℤ → ZMod n)

/-- The representative map has exactly congruence modulo n as its fibers. -/
def ResidueClassEquality : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ a b : ℤ,
    (a : ZMod n) = (b : ZMod n) ↔ (n : ℤ) ∣ a - b

/-- Addition, multiplication, inverses and identities descend from ℤ. -/
def ResidueOperations : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ a b : ℤ, ((a + b : ℤ) : ZMod n) = (a : ZMod n) + (b : ZMod n)) ∧
    (∀ a b : ℤ, ((a * b : ℤ) : ZMod n) = (a : ZMod n) * (b : ZMod n)) ∧
    (∀ a : ℤ, ((-a : ℤ) : ZMod n) = -(a : ZMod n)) ∧
    ((0 : ℤ) : ZMod n) = 0 ∧ ((1 : ℤ) : ZMod n) = 1

/-- The descended operations satisfy all commutative unital ring axioms. -/
def ResidueRing : Prop :=
  ∀ n : ℕ, 1 ≤ n → CommRingOnGivenOperations (ZMod n)

/-- The modulus-one boundary is the one-element zero ring. -/
def ModulusOne : Prop :=
  (0 : ZMod 1) = 1 ∧ ∃! _z : ZMod 1, True

end Specs.D07.Ch08.BasicExamples
