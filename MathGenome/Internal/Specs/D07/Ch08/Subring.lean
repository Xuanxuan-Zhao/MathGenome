import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import MathGenome.Internal.Specs.D07.Ch08.RingDefinition

/-!
Independent specification for K07.08.subring, paper.tex:1273–1281.
Rings are associative; neither commutativity nor nontriviality is imposed.
The nonunital criterion also applies when the ambient ring has no identity.
`Subring` and `NonUnitalSubring` are the canonical bundled objects. The
structure-existence statements explicitly require the inherited operations.
-/

universe u

namespace Specs.D07.Ch08.Subring

/-- Closure under precisely the two binary operations used in the source test. -/
def SubMulClosed {R : Type u} [Sub R] [Mul R] (S : Set R) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, a - b ∈ S) ∧
  (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)

def UnitalConditions {R : Type u} [Ring R] (S : Set R) : Prop :=
  (1 : R) ∈ S ∧ SubMulClosed S

def NonUnitalConditions {R : Type u} [NonUnitalRing R] (S : Set R) : Prop :=
  S.Nonempty ∧ SubMulClosed S

/-- The additive closure consequences are conclusions, not extra assumptions. -/
def AdditiveClosure {R : Type u} [AddGroup R] (S : Set R) : Prop :=
  (0 : R) ∈ S ∧ (∀ a ∈ S, -a ∈ S) ∧ (∀ a ∈ S, ∀ b ∈ S, a + b ∈ S)

def UnitalSubringCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (S : Set R),
    UnitalConditions S ↔ ∃ T : _root_.Subring R, (T : Set R) = S

def NonUnitalSubringCharacterization : Prop :=
  ∀ (R : Type u) [NonUnitalRing R] (S : Set R),
    NonUnitalConditions S ↔ ∃ T : _root_.NonUnitalSubring R, (T : Set R) = S

def UnitalClosureConsequences : Prop :=
  ∀ (R : Type u) [Ring R] (S : Set R), UnitalConditions S → AdditiveClosure S

def NonUnitalClosureConsequences : Prop :=
  ∀ (R : Type u) [NonUnitalRing R] (S : Set R),
    NonUnitalConditions S → AdditiveClosure S

/-- All ring axioms hold on the subset with exactly the ambient operations. -/
def UnitalInheritedStructure : Prop :=
  ∀ (R : Type u) [Ring R] (S : Set R), UnitalConditions S →
    ∃ s : Ring S, letI : Ring S := s
      ((0 : S) : R) = 0 ∧ ((1 : S) : R) = 1 ∧
      (∀ a b : S, ((a + b : S) : R) = (a : R) + (b : R)) ∧
      (∀ a : S, ((-a : S) : R) = -(a : R)) ∧
      (∀ a b : S, ((a - b : S) : R) = (a : R) - (b : R)) ∧
      (∀ a b : S, ((a * b : S) : R) = (a : R) * (b : R))

/-- The analogous conclusion requires no choice of a multiplicative identity. -/
def NonUnitalInheritedStructure : Prop :=
  ∀ (R : Type u) [NonUnitalRing R] (S : Set R), NonUnitalConditions S →
    ∃ s : NonUnitalRing S, letI : NonUnitalRing S := s
      ((0 : S) : R) = 0 ∧
      (∀ a b : S, ((a + b : S) : R) = (a : R) + (b : R)) ∧
      (∀ a : S, ((-a : S) : R) = -(a : R)) ∧
      (∀ a b : S, ((a - b : S) : R) = (a : R) - (b : R)) ∧
      (∀ a b : S, ((a * b : S) : R) = (a : R) * (b : R))

/-- The actual subset denoted by `2ℤ`, with multiplication inherited from `ℤ`. -/
def evenIntegers : Set ℤ := {z | ∃ k : ℤ, z = 2 * k}

def EvenIntegersNonUnitalSubring : Prop :=
  ∃ T : _root_.NonUnitalSubring ℤ, (T : Set ℤ) = evenIntegers

/-- Excludes an identity of its own, not merely the ambient identity `1`. -/
def EvenIntegersNoIdentity : Prop :=
  ¬ ∃ e : ℤ, e ∈ evenIntegers ∧
    ∀ x : ℤ, x ∈ evenIntegers → e * x = x ∧ x * e = x

def EvenIntegersNotUnitalSubring : Prop :=
  ¬ ∃ T : _root_.Subring ℤ, (T : Set ℤ) = evenIntegers

end Specs.D07.Ch08.Subring
