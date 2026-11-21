import MathGenome.Internal.Specs.D07.Ch08.RingDefinition
import Mathlib.Algebra.Ring.Equiv

/-!
Independent specification of K07.08.ring_homomorphism,
paper.tex:1283–1294. Rings are associative and unital; they need not be
commutative or nontrivial. The three source laws are compared with
`RingHom`, and isomorphisms are the canonical `RingEquiv` objects.
Integer multiples of one mean additive integer scalar multiplication.
-/

universe u v w

namespace Specs.D07.Ch08.RingHomomorphism

/-- Exactly the three preservation laws in the paper's definition. -/
structure UnitalHomLaws {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R → S) : Prop where
  map_add : ∀ a b, f (a + b) = f a + f b
  map_mul : ∀ a b, f (a * b) = f a * f b
  map_one : f 1 = 1

/-- Preserving the three operations is precisely being a bundled ring map. -/
def HomomorphismCharacterization : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R → S),
    UnitalHomLaws f ↔ ∃ φ : R →+* S, (φ : R → S) = f

def MapZero : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S),
    f 0 = 0

def MapNeg : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S) (a : R),
    f (-a) = -f a

def MapIntegerMultiplesOfOne : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S) (n : ℤ),
    f (n • (1 : R)) = n • (1 : S)

/-- Composition preserves addition, multiplication, and the identity. -/
def Composition : Prop :=
  ∀ (R : Type u) (S : Type v) (T : Type w) [Ring R] [Ring S] [Ring T]
    (f : R → S) (g : S → T),
    UnitalHomLaws f → UnitalHomLaws g → UnitalHomLaws (g ∘ f)

/-- A homomorphism gives an isomorphism of the entire rings exactly when
it is bijective, including surjectivity and not merely injectivity. -/
def IsomorphismCharacterization : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S),
    Function.Bijective f ↔ ∃ e : R ≃+* S, (e : R →+* S) = f

/-- Every two-sided inverse of a ring homomorphism preserves the three laws. -/
def InverseHomomorphism : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (f : R →+* S) (g : S → R),
    Function.LeftInverse g f → Function.RightInverse g f → UnitalHomLaws g

/-- The inverse equivalence has the source's inverse identities and laws. -/
def IsomorphismInverse : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (e : R ≃+* S),
    UnitalHomLaws (e.symm : S → R) ∧
      Function.LeftInverse e.symm e ∧ Function.RightInverse e.symm e

def ZeroMapNotUnital : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    [Nontrivial R] [Nontrivial S], ¬ UnitalHomLaws (fun _ : R => (0 : S))

end Specs.D07.Ch08.RingHomomorphism
