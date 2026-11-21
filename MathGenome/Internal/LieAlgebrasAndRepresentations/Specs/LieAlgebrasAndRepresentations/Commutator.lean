import Mathlib.Algebra.Lie.OfAssociative

/-!
LA-U01: notes/005/lie-algebras-and-representations.tex, lines 200–203.
The field and unital conventions are at lines 168–171; alternation in
characteristic two is explicit in the global conventions and LA-A01.
These interfaces use the existing associative-ring commutator structure.
The local instance activates Mathlib's reducible non-instance and does not
install a second Lie structure. No finite dimension or characteristic
restriction is imposed, including on the endomorphism example.
-/

universe u v w

namespace Specs.LieAlgebrasAndRepresentations.Commutator

attribute [local instance 100] LieRing.ofAssociativeRing

def commutator_lie_ring_type :=
  ∀ (A : Type v) [Ring A], LieRing A

def commutator_lie_ring_value (A : Type v) [Ring A] : LieRing A :=
  LieRing.ofAssociativeRing

def commutator_lie_algebra_type :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A], LieAlgebra k A

def commutator_lie_algebra_value (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A] : LieAlgebra k A :=
  LieAlgebra.ofAssociativeAlgebra

def commutator_bracket_type :=
  ∀ {A : Type v} [Ring A] (a b : A), ⁅a, b⁆ = a * b - b * a

/-- Alternation, cyclic Jacobi, and bilinearity over the original field. -/
def commutator_axioms_type :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    (a b c : A) (t : k),
  ⁅a, a⁆ = 0 ∧
    ⁅a, ⁅b, c⁆⁆ + ⁅b, ⁅c, a⁆⁆ + ⁅c, ⁅a, b⁆⁆ = 0 ∧
    ⁅a + b, c⁆ = ⁅a, c⁆ + ⁅b, c⁆ ∧
    ⁅a, b + c⁆ = ⁅a, b⁆ + ⁅a, c⁆ ∧
    ⁅t • a, b⁆ = t • ⁅a, b⁆ ∧ ⁅a, t • b⁆ = t • ⁅a, b⁆

def general_linear_lie_algebra_type :=
  ∀ (k : Type u) [Field k] (V : Type w) [AddCommGroup V] [Module k V],
    LieAlgebra k (Module.End k V)

def general_linear_lie_algebra_value (k : Type u) [Field k]
    (V : Type w) [AddCommGroup V] [Module k V] : LieAlgebra k (Module.End k V) :=
  LieAlgebra.ofAssociativeAlgebra

/-- Multiplication in End is composition, so this is the claimed commutator on gl(V). -/
def general_linear_bracket_apply_type :=
  ∀ {k : Type u} [Field k] {V : Type w} [AddCommGroup V] [Module k V]
    (f g : Module.End k V) (v : V), ⁅f, g⁆ v = f (g v) - g (f v)

end Specs.LieAlgebrasAndRepresentations.Commutator
