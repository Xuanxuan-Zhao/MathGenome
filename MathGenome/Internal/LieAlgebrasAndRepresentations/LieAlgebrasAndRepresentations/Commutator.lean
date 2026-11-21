import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Commutator

/-!
The associative-algebra and general-linear examples, LA-U01, source lines
200–203. All structures below are the canonical Mathlib structures;
these named definitions introduce no new instances.
-/

universe u v w

namespace LieAlgebrasAndRepresentations

attribute [local instance 100] LieRing.ofAssociativeRing

def commutator_lie_ring (A : Type v) [Ring A] : LieRing A :=
  LieRing.ofAssociativeRing

def commutator_lie_algebra (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A] : LieAlgebra k A :=
  LieAlgebra.ofAssociativeAlgebra

theorem commutator_bracket {A : Type v} [Ring A] (a b : A) :
    ⁅a, b⁆ = a * b - b * a :=
  LieRing.of_associative_ring_bracket a b

theorem commutator_axioms {k : Type u} [Field k]
    {A : Type v} [Ring A] [Algebra k A] (a b c : A) (t : k) :
    ⁅a, a⁆ = 0 ∧
    ⁅a, ⁅b, c⁆⁆ + ⁅b, ⁅c, a⁆⁆ + ⁅c, ⁅a, b⁆⁆ = 0 ∧
    ⁅a + b, c⁆ = ⁅a, c⁆ + ⁅b, c⁆ ∧
    ⁅a, b + c⁆ = ⁅a, b⁆ + ⁅a, c⁆ ∧
    ⁅t • a, b⁆ = t • ⁅a, b⁆ ∧ ⁅a, t • b⁆ = t • ⁅a, b⁆ :=
  ⟨lie_self a, lie_jacobi a b c, add_lie a b c, lie_add a b c,
    smul_lie t a b, lie_smul t a b⟩

def general_linear_lie_algebra (k : Type u) [Field k]
    (V : Type w) [AddCommGroup V] [Module k V] : LieAlgebra k (Module.End k V) :=
  LieAlgebra.ofAssociativeAlgebra

theorem general_linear_bracket_apply {k : Type u} [Field k]
    {V : Type w} [AddCommGroup V] [Module k V]
    (f g : Module.End k V) (v : V) : ⁅f, g⁆ v = f (g v) - g (f v) :=
  rfl

end LieAlgebrasAndRepresentations
