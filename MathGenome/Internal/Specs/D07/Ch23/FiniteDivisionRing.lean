import Mathlib.Algebra.Field.Defs
import Mathlib.Basic.Finite.Defs

/-!
Independent specifications for K07.23.finite_division_ring,
paper.tex:7387–7431.

`DivisionRing` includes associativity, a unit, nontriviality, and inverses
of nonzero elements, but does not assume commutativity. `Finite D` refers
to the underlying set. No scalar field or commutative-centralizer hypothesis
is required. The field conclusion preserves the entire given division-ring
structure, and its underlying set is still the same finite type `D`.
-/

universe u

namespace Specs.D07.Ch23.FiniteDivisionRing

/-- Multiplication in every finite division ring is commutative. -/
def Commutative : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Finite D] (a b : D), a * b = b * a

/-- The original finite division ring admits a field structure with exactly
its given operations, including its original inverse and division operations. -/
def FiniteField : Prop :=
  ∀ (D : Type u) [d : DivisionRing D] [Finite D],
    ∃ f : Field D, f.toDivisionRing = d

end Specs.D07.Ch23.FiniteDivisionRing
