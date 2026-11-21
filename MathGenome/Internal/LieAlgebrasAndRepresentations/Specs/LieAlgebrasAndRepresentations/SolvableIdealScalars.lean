import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.LieTheorem
import Mathlib.Algebra.Lie.IdealOperations

/-! The consequence of Lie's theorem at source lines 714–726.
The chapter convention (lines 600–603) makes both the algebra and its
representation finite dimensional. A linear character is a linear functional
vanishing on brackets. The last conclusion concerns every element of the
commutator ideal, not only its bracket generators. -/

universe u v w

namespace Specs.LieAlgebrasAndRepresentations.SolvableIdealScalars

def solvable_ideal_scalars_type : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {G : Type v} [LieRing G] [LieAlgebra k G] [Module.Finite k G]
    {V : Type w} [AddCommGroup V] [Module k V]
    [LieRingModule G V] [LieModule k G V] [Module.Finite k V]
    [Nontrivial V] [LieModule.IsIrreducible k G V]
    (r : LieIdeal k G) [LieAlgebra.IsSolvable r],
    ∃ χ : Module.Dual k r,
      (∀ a b : r, χ ⁅a, b⁆ = 0) ∧
      (∀ (a : r) (v : V), ⁅a, v⁆ = χ a • v) ∧
      (∀ z ∈ (⁅(⊤ : LieIdeal k G), r⁆ : LieIdeal k G),
        ∀ v : V, ⁅z, v⁆ = 0)

end Specs.LieAlgebrasAndRepresentations.SolvableIdealScalars
