import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.TraceCriterion
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SolvableRadical
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.KillingCriterion

/-! LA-B05: the Killing criterion with the source's radical definition
of semisimplicity. The Killing form is the trace of the product of adjoint
operators, inherited from LA-B04. All conclusions include the zero algebra. -/

universe u v
namespace LieAlgebrasAndRepresentations

variable (k : Type u) (L : Type v) [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

theorem killingForm_symmetric (x y : L) :
    killingForm k L x y = killingForm k L y x :=
  LieModule.traceForm_comm k L L x y

theorem killingForm_invariant (x y z : L) :
    killingForm k L ⁅x, y⁆ z = killingForm k L x ⁅y, z⁆ :=
  LieModule.traceForm_apply_lie_apply k L L x y z

/-- The adjoint action of an ideal on the quotient vanishes, so its own
Killing form is precisely the restriction of the ambient Killing form. -/
theorem killingForm_restrict_ideal (I : LieIdeal k L) (x y : I) :
    killingForm k I x y = killingForm k L (x : L) (y : L) := by
  exact congrArg (fun B : LinearMap.BilinForm k I => B x y) (I.killingForm_eq k L)

/-- This is a conclusion about the solvable radical, not an alternative
assumption defining semisimplicity. Mathlib's `IsKilling` is bridged explicitly
from nondegeneracy, and its `HasTrivialRadical` means the actual radical is zero. -/
theorem killingForm_nondegenerate_iff_radical_eq_bot :
    (killingForm k L).Nondegenerate ↔ radical k L = ⊥ := by
  constructor
  · intro h
    haveI : LieAlgebra.IsKilling k L := ⟨by
      apply le_bot_iff.mp
      intro x hx
      have hx0 : x = 0 := h.1 x (fun y =>
        (killingForm_symmetric k L x y).trans
          ((LieIdeal.mem_killingCompl k L ⊤).mp hx y (LieSubmodule.mem_top y)))
      simpa only [LieSubmodule.mem_bot] using hx0⟩
    exact LieAlgebra.radical_eq_bot
  · intro h
    haveI : LieAlgebra.HasTrivialRadical k L := ⟨h⟩
    exact LieAlgebra.IsKilling.killingForm_nondegenerate k L

theorem semisimple_iff_killingForm_nondegenerate :
    IsSemisimple k L ↔ (killingForm k L).Nondegenerate :=
  (killingForm_nondegenerate_iff_radical_eq_bot k L).symm

end LieAlgebrasAndRepresentations
