import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.TraceCriterion
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical

/-! Independent specification of LA-B05, source lines 865–907.
Chapter 2 assumes finite dimension (lines 600–603). Semisimplicity means
that the sum of the solvable ideals is zero, as in the upstream radical
specification. No nondegeneracy certificate is part of the hypotheses.
Scalar extension (lines 909–912) is separately assigned to LA-U04. -/

universe u v
namespace Specs.LieAlgebrasAndRepresentations.KillingCriterion

open TraceCriterion (killingForm_value)
open SolvableRadical (radical_value IsSemisimple_value)

def killingForm_symmetric_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] (x y : L),
    killingForm_value k L x y = killingForm_value k L y x

def killingForm_invariant_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] (x y z : L),
    killingForm_value k L ⁅x, y⁆ z = killingForm_value k L x ⁅y, z⁆

def killingForm_restrict_ideal_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (I : LieIdeal k L) (x y : I),
    killingForm_value k I x y = killingForm_value k L (x : L) (y : L)

def killingForm_nondegenerate_iff_radical_eq_bot_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    (killingForm_value k L).Nondegenerate ↔ radical_value k L = ⊥

def semisimple_iff_killingForm_nondegenerate_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L ↔ (killingForm_value k L).Nondegenerate

end Specs.LieAlgebrasAndRepresentations.KillingCriterion
