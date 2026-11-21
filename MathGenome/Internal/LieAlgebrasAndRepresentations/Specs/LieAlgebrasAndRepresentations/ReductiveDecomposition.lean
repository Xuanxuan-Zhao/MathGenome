import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical
import Mathlib.Algebra.Lie.Prod

/-! LA-I07, Lie volume, expanded lines 4267–4320, last assertion and its
converse. The conjugacy assertion is allocated separately. Reductive means
that the actual solvable radical equals the center. The internal direct sum
is a semisimple ideal complementary to the center as a vector space; the
second theorem explicitly realizes this as the canonical Lie product
isomorphism. No condition on the action of the center on representations is
introduced. Both zero summands are permitted. -/

universe u v
namespace Specs.LieAlgebrasAndRepresentations.ReductiveDecomposition

def IsReductive_value (k : Type u) (L : Type v) [Field k]
    [LieRing L] [LieAlgebra k L] : Prop :=
  SolvableRadical.radical_value k L = LieAlgebra.center k L

def IsReductive_type :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L], Prop

def reductive_iff_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsReductive_value k L ↔
      ∃ S : LieIdeal k L, SolvableRadical.IsSemisimple_value k S ∧
        IsCompl S.toSubmodule (LieAlgebra.center k L).toSubmodule

def center_direct_sum_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (S : LieIdeal k L),
    IsCompl S.toSubmodule (LieAlgebra.center k L).toSubmodule →
      ∃ e : (S × LieAlgebra.center k L) ≃ₗ⁅k⁆ L,
        ∀ (x : S) (z : LieAlgebra.center k L), e (x, z) = (x : L) + (z : L)

end Specs.LieAlgebrasAndRepresentations.ReductiveDecomposition
