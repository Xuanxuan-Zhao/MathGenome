import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Independent specification of the inner-derivation part of LA-B07
(source lines 954–982). The chapter convention (lines 600–603) imposes
finite dimension and characteristic zero. Semisimplicity means that the
solvable radical vanishes, as in LA-B05. The adjoint map is the canonical
map from LA-A03, with values in the derivations of the original algebra.
No algebraic closure or nonzero-algebra hypothesis is imposed. -/

universe u v
namespace Specs.LieAlgebrasAndRepresentations.InnerDerivations

open SolvableRadical (IsSemisimple_value)
open ActionsDerivationsSemidirect (adjoint_value)

def adjoint_bijective_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L → Function.Bijective (adjoint_value k L)

/-- Existence and uniqueness of the element inducing each derivation. -/
def derivation_inner_unique_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L → ∀ D : LieDerivation k L L,
      ∃! x : L, adjoint_value k L x = D

/-- A Lie algebra isomorphism whose forward map is precisely the adjoint map. -/
def adjoint_isomorphism_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L →
      ∃ e : L ≃ₗ⁅k⁆ LieDerivation k L L, e.toLieHom = adjoint_value k L

end Specs.LieAlgebrasAndRepresentations.InnerDerivations
