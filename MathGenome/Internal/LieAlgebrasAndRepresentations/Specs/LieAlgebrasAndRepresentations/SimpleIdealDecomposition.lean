import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.KillingCriterion
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Lie.DirectSum

/-! Independent specification of LA-B06, source lines 915–952.
The chapter convention (lines 600–603) gives finite dimension and characteristic
zero. Semisimplicity is the upstream vanishing-radical definition. The simple
factors are actual ideals of the original algebra, and `IsSimple` includes
nonabelianness. Internal direct sum means that the canonical sum map from the
external direct sum is bijective; it allows the empty family. -/

universe u v
open scoped Classical
namespace Specs.LieAlgebrasAndRepresentations.SimpleIdealDecomposition

open SolvableRadical (IsSemisimple_value)

variable (k : Type u) (L : Type v) [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

def semisimple_structure_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L → LieAlgebra.IsSemisimple k L

def ideal_isCompl_killingCompl_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L → ∀ I : LieIdeal k L, IsCompl I I.killingCompl

def semisimple_center_eq_bot_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L → LieAlgebra.center k L = ⊥

def semisimple_perfect_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L → ⁅(⊤ : LieIdeal k L), (⊤ : LieIdeal k L)⁆ = ⊤

def simple_ideal_decomposition_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L →
      ∃ S : Set (LieIdeal k L), S.Finite ∧ S = {I | IsAtom I} ∧
        (∀ I ∈ S, LieAlgebra.IsSimple k I) ∧
        DirectSum.IsInternal (fun I : S => I.val.toSubmodule)

/-- The direct sum is an isomorphism of Lie algebras, with the original
inclusion on each component, not just an abstract vector-space equivalence. -/
def simple_ideal_lie_decomposition_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L →
      ∃ S : Set (LieIdeal k L), S.Finite ∧ S = {I | IsAtom I} ∧
        (∀ I ∈ S, LieAlgebra.IsSimple k I) ∧
        ∃ e : DirectSum S (fun I => ↥I.val) ≃ₗ⁅k⁆ L,
          ∀ (I : S) (x : I.val),
            e (DirectSum.of (fun J : S => ↥J.val) I x) = (x : L)

def every_ideal_unique_sum_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L → ∀ I : LieIdeal k L,
      ∃! T : Set (LieIdeal k L), T ⊆ {J | IsAtom J} ∧ sSup T = I

/-- In the trivial algebra the family in the decomposition is empty, and only
in that case is it empty. -/
def simple_factors_empty_iff_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L → ({I : LieIdeal k L | IsAtom I} = ∅ ↔ Subsingleton L)

end Specs.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
