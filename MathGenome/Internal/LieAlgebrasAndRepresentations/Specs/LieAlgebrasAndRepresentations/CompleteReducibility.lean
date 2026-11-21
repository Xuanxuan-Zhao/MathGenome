import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.DirectSum.Module

/-! LA-C05 (source lines 1361–1389), under the section conventions at
lines 1184–1190: arbitrary characteristic-zero field, finite-dimensional
semisimple Lie algebra, and finite-dimensional modules. The complement is
an actual invariant subspace. The internal direct sum is the canonical sum
of inclusions of simple invariant subspaces, and its indexing set is finite.
The empty set is permitted, in particular for the zero module. -/

open scoped Classical
universe u v w
namespace Specs.LieAlgebrasAndRepresentations.CompleteReducibility

def invariant_complement_type : Prop :=
  ∀ (k : Type u) (g : Type v) (V : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [LieRingModule g V] [LieModule k g V],
    SolvableRadical.IsSemisimple_value k g →
    ∀ W : LieSubmodule k g V, ∃ C : LieSubmodule k g V, IsCompl W C

def finite_simple_decomposition_type : Prop :=
  ∀ (k : Type u) (g : Type v) (V : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [LieRingModule g V] [LieModule k g V],
    SolvableRadical.IsSemisimple_value k g →
    ∃ S : Set (LieSubmodule k g V), S.Finite ∧
      (∀ W ∈ S, LieModule.IsIrreducible k g W) ∧
      DirectSum.IsInternal (fun W : S => W.val.toSubmodule)

end Specs.LieAlgebrasAndRepresentations.CompleteReducibility
