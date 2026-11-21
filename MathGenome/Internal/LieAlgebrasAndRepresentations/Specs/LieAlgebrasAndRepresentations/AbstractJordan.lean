import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.LinearJordan
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical

/-! LA-B07, source lines 954–999. By the chapter convention (lines 597–600),
the algebra is finite dimensional and the structure theorem uses characteristic
zero. Semisimplicity means vanishing solvable radical. Semisimplicity of an
endomorphism is geometric, as in LA-B03. The zero algebra is included. -/

universe u v

namespace LieAlgebrasAndRepresentations

/-- The abstract additive Jordan decomposition in the original Lie algebra. -/
def IsAbstractJordanDecomposition {k : Type u} [Field k]
    {L : Type v} [LieRing L] [LieAlgebra k L] (x s n : L) : Prop :=
  x = s + n ∧ ⁅s, n⁆ = 0 ∧
    IsAbsolutelySemisimple (LieAlgebra.ad k L s) ∧
    IsNilpotent (LieAlgebra.ad k L n)

end LieAlgebrasAndRepresentations

namespace Specs.LieAlgebrasAndRepresentations.AbstractJordan

open _root_.LieAlgebrasAndRepresentations
open SolvableRadical (IsSemisimple_value)

/-- Existence and uniqueness among all commuting semisimple/nilpotent pairs. -/
def abstract_jordan_decomposition_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L → ∀ x : L,
      ∃ s n : L, IsAbstractJordanDecomposition (k := k) x s n ∧
        ∀ s' n' : L, IsAbstractJordanDecomposition (k := k) x s' n' →
          s' = s ∧ n' = n

/-- Every element commuting with x commutes with each of its two parts. -/
def abstract_jordan_centralizer_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    IsSemisimple_value k L → ∀ x s n : L,
      IsAbstractJordanDecomposition (k := k) x s n →
        ∀ y : L, ⁅x, y⁆ = 0 → ⁅s, y⁆ = 0 ∧ ⁅n, y⁆ = 0

end Specs.LieAlgebrasAndRepresentations.AbstractJordan
