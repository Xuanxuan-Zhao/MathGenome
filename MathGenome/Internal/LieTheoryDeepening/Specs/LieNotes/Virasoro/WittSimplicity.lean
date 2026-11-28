import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.WittAlgebra
import Mathlib.Algebra.Lie.Semisimple.Defs

namespace LieNotes.Virasoro.WittSpec

/-- The complex Laurent derivation Lie algebra is nonabelian and has no proper nonzero ideals. -/
def Simplicity : Prop :=
  LieAlgebra.IsSimple ℂ Witt

/-- The complex Laurent derivation Lie algebra equals its derived algebra. -/
def Perfectness : Prop :=
  LieAlgebra.derivedSeries ℂ Witt 1 = ⊤

end LieNotes.Virasoro.WittSpec
