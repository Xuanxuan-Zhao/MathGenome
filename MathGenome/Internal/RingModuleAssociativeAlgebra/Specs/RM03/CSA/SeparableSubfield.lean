import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Degree
import Mathlib.FieldTheory.Separable

/-! Specification for the embedded separable field in RM03-C04.05. -/

namespace Specs.RM03.CSA

universe u v

/-- The field operations and the scalar map are inherited from the given division algebra. -/
def ExistsSeparableSubfield : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D],
    isCentralDivision k D →
    ∃ E : Subalgebra k D, IsField E ∧ Algebra.IsSeparable k E ∧
      Module.finrank k E = degree k D

end Specs.RM03.CSA
