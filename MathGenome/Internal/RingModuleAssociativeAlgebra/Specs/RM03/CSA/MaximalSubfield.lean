import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.SeparableSubfield

/-! Specifications for RM03-C04.09. -/

namespace Specs.RM03.CSA

universe u v

set_option linter.checkUnivs false in
def IsMaximalSubfieldType :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D],
    Subalgebra k D → Prop

/-- A maximal subfield has the inherited operations, contains the base field,
and has no strictly larger subfield in the division algebra. -/
def isMaximalSubfield {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    (E : Subalgebra k D) : Prop :=
  IsField E ∧ ∀ F : Subalgebra k D, IsField F → E ≤ F → F ≤ E

def MaximalSubfieldIffCentralizerEq : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    (_hD : isCentralDivision k D) (E : Subalgebra k D), IsField E →
    (isMaximalSubfield E ↔ Subalgebra.centralizer k (E : Set D) = E)

def MaximalSubfieldIffDegree : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    (_hD : isCentralDivision k D) (E : Subalgebra k D), IsField E →
    (isMaximalSubfield E ↔ Module.finrank k E = degree k D)

def MaximalSubfieldSplits : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    (_hD : isCentralDivision k D) (E : Subalgebra k D) (hE : isMaximalSubfield E),
    letI := hE.1.toField
    Nonempty (baseChange k E D ≃ₐ[E] Matrix (Fin (degree k D)) (Fin (degree k D)) E)

def ExistsSeparableMaximalSubfield : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D],
    isCentralDivision k D →
    ∃ E : Subalgebra k D, isMaximalSubfield E ∧ Algebra.IsSeparable k E ∧
      Module.finrank k E = degree k D

end Specs.RM03.CSA
