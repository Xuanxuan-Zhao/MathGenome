import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.Presentation
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.CartanFreeness
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.TriangularGrading
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.UniversalAlgebra

namespace LieNotes.Contragredient.Presentation

open scoped Classical

/-- The universal algebra before taking the Cartan-disjoint quotient (KM03). -/
theorem universalAlgebra :
    Specs.LieNotes.Contragredient.UniversalAlgebra.UniversalAlgebraBeforeQuotient := by
  intro I A H _ _ _ R _hA
  exact ⟨definingRelations R, generated R, fun C E F => universalProperty R C E F,
    cartan_injective R, exists_triangularAdditionEquiv R, negative_isFree R, positive_isFree R,
    grade_isInternal R, cartan_mem_grade R, e_mem_grade R, f_mem_grade R,
    fun hx hy => lie_mem_grade R hx hy, fun _ _ => mem_grade R,
    grade_zero R, iSup_negative_grade R, iSup_positive_grade R⟩

end LieNotes.Contragredient.Presentation
