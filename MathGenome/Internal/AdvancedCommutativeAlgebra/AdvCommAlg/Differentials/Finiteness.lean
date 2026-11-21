import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Finiteness
import Mathlib.RingTheory.Extension.Cotangent.Basic

/-! Finite generation and finite presentation of relative differentials (KD-13).
The canonical KaehlerDifferential is the Omega used in the universal interface.
-/

namespace AdvCommAlg.Differentials

universe u v

/-- Differentials of a finite type algebra form a finite module over that algebra. -/
theorem finite_of_finite_type : Specs.AdvCommAlg.Differentials.finiteOfFiniteType.{u,v} := by
  intro A B _ _ _ _
  exact KaehlerDifferential.finite A B

/-- Algebra finite presentation implies module finite presentation for differentials.
The library proof uses the conormal sequence for a finite polynomial presentation.
-/
theorem finite_presentation_of_finite_presentation :
    Specs.AdvCommAlg.Differentials.finitePresentationOfFinitePresentation.{u,v} := by
  intro A B _ _ _ _
  infer_instance

end AdvCommAlg.Differentials
