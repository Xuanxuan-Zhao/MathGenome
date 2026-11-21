import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.DaniellStoneRepresentation
import MathGenome.Internal.RealAnalysis.D11.Ch23.LevelCylinderIntegrals
import MathGenome.Internal.RealAnalysis.D11.Ch23.LocalizedSigmaRingUniqueness

/-! Daniell–Stone existence and uniqueness on R_V (paper.tex:6288–6294).
The cylinder construction supplies the representing measure on A_V.
Localized uniqueness compares it with every other integrable representation.
Both prerequisites apply to an arbitrary type, including the empty type.
-/

open MeasureTheory
universe u

namespace D11.Ch23.DaniellStoneRepresentation

/-- Existence on A_V and uniqueness precisely on the positive-level sigma-ring. -/
theorem daniell_stone_representation :
    _root_.Specs.D11.Ch23.DaniellStoneRepresentation.daniell_stone_representation := by
  intro X V hV hStone L hL
  letI : MeasurableSpace X := positiveLevelMeasurableSpace V
  refine ⟨levelCylinderMeasure V L, ?_, ?_⟩
  · exact levelCylinder_integral_representation V hV hStone L hL
  · intro ν hν A hA
    exact LocalizedSigmaRingUniqueness.localized_sigma_ring_uniqueness
      V hV hStone L hL (levelCylinderMeasure V L) ν
      (fun f => (levelCylinder_integral_representation V hV hStone L hL f).2)
      hν A hA

end D11.Ch23.DaniellStoneRepresentation
