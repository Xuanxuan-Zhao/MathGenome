import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.CantorSet
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.FatCantor

/-! Independent statement of the complete Cantor-sets proposition,
paper.tex:1025–1030. The middle-thirds set is the canonical set fixed in
`CantorSet`. Nullity is stated for the completed Euclidean Lebesgue measure
under the canonical real-line coordinate map. The prescribed-mass sets use
the same Euclidean line and completed measure as the upstream construction.
-/

open Set MeasureTheory
open scoped Cardinal ENNReal

namespace Specs.D11.Ch03.CantorSets

open _root_.D11.Ch03 _root_.D11.Ch03.CantorConstruction

/-- Both assertions of the original Cantor-sets proposition, with no
additional assumptions on the prescribed mass beyond `0 < α < 1`. -/
def cantor_sets : Prop :=
  (CantorSet.C_value ⊆ Icc 0 1 ∧
    IsCompact CantorSet.C_value ∧
    Perfect CantorSet.C_value ∧
    IsNowhereDense CantorSet.C_value ∧
    Cardinal.mk ↥CantorSet.C_value = 𝔠 ∧
    MeasurableSet[LebesgueMeasures.lebesgueSpace_value 1]
      (linePoint '' CantorSet.C_value) ∧
    LebesgueMeasures.lebesgue_value 1 (linePoint '' CantorSet.C_value) = 0) ∧
  ∀ α : ℝ, 0 < α → α < 1 →
    ∃ K : Set (Point 1),
      K ⊆ closedBox (fun _ => 0) (fun _ => 1) ∧
      IsClosed K ∧ IsNowhereDense K ∧
      MeasurableSet[LebesgueMeasures.lebesgueSpace_value 1] K ∧
      LebesgueMeasures.lebesgue_value 1 K = ENNReal.ofReal α

end Specs.D11.Ch03.CantorSets
