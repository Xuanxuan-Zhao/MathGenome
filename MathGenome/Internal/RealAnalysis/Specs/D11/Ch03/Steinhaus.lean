import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! Independent statement of paper.tex:1139–1143.
The real line is the shared Euclidean space `Point 1`. Its single coordinate
identifies the displayed set with the open interval `(-δ, δ)`. The hypothesis
uses the full Carathéodory Lebesgue sigma-algebra, with no finiteness assumption.
-/

open Set MeasureTheory
open scoped Pointwise

namespace Specs.D11.Ch03.Steinhaus

open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

def steinhaus : Prop :=
  ∀ E : Set (Point 1), MeasurableSet[lebesgueSpace_value 1] E →
    0 < lebesgue_value 1 E →
    ∃ δ : ℝ, 0 < δ ∧ {h : Point 1 | -δ < h 0 ∧ h 0 < δ} ⊆ E - E

end Specs.D11.Ch03.Steinhaus
