import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! Independent statement of paper.tex:915–921. Both errors are measured in
the full Carathéodory Lebesgue space. No finiteness assumption is made on E. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch03.GlobalClosedOpen

open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

def global_closed_open_approximation : Prop :=
  ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
    MeasurableSet[lebesgueSpace_value d] E →
    ∀ ε : ℝ, 0 < ε → ∃ F G : Set (Point d),
      IsClosed F ∧ IsOpen G ∧ F ⊆ E ∧ E ⊆ G ∧
        lebesgue_value d (E \ F) < ENNReal.ofReal ε ∧
        lebesgue_value d (G \ E) < ENNReal.ofReal ε

end Specs.D11.Ch03.GlobalClosedOpen
