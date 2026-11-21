import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! Independent statements of paper.tex:1073–1088. Native real volume evaluates
its outer measure on every set. `NullMeasurableSet` is measurability for its
ordinary completion, not Borel measurability. The second statement uses the
shared covering construction and its full Carathéodory measurable space on
one-dimensional Euclidean space. Neither statement assumes that `B` is
measurable, bounded, or of finite outer measure. Choice is classical Lean choice. -/

open Set MeasureTheory

namespace Specs.D11.Ch03.PositiveOuterNonmeasurable

/-- The literal real-line statement, using the completed Borel Lebesgue space. -/
def positive_set_nonmeasurable_subset : Prop :=
  ∀ B : Set ℝ, 0 < volume B →
    ∃ V ⊆ B, ¬ NullMeasurableSet V (volume : Measure ℝ)

/-- The same conclusion for the shared one-dimensional covering construction. -/
def positive_outer_nonmeasurable_subset : Prop :=
  ∀ B : Set (_root_.D11.Ch03.Point 1),
    0 < LebesgueMeasures.coveringOuter 1 B →
    ∃ V ⊆ B, ¬ MeasurableSet[LebesgueMeasures.lebesgueSpace_value 1] V

end Specs.D11.Ch03.PositiveOuterNonmeasurable
