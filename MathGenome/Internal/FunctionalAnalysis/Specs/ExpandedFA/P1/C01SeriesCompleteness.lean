import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach

/-!
Independent statements for Theorem `fa2:p1:c01:series-completeness`,
paper.tex lines 166–170.

The upstream interface relabels the manuscript's positive indices by ℕ,
and defines convergence using ordered initial partial sums in the given norm.
The scalar parameter includes both ℝ and ℂ. Neither nontriviality nor
completeness is assumed in the equivalence, including its reverse direction.
-/

namespace ExpandedFA.P1.C01SeriesCompleteness.Spec

open ExpandedFA.P1.C01Banach.Spec

/-- A normed space is Banach exactly when every absolutely norm-summable
ordered series has a limit in that space. -/
def SeriesCriterion : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    IsBanachSpaceValue E ↔
      ∀ u : ℕ → E, AbsolutelySummableValue E u → SequentiallySummableValue E u

/-- The infinite triangle inequality for the actual ordered-series limit.
The right-hand real series is summable by the absolute-summability hypothesis. -/
def SeriesNormBound : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    IsBanachSpaceValue E →
      ∀ (u : ℕ → E) (a : E), AbsolutelySummableValue E u →
        HasSequentialSumValue E u a → ‖a‖ ≤ ∑' n, ‖u n‖

end ExpandedFA.P1.C01SeriesCompleteness.Spec
