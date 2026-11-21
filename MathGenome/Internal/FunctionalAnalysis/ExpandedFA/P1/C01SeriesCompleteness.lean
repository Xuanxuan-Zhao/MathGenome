import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SeriesCompleteness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Banach
import Mathlib.Analysis.Normed.Group.Completeness

/-!
The series criterion for completeness and its norm estimate.

Mathlib's completeness criterion uses ordered initial sums. Its converse
selects a Cauchy subsequence with summable successive differences, telescopes
the resulting series, and obtains convergence of the original Cauchy sequence.
The quantitative bound applies to the ordered limit through the upstream
absolute-series bridge; no unconditional interpretation is imposed on
general series.
-/

namespace ExpandedFA.P1.C01SeriesCompleteness

open ExpandedFA.P1.C01Banach

theorem series_completeness : Spec.SeriesCriterion := by
  intro 𝕜 E _ _ _
  constructor
  · intro h u hu
    let : CompleteSpace E := (isBanachSpace_iff_completeSpace E).mp h
    obtain ⟨a, ha⟩ := NormedAddCommGroup.summable_imp_tendsto_of_complete u hu
    exact ⟨a, (hasSequentialSum_iff E u a).mpr ha⟩
  · intro h
    apply (isBanachSpace_iff_completeSpace E).mpr
    apply NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
    intro u hu
    obtain ⟨a, ha⟩ := h u hu
    exact ⟨a, (hasSequentialSum_iff E u a).mp ha⟩

theorem series_norm_bound : Spec.SeriesNormBound := by
  intro 𝕜 E _ _ _ _ u a hu ha
  have hs : HasSum u a := (hasSequentialSum_iff_hasSum_of_absolute E u a hu).mp ha
  exact hs.norm_le_of_bounded hu.hasSum (fun _ => le_rfl)

end ExpandedFA.P1.C01SeriesCompleteness
