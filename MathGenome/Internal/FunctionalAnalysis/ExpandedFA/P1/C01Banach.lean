import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach

/-! Banach completeness and ordered-series definitions, with canonical bridges. -/

open Filter
open scoped Topology

namespace ExpandedFA.P1.C01Banach

/-- The Cauchy condition in the displayed norm. -/
def NormCauchySequence : Spec.NormCauchySequenceType :=
  fun _ _ u => ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖u m - u n‖ < ε

/-- Convergence to a vector in the displayed norm. -/
def NormConvergesTo : Spec.NormConvergesToType :=
  fun _ _ u a => ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ‖u n - a‖ < ε

/-- Every norm Cauchy sequence converges in this space. No nontriviality is required. -/
def IsBanachSpace : Spec.IsBanachSpaceType :=
  fun E _ => ∀ u : ℕ → E, NormCauchySequence E u →
    ∃ a : E, NormConvergesTo E u a

/-- The sum of the first N terms; at N = 0 it is zero. -/
def seriesPartialSums : Spec.seriesPartialSumsType :=
  fun _ _ u N => ∑ n ∈ Finset.range N, u n

/-- An ordered series converges to a when its finite initial sums converge in norm. -/
def HasSequentialSum : Spec.HasSequentialSumType :=
  fun E _ u a => NormConvergesTo E
    (seriesPartialSums E u) a

/-- Existence of a limit of the ordered partial sums, allowing conditional convergence. -/
def SequentiallySummable : Spec.SequentiallySummableType :=
  fun E _ u => ∃ a : E, HasSequentialSum E u a

/-- Absolute norm summability; the real nonnegative series has a finite sum. -/
def AbsolutelySummable : Spec.AbsolutelySummableType :=
  fun _ _ u => Summable (fun n => ‖u n‖)

theorem normCauchySequence_iff : Spec.NormCauchySequenceIdentification := by
  intro E _ u
  simpa only [Spec.NormCauchySequenceValue, dist_eq_norm] using
    (Metric.cauchySeq_iff (u := u)).symm

theorem normConvergesTo_iff : Spec.NormConvergenceIdentification := by
  intro E _ u a
  simpa only [Spec.NormConvergesToValue, dist_eq_norm] using
    (Metric.tendsto_atTop (u := u) (a := a)).symm

theorem isBanachSpace_iff_completeSpace : Spec.BanachIdentification := by
  intro E _
  constructor
  · intro h
    apply Metric.complete_of_cauchySeq_tendsto
    intro u hu
    obtain ⟨a, ha⟩ := h u ((normCauchySequence_iff E u).mpr hu)
    exact ⟨a, (normConvergesTo_iff E u a).mp ha⟩
  · intro h
    let : CompleteSpace E := h
    intro u hu
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
      ((normCauchySequence_iff E u).mp hu)
    exact ⟨a, (normConvergesTo_iff E u a).mpr ha⟩

theorem hasSequentialSum_iff : Spec.SequentialSumIdentification := by
  intro E _ u a
  exact normConvergesTo_iff E (seriesPartialSums E u) a

theorem sequentiallySummable_iff : Spec.SequentialSummabilityIdentification := by
  intro E _ u
  exact exists_congr (fun a => hasSequentialSum_iff E u a)

theorem absolutelySummable_iff : Spec.AbsoluteSummabilityIdentification := by
  intro E _ u
  exact exists_congr (fun r => hasSum_iff_tendsto_nat_of_nonneg (fun n => norm_nonneg (u n)) r)

theorem hasSequentialSum_iff_hasSum_of_absolute : Spec.AbsoluteSeriesBridge := by
  intro E _ u a hu
  exact (hasSequentialSum_iff E u a).trans
    (hasSum_iff_tendsto_nat_of_summable_norm hu).symm

end ExpandedFA.P1.C01Banach
