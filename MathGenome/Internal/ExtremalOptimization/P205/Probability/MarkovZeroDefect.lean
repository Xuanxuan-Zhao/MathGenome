import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.MarkovZeroDefect

open MeasureTheory

namespace P205.Probability

/-- The inclusive form of Markov's inequality on any probability space. -/
theorem markov_bound : Specs.P205.Probability.MarkovBound := by
  intro Ω _ μ _ X _hX hInt hNonneg a ha
  apply (le_div_iff₀ ha).2
  simpa only [mul_comm] using mul_meas_ge_le_integral_of_nonneg hNonneg hInt a

/-- The almost-sure integer-valued hypothesis turns the first moment bound
at one into positive probability of no defects. -/
theorem zero_defect_criterion : Specs.P205.Probability.ZeroDefectCriterion := by
  intro Ω _ μ _ X hX hInt hNat hMean
  have hNonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω := by
    filter_upwards [hNat] with ω hω
    obtain ⟨n, hn⟩ := hω
    rw [hn]
    exact Nat.cast_nonneg n
  have hEvents : {ω | X ω ≠ 0} =ᵐ[μ] {ω | 1 ≤ X ω} := by
    filter_upwards [hNat] with ω hω
    obtain ⟨n, hn⟩ := hω
    apply propext
    rw [hn, Nat.cast_ne_zero, Nat.one_le_cast_iff_ne_zero]
  have hTail : μ.real {ω | 1 ≤ X ω} ≤ ∫ ω, X ω ∂μ := by
    simpa using markov_bound μ X hX hInt hNonneg 1 zero_lt_one
  have hZero : MeasurableSet {ω | X ω = 0} :=
    measurableSet_eq_fun hX measurable_const
  have hCompl : μ.real {ω | X ω ≠ 0} = 1 - μ.real {ω | X ω = 0} := by
    exact probReal_compl_eq_one_sub hZero
  rw [measureReal_congr hEvents] at hCompl
  apply (sub_lt_self_iff (1 : ℝ)).mp
  rw [← hCompl]
  exact hTail.trans_lt hMean

end P205.Probability
