import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Dirichlet
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Monotone
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Abel

/-!
# Abel's test for ordinary scalar series

K03.11.abel, paper.tex:1073–1081. Bounded monotonicity gives a finite
limit L of the real amplitude b. The centered amplitude b - L is still
monotone and tends to zero. Convergence of the original ordered partial
sums bounds them, so Dirichlet applies to a * (b - L). Adding L * a
recovers the required product series. Both directions of monotonicity
and conditional convergence are included.
-/
namespace SingleVariableAnalysis

/-- A bounded monotone real amplitude has a finite limit in either direction. -/
theorem bounded_monotone_real_sequence_converges (b : ℕ → ℝ)
    (hb : Monotone b ∨ Antitone b) (hB : ∃ M : ℝ, ∀ n, |b n| ≤ M) :
    ∃ L : ℝ, RealSequenceConverges b L := by
  obtain ⟨M, hM⟩ := hB
  rcases hb with hb | hb
  · have hu : BddAbove (Set.range b) :=
      ⟨M, by rintro _ ⟨n, rfl⟩; exact (le_abs_self (b n)).trans (hM n)⟩
    exact ⟨_, monotone_converges_to_supremum b hb hu⟩
  · have hl : BddBelow (Set.range b) := by
      refine ⟨-M, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (neg_le_neg (hM n)).trans (neg_abs_le (b n))
    exact ⟨_, antitone_converges_to_infimum b hb hl⟩

theorem real_abel : Specs.SingleVariableAnalysis.Ch11.Abel.realAbel := by
  intro a b ha hb hB
  obtain ⟨S, hS⟩ := ha
  obtain ⟨L, hL⟩ := bounded_monotone_real_sequence_converges b hb hB
  have hmono : Monotone (fun n => b n - L) ∨ Antitone (fun n => b n - L) := by
    rcases hb with hb | hb
    · exact Or.inl (fun _ _ h => sub_le_sub_right (hb h) L)
    · exact Or.inr (fun _ _ h => sub_le_sub_right (hb h) L)
  have hzero : RealSequenceConverges (fun n => b n - L) 0 := by
    intro ε hε
    simpa only [sub_zero] using hL ε hε
  obtain ⟨M, _, hM⟩ := real_convergent_bounded (realPartialSum a) S hS
  obtain ⟨T, hT⟩ := real_dirichlet a (fun n => b n - L) ⟨M, hM⟩ hmono hzero
  have hsum := real_series_add (fun n => L * a n)
    (fun n => a n * (b n - L)) (L * S) T
    (real_series_const_mul a S hS L) hT
  refine ⟨L * S + T, ?_⟩
  change RealSeriesHasSum (fun n => a n * b n) (L * S + T)
  convert hsum using 1
  funext n
  ring

theorem complex_abel : Specs.SingleVariableAnalysis.Ch11.Abel.complexAbel := by
  intro a b ha hb hB
  obtain ⟨S, hS⟩ := ha
  obtain ⟨L, hL⟩ := bounded_monotone_real_sequence_converges b hb hB
  have hmono : Monotone (fun n => b n - L) ∨ Antitone (fun n => b n - L) := by
    rcases hb with hb | hb
    · exact Or.inl (fun _ _ h => sub_le_sub_right (hb h) L)
    · exact Or.inr (fun _ _ h => sub_le_sub_right (hb h) L)
  have hzero : RealSequenceConverges (fun n => b n - L) 0 := by
    intro ε hε
    simpa only [sub_zero] using hL ε hε
  obtain ⟨M, _, hM⟩ := complex_convergent_bounded (complexPartialSum a) S hS
  obtain ⟨T, hT⟩ := complex_dirichlet a (fun n => b n - L) ⟨M, hM⟩ hmono hzero
  have hsum := complex_series_add (fun n => (L : ℂ) * a n)
    (fun n => a n * ((b n - L : ℝ) : ℂ)) ((L : ℂ) * S) T
    (complex_series_const_mul a S hS (L : ℂ)) hT
  refine ⟨(L : ℂ) * S + T, ?_⟩
  change ComplexSeriesHasSum (fun n => a n * (b n : ℂ)) ((L : ℂ) * S + T)
  convert hsum using 1
  funext n
  push_cast
  ring

end SingleVariableAnalysis
