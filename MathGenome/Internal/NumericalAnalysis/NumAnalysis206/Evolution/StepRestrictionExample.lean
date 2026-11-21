import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.StepRestrictionExample
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Evolution.Definitions
import Mathlib.Tactic.NormNum

open Filter Topology

noncomputable section

namespace NumAnalysis206.Evolution.StepRestriction

lemma operators_eq_one {h : ℝ} (hh : h ≤ 1 / 2) : operators h = 1 := by
  unfold operators coefficient
  rw [ite_eq_left (Or.inl hh)]
  simp

lemma operators_apply_large {h : ℝ} (hh : 1 / 2 < h) (hne : h ≠ 3 / 4)
    (x : ℝ) : operators h x = (1 / |h - 3 / 4|) * x := by
  unfold operators coefficient
  rw [ite_eq_right (not_or.mpr ⟨not_le.mpr hh, hne⟩)]
  simp

lemma meshError_eq_zero (x : ℝ) {h : ℝ} (hh : h ≤ 1 / 2) :
    meshError operators exactSemigroup 1 h x = 0 := by
  simp [meshError, operators_eq_one hh, exactSemigroup]

lemma convergent : StronglyConvergent operators exactSemigroup 1 := by
  intro x
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with h hh
  exact (meshError_eq_zero x hh.2).symm

lemma stable : SmallStepStable operators 1 := by
  refine ⟨1 / 2, by norm_num, 1, by norm_num, ?_⟩
  intro h _ hh n _
  simp [operators_eq_one hh]

lemma unbounded_one_step (M : ℝ) :
    ∃ h : ℝ, 3 / 4 < h ∧ h ≤ 1 ∧ M < ‖operators h ^ 1‖ := by
  let R : ℝ := 8 * (|M| + 1)
  have hR8 : 8 ≤ R := by dsimp [R]; nlinarith [abs_nonneg M]
  have hR : 0 < R := by linarith
  have hd : 0 < R⁻¹ := inv_pos.mpr hR
  have hdle : R⁻¹ ≤ 1 / 8 := by
    have hprod : R⁻¹ * R = 1 := inv_mul_cancel₀ (ne_of_gt hR)
    nlinarith
  let h : ℝ := 3 / 4 + R⁻¹
  have hh : 1 / 2 < h := by dsimp [h]; linarith
  have hne : h ≠ 3 / 4 := by dsimp [h]; linarith
  have hnorm : ‖operators h ^ 1‖ = R := by
    simp only [pow_one, operators, coefficient, ite_eq_right (not_or.mpr ⟨not_le.mpr hh, hne⟩)]
    rw [norm_smul]
    have habs : |h - 3 / 4| = R⁻¹ := by
      dsimp [h]
      rw [add_sub_cancel_left, abs_of_pos hd]
    rw [habs]
    simp [abs_of_pos hR]
  refine ⟨h, ?_, ?_, ?_⟩
  · dsimp [h]; linarith
  · dsimp [h]; linarith
  · rw [hnorm]
    dsimp [R]
    nlinarith [le_abs_self M, abs_nonneg M]

lemma no_all_step_bound :
    ¬ (∃ M : ℝ, ∀ h : ℝ, 0 < h → ∀ n : ℕ,
      (n : ℝ) * h ≤ 1 → ‖operators h ^ n‖ ≤ M) := by
  rintro ⟨M, hM⟩
  obtain ⟨h, hh, hle, hnorm⟩ := unbounded_one_step M
  have hbound := hM h (by linarith) 1 (by simpa using hle)
  exact (not_lt_of_ge hbound) hnorm

/-- Exact convergence and eventual stability coexist with an unbounded family
of one-step maps away from zero. -/
theorem exampleProperties :
    Specs.NumAnalysis206.Evolution.StepRestriction.exampleProperties := by
  refine ⟨fun h => (operators h).continuous, ?_, ?_, ?_, ?_,
    convergent, stable, unbounded_one_step, no_all_step_bound⟩
  · intro h _ hh
    exact operators_eq_one hh
  · simp [operators, coefficient]
  · intro h hh hne x
    exact operators_apply_large hh hne x
  · intro x h _ hh
    exact meshError_eq_zero x hh

end NumAnalysis206.Evolution.StepRestriction
