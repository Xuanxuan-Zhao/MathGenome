import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.CholeskyBreakdownExample
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.RadixModel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
namespace NumAnalysis206.LinearAlgebra.CholeskyBreakdownExample
open NumAnalysis206.Rounding
open NumAnalysis206.MatrixDefinitions
open NumAnalysis206.LinearAlgebra.CholeskyData
open NumAnalysis206.LinearAlgebra.CholeskyBreakdownData

private theorem half_mem : (1 / 2 : ℝ) ∈ F format := by
  rw [mem_F]
  refine Or.inr (Or.inl ⟨8, -4, ?_, ?_, ?_, ?_, Or.inl ?_⟩) <;>
    norm_num [format]

private theorem quarter_mem : (1 / 4 : ℝ) ∈ F format := by
  rw [mem_F]
  refine Or.inr (Or.inl ⟨8, -5, ?_, ?_, ?_, ?_, Or.inl ?_⟩) <;>
    norm_num [format]

private theorem nine_mem : (9 / 32 : ℝ) ∈ F format := by
  rw [mem_F]
  refine Or.inr (Or.inl ⟨9, -5, ?_, ?_, ?_, ?_, Or.inl ?_⟩) <;>
    norm_num [format]

/-- There is no representable point strictly between 1/2 and its successor. -/
private theorem format_gap (y : ℝ) (hy : y ∈ F format) :
    y ≤ 1 / 2 ∨ 9 / 16 ≤ y := by
  rw [mem_F] at hy
  rcases hy with rfl | ⟨m, e, hm, hm', he, he', hy⟩ | ⟨hg, _⟩
  · norm_num
  · norm_num [format] at hm hm' he he'
    have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
    have hmR' : (m : ℝ) ≤ 15 := by exact_mod_cast (show m ≤ 15 by omega)
    by_cases hm8 : m = 8
    · subst m
      rcases hy with rfl | rfl <;> interval_cases e <;> norm_num [format]
    · have hm9 : (9 : ℝ) ≤ m := by exact_mod_cast (show 9 ≤ m by omega)
      rcases hy with rfl | rfl <;> interval_cases e <;> norm_num [format] <;>
        first | (left; linarith) | (right; linarith)
  · simp [format] at hg

private theorem sqrt_round : fl format (Real.sqrt (9 / 32)) = 1 / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 9 / 32 by norm_num)
  have hn := Real.sqrt_nonneg (9 / 32 : ℝ)
  have hlo : (1 / 2 : ℝ) ≤ Real.sqrt (9 / 32) := by nlinarith
  have hhi : Real.sqrt (9 / 32 : ℝ) < 17 / 32 := by nlinarith
  have hmin := fl_minimizes format (Real.sqrt (9 / 32)) (1 / 2) half_mem
  rw [abs_of_nonpos (by linarith : (1 / 2 : ℝ) - Real.sqrt (9 / 32) ≤ 0)] at hmin
  have hbounds := abs_le.mp hmin
  rcases format_gap _ (fl_mem_F format (Real.sqrt (9 / 32))) with h | h
  · linarith
  · linarith

theorem rounded_steps :
    _root_.Specs.NumAnalysis206.LinearAlgebra.CholeskyBreakdownExample.roundedSteps := by
  have hhalf := fl_fixes format (1 / 2) half_mem
  have hquarter := fl_fixes format (1 / 4) quarter_mem
  have hzero := fl_fixes format 0 (zero_mem_F format)
  change fl format (Real.sqrt (9 / 32)) = 1 / 2 ∧ _
  refine ⟨sqrt_round, ?_, ?_, ?_⟩
  · norm_num at hhalf ⊢
    exact hhalf
  · norm_num at hquarter ⊢
    exact hquarter
  · change fl format ((1 / 4) - fl format ((1 / 2) * (1 / 2))) = 0
    norm_num at hquarter ⊢
    rw [hquarter]
    norm_num

theorem input_properties :
    _root_.Specs.NumAnalysis206.LinearAlgebra.CholeskyBreakdownExample.inputProperties := by
  refine ⟨?_, by norm_num [A], by norm_num [A, Matrix.det_fin_two],
    by norm_num [A], ?_⟩
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [A, Matrix.conjTranspose_apply]
    · intro x hx
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.star_apply,
        star_trivial]
      norm_num [A]
      by_cases h0 : x 0 = 0
      · have h1 : x 1 ≠ 0 := by
          intro h1
          apply hx
          funext i
          fin_cases i <;> simp [h0, h1]
        have hp := sq_pos_of_ne_zero h1
        simp only [h0, zero_mul, mul_zero, zero_add]
        nlinarith
      · have hp := sq_pos_of_ne_zero h0
        have hsq := sq_nonneg (x 0 + x 1)
        nlinarith
  · intro i j
    fin_cases i <;> fin_cases j <;>
      first | simpa [A, F] using nine_mem | simpa [A, F] using quarter_mem

private theorem primitive_trace : PrimitiveTrace (fl format) A L states := by
  have hhalf := fl_fixes format (1 / 2) half_mem
  have hquarter := fl_fixes format (1 / 4) quarter_mem
  have hzero := fl_fixes format 0 (zero_mem_F format)
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [L] at *
  · intro i j hij
    simp [states]
  · intro i j hij t ht
    fin_cases i <;> fin_cases j <;> norm_num at *
    have ht0 : t = 0 := by omega
    subst t
    norm_num [states, A, L, entry]
    norm_num at hquarter
    rw [hquarter]
    simpa using hzero.symm
  · intro j
    fin_cases j
    · simpa [L, states, A] using sqrt_round.symm
    · simpa [L, states] using hzero.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
    norm_num [L, states, A]
    norm_num at hhalf
    exact hhalf.symm

private theorem every_primitive_breaks (L' : Mat ℝ 2 2)
    (s : Fin 2 → Fin 2 → ℕ → ℝ) (T : PrimitiveTrace (fl format) A L' s) :
    s 1 1 1 = 0 := by
  have hhalf := fl_fixes format (1 / 2) half_mem
  have hquarter := fl_fixes format (1 / 4) quarter_mem
  have hzero := fl_fixes format 0 (zero_mem_F format)
  have h00 : L' 0 0 = 1 / 2 := by
    rw [T.diagonal]
    change fl format (Real.sqrt (s 0 0 0)) = 1 / 2
    rw [T.initial 0 0 le_rfl]
    simpa [A] using sqrt_round
  have h10 : L' 1 0 = 1 / 2 := by
    rw [T.offDiagonal 1 0 (by decide)]
    change fl format (s 1 0 0 / L' 0 0) = 1 / 2
    rw [T.initial 1 0 (by decide), h00]
    norm_num [A] at hhalf ⊢
    exact hhalf
  have hstep := T.step 1 1 le_rfl 0 (by decide)
  rw [T.initial 1 1 le_rfl] at hstep
  norm_num [entry, A, h10] at hstep
  norm_num at hquarter
  rw [hquarter] at hstep
  simpa using hstep.trans (by simpa using hzero)

theorem breakdown :
    _root_.Specs.NumAnalysis206.LinearAlgebra.CholeskyBreakdownExample.breakdown := by
  refine ⟨primitive_trace, by simp [states], every_primitive_breaks, ?_⟩
  intro u D L' s T
  have hz := every_primitive_breaks L' s T.primitive
  have hp := T.positive 1
  norm_num at hp
  rw [hz] at hp
  exact lt_irrefl 0 hp

end NumAnalysis206.LinearAlgebra.CholeskyBreakdownExample
