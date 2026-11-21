import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.SummationParts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Necessary
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Dirichlet
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Dirichlet's test for ordinary scalar series

K03.11.dirichlet, paper.tex:1063–1073. Finite summation by parts gives
the quantitative estimate before completeness is invoked. The finite
estimate is proved for real scalar multiplication in a normed space;
its real and complex specializations use the canonical scalar products.
The increasing case is reduced by negating the amplitude. Finally the
upstream ordinary-series Cauchy criterion supplies a finite scalar sum.
-/
namespace SingleVariableAnalysis
open scoped BigOperators Topology

private lemma sum_differences (b : ℕ → ℝ) {p q : ℕ} (hpq : p ≤ q) :
    (∑ n ∈ Finset.Ico p q, (b n - b (n + 1))) = b p - b q := by
  induction q, hpq using Nat.le_induction with
  | base => simp
  | succ q hpq ih =>
    rw [Finset.sum_Ico_succ_top hpq, ih]
    ring

/-- The finite Dirichlet bound for a nonnegative decreasing amplitude.
The bound on inclusive prefixes also bounds the empty prefix. -/
theorem dirichlet_tail_bound_antitone_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (b : ℕ → ℝ) (M : ℝ)
    (hA : ∀ n, ‖∑ j ∈ Finset.range (n + 1), a j‖ ≤ M)
    (hb : Antitone b) (hb0 : ∀ n, 0 ≤ b n)
    (p q : ℕ) (hpq : p ≤ q) :
    ‖∑ n ∈ Finset.Icc p q, b n • a n‖ ≤ 2 * M * b p := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA 0)
  have hprefix : ∀ n, ‖∑ j ∈ Finset.range n, a j‖ ≤ M := by
    intro n
    cases n with
    | zero => simpa using hM
    | succ n => exact hA n
  have h := Finset.sum_Ico_by_parts b a (Nat.lt_succ_of_le hpq)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel,
    Finset.Ico_add_one_right_eq_Icc] at h
  rw [h]
  calc
    _ ≤ (‖b q • (∑ j ∈ Finset.range (q + 1), a j)‖ +
        ‖b p • (∑ j ∈ Finset.range p, a j)‖) +
        ∑ n ∈ Finset.Ico p q,
          ‖(b (n + 1) - b n) • (∑ j ∈ Finset.range (n + 1), a j)‖ := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sum_le _ _))
    _ ≤ b q * M + b p * M +
        ∑ n ∈ Finset.Ico p q, (b n - b (n + 1)) * M := by
      apply add_le_add
      · apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb0 q)]
          exact mul_le_mul_of_nonneg_left (hA q) (hb0 q)
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb0 p)]
          exact mul_le_mul_of_nonneg_left (hprefix p) (hb0 p)
      · apply Finset.sum_le_sum
        intro n _
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (hb (Nat.le_succ n))), neg_sub]
        exact mul_le_mul_of_nonneg_left (hA n) (sub_nonneg.mpr (hb (Nat.le_succ n)))
    _ = 2 * M * b p := by
      rw [← Finset.sum_mul, sum_differences b hpq]
      ring

/-- Signed monotone amplitudes tending to zero, with either direction allowed. -/
theorem dirichlet_tail_bound_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (b : ℕ → ℝ) (M : ℝ)
    (hA : ∀ n, ‖∑ j ∈ Finset.range (n + 1), a j‖ ≤ M)
    (hb : Monotone b ∨ Antitone b) (hb0 : RealSequenceConverges b 0)
    (p q : ℕ) (hpq : p ≤ q) :
    ‖∑ n ∈ Finset.Icc p q, b n • a n‖ ≤ 2 * M * |b p| := by
  have ht := (realSequenceConverges_iff b 0).mp hb0
  rcases hb with hb | hb
  · have hneg : Antitone (fun n => -b n) := fun _ _ h => neg_le_neg (hb h)
    have hn0 : ∀ n, 0 ≤ -b n := fun n => neg_nonneg.mpr (hb.ge_of_tendsto ht n)
    have h := dirichlet_tail_bound_antitone_smul a (fun n => -b n) M hA hneg hn0 p q hpq
    simpa only [neg_smul, Finset.sum_neg_distrib, norm_neg,
      abs_of_nonpos (hb.ge_of_tendsto ht p)] using h
  · simpa only [abs_of_nonneg (hb.le_of_tendsto ht p)] using
      dirichlet_tail_bound_antitone_smul a b M hA hb (hb.le_of_tendsto ht) p q hpq

theorem real_dirichlet_tail_bound :
    Specs.SingleVariableAnalysis.Ch11.Dirichlet.realDirichletTailBound := by
  intro a b M hA hb hb0 p q hpq
  have hA' : ∀ n, ‖∑ j ∈ Finset.range (n + 1), a j‖ ≤ M := by
    simpa only [Real.norm_eq_abs,
      Specs.SingleVariableAnalysis.Ch11.PartialSums.realPartialSumValue] using hA
  simpa only [smul_eq_mul, mul_comm, Real.norm_eq_abs] using
    dirichlet_tail_bound_smul a b M hA' hb hb0 p q hpq

theorem complex_dirichlet_tail_bound :
    Specs.SingleVariableAnalysis.Ch11.Dirichlet.complexDirichletTailBound := by
  intro a b M hA hb hb0 p q hpq
  simpa only [Complex.real_smul, mul_comm] using
    dirichlet_tail_bound_smul a b M hA hb hb0 p q hpq

theorem real_dirichlet :
    Specs.SingleVariableAnalysis.Ch11.Dirichlet.realDirichlet := by
  intro a b hA hb hb0
  obtain ⟨M, hM⟩ := hA
  apply (real_series_cauchy_criterion _).mpr
  intro ε hε
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  obtain ⟨N, hN⟩ := hb0 (ε / (2 * M + 1)) (div_pos hε (by linarith))
  refine ⟨N, ?_⟩
  intro p hp q hpq
  have hbound := real_dirichlet_tail_bound a b M hM hb hb0 p q hpq
  have hsmall : |b p| < ε / (2 * M + 1) := by simpa only [sub_zero] using hN p hp
  have hlt : |b p| * (2 * M + 1) < ε := (lt_div_iff₀ (by linarith)).mp hsmall
  nlinarith [abs_nonneg (b p)]

theorem complex_dirichlet :
    Specs.SingleVariableAnalysis.Ch11.Dirichlet.complexDirichlet := by
  intro a b hA hb hb0
  obtain ⟨M, hM⟩ := hA
  apply (complex_series_cauchy_criterion _).mpr
  intro ε hε
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨N, hN⟩ := hb0 (ε / (2 * M + 1)) (div_pos hε (by linarith))
  refine ⟨N, ?_⟩
  intro p hp q hpq
  have hbound := complex_dirichlet_tail_bound a b M hM hb hb0 p q hpq
  have hsmall : |b p| < ε / (2 * M + 1) := by simpa only [sub_zero] using hN p hp
  have hlt : |b p| * (2 * M + 1) < ε := (lt_div_iff₀ (by linarith)).mp hsmall
  nlinarith [abs_nonneg (b p)]
end SingleVariableAnalysis
