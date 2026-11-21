import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.LimitAlgebra
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Squeeze
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Stolz
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-! Stolz–Cesàro, with real strictly increasing unbounded denominators.
The proof is the manuscript's telescoping argument in a real normed space,
then specialized to the two canonical scalar fields. No completeness,
positivity of a finite prefix, or limit of the numerator is required. -/

namespace SingleVariableAnalysis

open scoped Topology

/-- Positive divergence gives positive denominators on a tail. -/
theorem stolz_denominator_eventually_positive (b : ℕ → ℝ)
    (hb : DivergesToPosInfinity b) : SequenceEventually (fun n => 0 < b n) :=
  hb 0

/-- The triangle inequality telescopes an increment bound over any finite tail. -/
theorem norm_le_of_increment_bound {E : Type*} [SeminormedAddCommGroup E]
    (c : ℕ → E) (b : ℕ → ℝ) (δ : ℝ) (N : ℕ)
    (h : ∀ j ≥ N, ‖c (j + 1) - c j‖ ≤ δ * (b (j + 1) - b j)) :
    ∀ n ≥ N, ‖c n‖ ≤ ‖c N‖ + δ * (b n - b N) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have ht : ‖c (n + 1)‖ ≤ ‖c (n + 1) - c n‖ + ‖c n‖ := by
      simpa only [sub_add_cancel] using norm_add_le (c (n + 1) - c n) (c n)
    have hi := h n hn
    nlinarith

/-- The common real-vector argument, used for both real and complex scalars. -/
theorem tendsto_stolz_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (b : ℕ → ℝ) (L : E) (hb : StrictMono b)
    (hbinf : DivergesToPosInfinity b)
    (h : Filter.Tendsto (fun n => (b (n + 1) - b n)⁻¹ • (a (n + 1) - a n))
      Filter.atTop (𝓝 L)) :
    Filter.Tendsto (fun n => (b n)⁻¹ • a n) Filter.atTop (𝓝 L) := by
  let c : ℕ → E := fun n => a n - b n • L
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hδ : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h (ε / 2) hδ
  have hinc : ∀ j ≥ N, ‖c (j + 1) - c j‖ ≤ (ε / 2) * (b (j + 1) - b j) := by
    intro j hj
    have hd : 0 < b (j + 1) - b j := sub_pos.mpr (hb (Nat.lt_succ_self j))
    have heq : c (j + 1) - c j = (b (j + 1) - b j) •
        ((b (j + 1) - b j)⁻¹ • (a (j + 1) - a j) - L) := by
      simp only [smul_sub, smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
      dsimp [c]
      module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    have hs := hN j hj
    rw [dist_eq_norm] at hs
    exact le_of_lt (by nlinarith)
  let C : ℝ := ‖c N‖ + (ε / 2) * |b N|
  obtain ⟨M, hM⟩ := hbinf (max 0 (C / (ε / 2)))
  refine ⟨max N M, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnM : M ≤ n := le_trans (le_max_right _ _) hn
  have hbn : 0 < b n := lt_of_le_of_lt (le_max_left _ _) (hM n hnM)
  have hC : C < (ε / 2) * b n := by
    have ht : C / (ε / 2) < b n := lt_of_le_of_lt (le_max_right _ _) (hM n hnM)
    have := (div_lt_iff₀ hδ).mp ht
    nlinarith
  have hc := norm_le_of_increment_bound c b (ε / 2) N hinc n hnN
  have hcsmall : ‖c n‖ < ε * b n := by
    have hab : -b N ≤ |b N| := neg_le_abs (b N)
    dsimp [C] at hC
    nlinarith
  have heq : (b n)⁻¹ • a n - L = (b n)⁻¹ • c n := by
    dsimp [c]
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hbn.ne', one_smul]
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hbn)]
  have hi : 0 < (b n)⁻¹ := inv_pos.mpr hbn
  have hh := mul_lt_mul_of_pos_left hcsmall hi
  simpa only [← mul_assoc, mul_left_comm (b n)⁻¹ ε, inv_mul_cancel₀ hbn.ne',
    mul_one] using hh

/-- Stolz–Cesàro for real numerators and a finite real ratio limit. -/
theorem real_stolz (a b : ℕ → ℝ) (L : ℝ) (hb : StrictMono b)
    (hbinf : DivergesToPosInfinity b)
    (h : RealSequenceConverges
      (fun n => (a (n + 1) - a n) / (b (n + 1) - b n)) L) :
    RealSequenceConverges (fun n => a n / b n) L := by
  apply (realSequenceConverges_iff _ _).mpr
  have ht := (realSequenceConverges_iff _ _).mp h
  have hs : Filter.Tendsto
      (fun n => (b (n + 1) - b n)⁻¹ • (a (n + 1) - a n))
      Filter.atTop (𝓝 L) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using ht
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    tendsto_stolz_smul a b L hb hbinf hs

/-- Stolz–Cesàro for complex numerators with the same real denominator. -/
theorem complex_stolz (a : ℕ → ℂ) (b : ℕ → ℝ) (L : ℂ) (hb : StrictMono b)
    (hbinf : DivergesToPosInfinity b)
    (h : ComplexSequenceConverges
      (fun n => (a (n + 1) - a n) / ((b (n + 1) - b n : ℝ) : ℂ)) L) :
    ComplexSequenceConverges (fun n => a n / (b n : ℂ)) L := by
  apply (complexSequenceConverges_iff _ _).mpr
  have ht := (complexSequenceConverges_iff _ _).mp h
  have hs : Filter.Tendsto
      (fun n => (b (n + 1) - b n)⁻¹ • (a (n + 1) - a n))
      Filter.atTop (𝓝 L) := by
    simpa only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using ht
  simpa only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using
    tendsto_stolz_smul a b L hb hbinf hs

end SingleVariableAnalysis
