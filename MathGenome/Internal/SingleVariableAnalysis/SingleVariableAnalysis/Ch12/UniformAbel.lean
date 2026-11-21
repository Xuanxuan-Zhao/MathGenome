import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.SummationParts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.UniformAbel
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform Abel test

For either canonical scalar field, summation by parts bounds each weighted
tail by the largest ordinary tail norm times the multiplier's final absolute
value plus its finite variation. Pointwise monotonicity makes that variation
at most twice the common bound. The upstream uniform Cauchy criterion then
produces the scalar-valued uniform limit. The denominator `3 * max M 0 + 1`
keeps the error choice positive for every bound, including zero and the
vacuous negative-bound case on the empty domain.
-/

namespace SingleVariableAnalysis

open scoped BigOperators
universe u

/-- The variation of a monotone real sequence on a finite interval. -/
theorem monotone_sequence_variation (b : ℕ → ℝ) (p q : ℕ) (hpq : p ≤ q)
    (hb : Monotone b ∨ Antitone b) :
    (∑ n ∈ Finset.Ico p q, |b n - b (n + 1)|) = |b p - b q| := by
  rcases hb with hb | hb
  · induction q, hpq using Nat.le_induction with
    | base => simp
    | succ q hpq ih =>
      rw [Finset.sum_Ico_succ_top hpq, ih,
        abs_of_nonpos (sub_nonpos.mpr (hb hpq)),
        abs_of_nonpos (sub_nonpos.mpr (hb (Nat.le_succ q))),
        abs_of_nonpos (sub_nonpos.mpr (hb (Nat.le_succ_of_le hpq)))]
      ring
  · induction q, hpq using Nat.le_induction with
    | base => simp
    | succ q hpq ih =>
      rw [Finset.sum_Ico_succ_top hpq, ih,
        abs_of_nonneg (sub_nonneg.mpr (hb hpq)),
        abs_of_nonneg (sub_nonneg.mpr (hb (Nat.le_succ q))),
        abs_of_nonneg (sub_nonneg.mpr (hb (Nat.le_succ_of_le hpq)))]
      ring

/-- A finite Abel tail estimate, valid for both canonical scalar fields. -/
theorem abel_tail_norm_le {K : Type*} [RCLike K]
    (a : ℕ → K) (b : ℕ → ℝ) (p q : ℕ) (hpq : p ≤ q)
    (η M : ℝ) (hη : 0 ≤ η)
    (ha : ∀ n, p ≤ n → n ≤ q → ‖∑ j ∈ Finset.Icc p n, a j‖ ≤ η)
    (hb : Monotone b ∨ Antitone b) (hM : ∀ n, |b n| ≤ M) :
    ‖∑ n ∈ Finset.Icc p q, a n * (b n : K)‖ ≤ 3 * M * η := by
  rw [summation_parts_tail a (fun n => (b n : K)) p q hpq]
  calc
    _ ≤ ‖(∑ j ∈ Finset.Icc p q, a j) * (b q : K)‖ +
        ∑ n ∈ Finset.Ico p q,
          ‖(∑ j ∈ Finset.Icc p n, a j) * ((b n : K) - (b (n + 1) : K))‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ = ‖∑ j ∈ Finset.Icc p q, a j‖ * |b q| +
        ∑ n ∈ Finset.Ico p q,
          ‖∑ j ∈ Finset.Icc p n, a j‖ * |b n - b (n + 1)| := by
      simp only [norm_mul, ← RCLike.ofReal_sub, RCLike.norm_ofReal]
    _ ≤ η * |b q| + ∑ n ∈ Finset.Ico p q, η * |b n - b (n + 1)| := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (ha q hpq le_rfl) (abs_nonneg _)
      · apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_right
          (ha n (Finset.mem_Ico.mp hn).1 (Nat.le_of_lt (Finset.mem_Ico.mp hn).2))
          (abs_nonneg _)
    _ = η * (|b q| + |b p - b q|) := by
      rw [← Finset.mul_sum, monotone_sequence_variation b p q hpq hb, mul_add]
    _ ≤ η * (M + (M + M)) := by
      apply mul_le_mul_of_nonneg_left _ hη
      exact add_le_add (hM q) ((abs_sub _ _).trans (add_le_add (hM p) (hM q)))
    _ = 3 * M * η := by ring

/-- Inclusive tails are differences of the inclusive prefixes. -/
theorem sum_Icc_succ_eq_prefix_sub {K : Type*} [AddCommGroup K]
    (a : ℕ → K) (m n : ℕ) (hmn : m ≤ n) :
    (∑ j ∈ Finset.Icc (m + 1) n, a j) =
      (∑ j ∈ Finset.range (n + 1), a j) -
        ∑ j ∈ Finset.range (m + 1), a j := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  exact Finset.sum_Ico_eq_sub a (Nat.succ_le_succ hmn)

/-- Uniformly small ordinary tails remain uniformly small after Abel weighting. -/
private theorem weighted_prefixes_cauchy {E : Type u} {K : Type*} [RCLike K]
    (a : ℕ → E → K) (b : ℕ → E → ℝ) (M : ℝ)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x,
      ‖(∑ j ∈ Finset.range (n + 1), a j x) -
        ∑ j ∈ Finset.range (m + 1), a j x‖ < ε)
    (hb : ∀ x, Monotone (fun n => b n x) ∨ Antitone (fun n => b n x))
    (hM : ∀ x n, |b n x| ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x,
      ‖(∑ j ∈ Finset.range (n + 1), a j x * (b j x : K)) -
        ∑ j ∈ Finset.range (m + 1), a j x * (b j x : K)‖ < ε := by
  intro ε hε
  let C := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  have hMC : M ≤ C := le_max_left _ _
  have hd : 0 < 3 * C + 1 := by positivity
  let η := ε / (3 * C + 1)
  have hη : 0 < η := div_pos hε hd
  obtain ⟨N, hN⟩ := hc η hη
  refine ⟨N, ?_⟩
  have ordered : ∀ m ≥ N, ∀ n ≥ N, m ≤ n → ∀ x,
      ‖(∑ j ∈ Finset.range (n + 1), a j x * (b j x : K)) -
        ∑ j ∈ Finset.range (m + 1), a j x * (b j x : K)‖ < ε := by
    intro m hm n hn hmn x
    rcases eq_or_lt_of_le hmn with rfl | hmn
    · simpa using hε
    rw [← sum_Icc_succ_eq_prefix_sub _ m n (Nat.le_of_lt hmn)]
    have ha : ∀ k, m + 1 ≤ k → k ≤ n →
        ‖∑ j ∈ Finset.Icc (m + 1) k, a j x‖ ≤ η := by
      intro k hk _
      rw [sum_Icc_succ_eq_prefix_sub _ m k (Nat.le_of_succ_le hk)]
      exact (hN m hm k (hm.trans (Nat.le_of_succ_le hk)) x).le
    calc
      _ ≤ 3 * C * η := abel_tail_norm_le (fun j => a j x) (fun j => b j x)
        (m + 1) n hmn η C hη.le ha (hb x) (fun j => (hM x j).trans hMC)
      _ < ε := by
        have heq : ε = (3 * C + 1) * η := by
          dsimp [η]
          exact (mul_div_cancel₀ ε (ne_of_gt hd)).symm
        rw [heq]
        exact mul_lt_mul_of_pos_right (by linarith) hη
  intro m hm n hn x
  rcases le_total m n with hmn | hnm
  · exact ordered m hm n hn hmn x
  · rw [norm_sub_rev]
    exact ordered n hn m hm hnm x

theorem real_uniform_abel : Specs.SingleVariableAnalysis.Ch12.UniformAbel.realUniformAbel := by
  intro E a b M hc hb hM
  apply (real_uniform_cauchy_criterion _).mpr
  have h := (real_uniform_cauchy_criterion _).mp hc
  have h' := weighted_prefixes_cauchy (K := ℝ) a b M
    (by simpa only [Real.norm_eq_abs] using h) hb hM
  simpa only [Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq] using h'

theorem complex_uniform_abel : Specs.SingleVariableAnalysis.Ch12.UniformAbel.complexUniformAbel := by
  intro E a b M hc hb hM
  apply (complex_uniform_cauchy_criterion _).mpr
  exact weighted_prefixes_cauchy (K := ℂ) a b M
    ((complex_uniform_cauchy_criterion _).mp hc) hb hM

end SingleVariableAnalysis
