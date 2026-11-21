import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Bolzano
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# The Cauchy criterion for real and complex sequences

We follow the proof of `K03.01.cauchy` (paper.tex:279–286). A Cauchy
tail is bounded by fixing its first term; a finite sum of the earlier
norms bounds the prefix. Bolzano–Weierstrass then supplies a convergent
subsequence. The common-tail estimate and one sufficiently late selected
term prove convergence of the full sequence. The generic estimates below
use only normed additive group algebra, with no completeness assumption.
In particular no complex completeness certificate is assumed or invoked.
Indexing is shifted by one, following the shared sequence definitions.
-/

namespace SingleVariableAnalysis

open scoped BigOperators

private theorem norm_tail_bounded {E : Type*} [NormedAddCommGroup E] (a : ℕ → E)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖a n - a m‖ < ε) :
    ∃ M : ℝ, ∀ n, ‖a n‖ ≤ M := by
  obtain ⟨N, hN⟩ := hc 1 zero_lt_one
  refine ⟨(∑ i ∈ Finset.range N, ‖a i‖) + (‖a N‖ + 1), ?_⟩
  intro n
  by_cases hn : n < N
  · have hp : ‖a n‖ ≤ ∑ i ∈ Finset.range N, ‖a i‖ :=
      Finset.single_le_sum (fun i _ => norm_nonneg (a i)) (Finset.mem_range.mpr hn)
    have hnonneg := norm_nonneg (a N)
    linarith
  · have ht := hN N le_rfl n (Nat.le_of_not_gt hn)
    have htri : ‖a n‖ ≤ ‖a n - a N‖ + ‖a N‖ := by
      simpa only [sub_add_cancel] using norm_add_le (a n - a N) (a N)
    have hp : 0 ≤ ∑ i ∈ Finset.range N, ‖a i‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg (a i))
    linarith

private theorem norm_cauchy_of_limit {E : Type*} [NormedAddCommGroup E]
    (a : ℕ → E) (L : E)
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖a n - L‖ < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖a n - a m‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have htri : ‖a n - a m‖ ≤ ‖a n - L‖ + ‖a m - L‖ := by
    calc
      ‖a n - a m‖ = ‖(a n - L) - (a m - L)‖ := by congr 1; abel
      _ ≤ ‖a n - L‖ + ‖a m - L‖ := norm_sub_le _ _
  have h₁ := hN m hm
  have h₂ := hN n hn
  linarith

private theorem norm_limit_of_cauchy_subsequence {E : Type*} [NormedAddCommGroup E]
    (a : ℕ → E) (L : E)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖a n - a m‖ < ε)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hL : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ‖a (φ j) - L‖ < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖a n - L‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
  obtain ⟨J, hJ⟩ := hL (ε / 2) (half_pos hε)
  let j := max N J
  have hindex : N ≤ φ j :=
    (le_max_left N J).trans (subsequenceIndex_ge φ hφ j)
  have hnear := hJ j (le_max_right N J)
  refine ⟨N, ?_⟩
  intro n hn
  have hpair := hN (φ j) hindex n hn
  have htri : ‖a n - L‖ ≤ ‖a n - a (φ j)‖ + ‖a (φ j) - L‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (a n - a (φ j)) (a (φ j) - L)
  linarith

theorem real_cauchy_criterion (a : ℕ → ℝ) :
    (∃ L : ℝ, RealSequenceConverges a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |a n - a m| < ε := by
  constructor
  · rintro ⟨L, hL⟩
    have h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖a n - L‖ < ε := by
      simpa only [RealSequenceConverges, SequenceEventually, Real.norm_eq_abs] using hL
    simpa only [Real.norm_eq_abs] using norm_cauchy_of_limit a L h
  · intro hc
    have hc' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖a n - a m‖ < ε := by
      simpa only [Real.norm_eq_abs] using hc
    have hb : ∃ M : ℝ, ∀ n, |a n| ≤ M := by
      simpa only [Real.norm_eq_abs] using norm_tail_bounded a hc'
    obtain ⟨L, φ, hφ, hL⟩ := real_bolzano_weierstrass a hb
    refine ⟨L, ?_⟩
    have hL' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ‖a (φ j) - L‖ < ε := by
      simpa only [RealSequenceConverges, SequenceEventually, Real.norm_eq_abs,
        Function.comp_apply] using hL
    simpa only [RealSequenceConverges, SequenceEventually, Real.norm_eq_abs] using
      norm_limit_of_cauchy_subsequence a L hc' φ hφ hL'

theorem complex_cauchy_criterion (a : ℕ → ℂ) :
    (∃ L : ℂ, ComplexSequenceConverges a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖a n - a m‖ < ε := by
  constructor
  · rintro ⟨L, hL⟩
    exact norm_cauchy_of_limit a L hL
  · intro hc
    obtain ⟨L, φ, hφ, hL⟩ := complex_bolzano_weierstrass a (norm_tail_bounded a hc)
    exact ⟨L, norm_limit_of_cauchy_subsequence a L hc φ hφ hL⟩

end SingleVariableAnalysis
