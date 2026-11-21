import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.MobiusReciprocalSquares
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.HarmonicBasel
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.MobiusInversion
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

open scoped BigOperators
open P203Specs.ClassicalFunctions
open P203Specs.Ch03.MobiusReciprocalSquares

namespace P203.Ch03.MobiusReciprocalSquares

lemma abs_mu_le (n : ℕ) : |(mu n : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

lemma square_summable : Summable squareTerm :=
  P203.Ch03.HarmonicBasel.basel_summable

lemma abs_mobius_le_square (n : ℕ) : |mobiusTerm n| ≤ squareTerm n := by
  simp only [mobiusTerm, squareTerm, abs_div, abs_of_nonneg (sq_nonneg (((n + 1 : ℕ) : ℝ)))]
  exact div_le_div_of_nonneg_right (abs_mu_le _) (sq_nonneg _)

theorem absolute_convergence :
    P203Specs.Ch03.MobiusReciprocalSquares.AbsoluteConvergence := by
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) abs_mobius_le_square square_summable

lemma mobius_summable : Summable mobiusTerm :=
  summable_abs_iff.mp absolute_convergence

lemma lseries_at_two (f : ℕ → ℝ) :
    LSeries (fun n => (f n : ℂ)) 2 =
      ((∑' n : ℕ, f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp [LSeries.term_of_ne_zero' (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_ofNat]

/-- Transfer the absolutely convergent Dirichlet convolution identity at s=2
from complex coefficients to the source's real positive-index series. -/
theorem convolution_product :
    P203Specs.Ch03.MobiusReciprocalSquares.ConvolutionProduct := by
  have hm := lseries_at_two (fun n => (mu n : ℝ))
  have h1 := lseries_at_two (fun _ => (1 : ℝ))
  simp only [Complex.ofReal_intCast] at hm
  simp only [Complex.ofReal_one] at h1
  have h := LSeries_one_mul_Lseries_moebius (s := 2) (by norm_num)
  change LSeries (fun _ => (1 : ℂ)) 2 * LSeries (fun n => (mu n : ℂ)) 2 = 1 at h
  rw [h1, hm, ← Complex.ofReal_mul, ← Complex.ofReal_one, Complex.ofReal_inj] at h
  have hm' : (∑' n : ℕ, (mu n : ℝ) / (n : ℝ) ^ 2) = ∑' n, mobiusTerm n := by
    simpa [mobiusTerm] using
      (tsum_eq_zero_add' (f := fun n : ℕ => (mu n : ℝ) / (n : ℝ) ^ 2) mobius_summable)
  have h1' : (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) = ∑' n, squareTerm n := by
    simpa [squareTerm] using
      (tsum_eq_zero_add' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) square_summable)
  rw [hm', h1', mul_comm] at h
  exact h

theorem mobius_hasSum : P203Specs.Ch03.MobiusReciprocalSquares.MobiusHasSum := by
  have h := convolution_product
  change (∑' n, mobiusTerm n) * (∑' n, squareTerm n) = 1 at h
  have hb : (∑' n, squareTerm n) = Real.pi ^ 2 / 6 :=
    P203.Ch03.HarmonicBasel.basel_hasSum.tsum_eq
  rw [hb] at h
  have hv : (∑' n, mobiusTerm n) = 6 / Real.pi ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 Real.pi_ne_zero)).2
    nlinarith [h]
  unfold P203Specs.Ch03.MobiusReciprocalSquares.MobiusHasSum
  rw [← hv]
  exact mobius_summable.hasSum

lemma square_tail_finite_bound (y : ℝ) (hy : 1 ≤ y) (N : ℕ) :
    (∑ n ∈ Finset.range N, if y < (n : ℝ) then 1 / (n : ℝ) ^ 2 else 0) ≤ 2 / y := by
  have hy0 : 0 ≤ y := by linarith
  have heq : (Finset.range N).filter (fun n : ℕ => y < (n : ℝ)) =
      Finset.Ioo ⌊y⌋₊ N := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo,
      Nat.floor_lt hy0, and_comm]
  rw [← Finset.sum_filter, heq]
  calc
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ N, 1 / (n : ℝ) ^ 2) ≤ 2 / ((⌊y⌋₊ : ℝ) + 1) := by
      simpa only [one_div] using (sum_Ioo_inv_sq_le (α := ℝ) ⌊y⌋₊ N)
    _ ≤ 2 / y := by
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (Nat.lt_floor_add_one y).le

theorem reciprocal_square_tail_bound :
    P203Specs.Ch03.MobiusReciprocalSquares.ReciprocalSquareTailBound := by
  intro y hy
  have hnonneg : ∀ n : ℕ, 0 ≤ (if y < (n : ℝ) then 1 / (n : ℝ) ^ 2 else 0) := by
    intro n
    split_ifs <;> positivity
  exact ⟨summable_of_sum_range_le hnonneg (square_tail_finite_bound y hy),
    Real.tsum_le_of_sum_range_le hnonneg (square_tail_finite_bound y hy)⟩

lemma absolute_tail_le_square (y : ℝ) (n : ℕ) :
    (if y < (n : ℝ) then |(mu n : ℝ)| / (n : ℝ) ^ 2 else 0) ≤
      (if y < (n : ℝ) then 1 / (n : ℝ) ^ 2 else 0) := by
  split_ifs
  · exact div_le_div_of_nonneg_right (abs_mu_le n) (sq_nonneg _)
  · rfl

theorem absolute_mobius_tail_bound :
    P203Specs.Ch03.MobiusReciprocalSquares.AbsoluteMobiusTailBound := by
  intro y hy
  have hb := reciprocal_square_tail_bound y hy
  have hnonneg : ∀ n : ℕ,
      0 ≤ (if y < (n : ℝ) then |(mu n : ℝ)| / (n : ℝ) ^ 2 else 0) := by
    intro n
    split_ifs <;> positivity
  have ha := Summable.of_nonneg_of_le hnonneg (absolute_tail_le_square y) hb.1
  exact ⟨ha, (ha.tsum_le_tsum (absolute_tail_le_square y) hb.1).trans hb.2⟩

theorem mobius_tail_bound :
    P203Specs.Ch03.MobiusReciprocalSquares.MobiusTailBound := by
  intro y hy
  have ha := absolute_mobius_tail_bound y hy
  have heq (n : ℕ) :
      |(if y < (n : ℝ) then (mu n : ℝ) / (n : ℝ) ^ 2 else 0)| =
      (if y < (n : ℝ) then |(mu n : ℝ)| / (n : ℝ) ^ 2 else 0) := by
    split_ifs <;> simp [abs_div]
  have habs : Summable (fun n : ℕ =>
      |(if y < (n : ℝ) then (mu n : ℝ) / (n : ℝ) ^ 2 else 0)|) := by
    simpa only [heq] using ha.1
  refine ⟨summable_abs_iff.mp habs, ?_⟩
  have hnorm := norm_tsum_le_tsum_norm
    (f := fun n : ℕ => if y < (n : ℝ) then (mu n : ℝ) / (n : ℝ) ^ 2 else 0)
    (by simpa only [Real.norm_eq_abs] using habs)
  simp only [Real.norm_eq_abs, heq] at hnorm
  exact hnorm.trans ha.2

end P203.Ch03.MobiusReciprocalSquares
