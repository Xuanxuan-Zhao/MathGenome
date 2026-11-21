import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Partition.RectangularPartitions
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.FiniteQBinomial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

noncomputable section
namespace FiniteCombinatorics.Partition
open Polynomial

/-- Multiplying the Gaussian recurrence by the triangular q-power gives
exactly the coefficient recurrence for the finite product. -/
theorem weighted_gaussian_recurrence (n k : ℕ) (hk : k ≤ n) :
    (X : Polynomial ℤ) ^ ((k + 1) * (k + 1 - 1) / 2) * G (n + 1) (k + 1) =
      X ^ ((k + 1) * (k + 1 - 1) / 2) * G n (k + 1) +
        X ^ n * (X ^ (k * (k - 1) / 2) * G n k) := by
  have he : (k + 1) * (k + 1 - 1) / 2 + (n - k) =
      n + k * (k - 1) / 2 := by
    rw [Nat.triangle_succ]
    omega
  have hg : G (n + 1) (k + 1) = G n (k + 1) + X ^ (n - k) * G n k :=
    gaussian_recurrence n k
  rw [hg, mul_add]
  congr 1
  rw [← mul_assoc, ← pow_add, he, pow_add, mul_assoc]

private def qBinomialTerm (n k : ℕ) : Polynomial (Polynomial ℤ) :=
  C ((X : Polynomial ℤ) ^ (k * (k - 1) / 2) * G n k) * X ^ k

private theorem qBinomialTerm_zero (n : ℕ) : qBinomialTerm n 0 = 1 := by
  simp [qBinomialTerm, gaussian_boundary.1 n]

private theorem qBinomialTerm_outside (n : ℕ) : qBinomialTerm n (n + 1) = 0 := by
  simp [qBinomialTerm, gaussian_boundary.2.2 n (n + 1) (by omega)]

private theorem qBinomialTerm_succ (n k : ℕ) (hk : k ≤ n) :
    qBinomialTerm (n + 1) (k + 1) = qBinomialTerm n (k + 1) +
      (X * C ((X : Polynomial ℤ) ^ n)) * qBinomialTerm n k := by
  unfold qBinomialTerm
  rw [weighted_gaussian_recurrence n k hk]
  simp only [map_add, map_mul, pow_succ]
  ring

private theorem qBinomialSum_succ (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), qBinomialTerm (n + 1) k) =
      (∑ k ∈ Finset.range (n + 1), qBinomialTerm n k) *
        (1 + X * C ((X : Polynomial ℤ) ^ n)) := by
  have hshift :
      (∑ k ∈ Finset.range (n + 1), qBinomialTerm n (k + 1)) + 1 =
        ∑ k ∈ Finset.range (n + 1), qBinomialTerm n k := by
    have hs := Finset.sum_range_succ' (fun k => qBinomialTerm n k) (n + 1)
    rw [Finset.sum_range_succ, qBinomialTerm_outside, add_zero,
      qBinomialTerm_zero] at hs
    exact hs.symm
  rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ',
    qBinomialTerm_zero]
  rw [Finset.sum_congr rfl (fun k hk =>
    qBinomialTerm_succ n k (by have := Finset.mem_range.mp hk; omega))]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [add_right_comm, hshift]
  ring

/-- The finite q-binomial identity, including the empty product at n = 0. -/
theorem finite_q_binomial : FiniteQBinomialSpecs.Identity := by
  intro n
  change (∏ i ∈ Finset.range n,
    (1 + X * C ((X : Polynomial ℤ) ^ i) : Polynomial (Polynomial ℤ))) =
      ∑ k ∈ Finset.range (n + 1), qBinomialTerm n k
  induction n with
  | zero => simp [qBinomialTerm_zero]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    exact (qBinomialSum_succ n).symm

end FiniteCombinatorics.Partition
